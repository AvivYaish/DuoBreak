#!/usr/bin/env python3
# SPDX-License-Identifier: AGPL-3.0-or-later
# Forked from v2.0.0 of github.com/JesseNaser/DuoBreak

import argparse
import base64
import getpass
import hashlib
import hmac
import importlib
import json
import os
import re
import stat
import sys
import tempfile
import time
from collections import deque
from contextlib import closing, suppress
from copy import deepcopy
from datetime import datetime, timezone
from email.utils import format_datetime
from functools import partial
from pathlib import Path
from queue import Empty, Queue
from threading import Event, Lock, Thread
from time import monotonic
from urllib.parse import urlencode

import portalocker
import pyotp
import requests
from Crypto.Cipher import AES
from Crypto.Hash import SHA512
from Crypto.Protocol.KDF import scrypt
from Crypto.PublicKey import RSA
from Crypto.Random import get_random_bytes
from Crypto.Signature import pkcs1_15
from PIL import Image
from prompt_toolkit import PromptSession
from prompt_toolkit.history import DummyHistory
from prompt_toolkit.input import create_input
from prompt_toolkit.input.typeahead import get_typeahead
from prompt_toolkit.keys import Keys
from prompt_toolkit.output.defaults import create_output
from prompt_toolkit.shortcuts import choice
from prompt_toolkit.utils import is_dumb_terminal

DB_V2 = b"DBv2"  # Authenticated AES-SIV with scrypt.
SALT_SIZE = NONCE_SIZE = TAG_SIZE = 16
SCRYPT_N, SCRYPT_R, SCRYPT_P = 2**17, 8, 1
REQUEST_TIMEOUT = (5, 30)
POLL_SECONDS = 5
PUSH_ERRORS = (requests.RequestException, ValueError, KeyError, TypeError)
ACTIVATION_URL = re.compile(
    r"(?i:https://m-([0-9a-f]+)\.duosecurity\.com)/activate/([A-Za-z0-9_-]+)",
    re.ASCII,
)


class EnterInput:
    """Plain-output events without a reader thread or terminal-mode changes."""

    def __init__(self):
        self.input = None
        self.pending = deque()
        self.previous = None
        self.codes = {}
        self.step = int(time.time()) // 30
        with suppress(OSError, ValueError, AttributeError):
            if sys.stdin.isatty():
                self.input = create_input()

    def __call__(self):
        if self.input is None:
            return False
        self.pending.extend(self.input.read_keys())
        if self.input.closed:
            raise EOFError
        while self.pending:
            key = self.pending.popleft().key
            previous, self.previous = self.previous, key
            if key == Keys.ControlC:
                raise KeyboardInterrupt
            if key in (Keys.ControlD, Keys.ControlZ):
                raise EOFError
            if key == Keys.Enter or (key == Keys.ControlJ and previous != Keys.Enter):
                return True
        return False

    def close(self):
        if self.input is not None:
            self.input.close()

    def get(self, listener):
        refresh = self()
        step = int(time.time()) // 30
        if not refresh and step != self.step:
            for row in self.codes.values():
                if callable(row):
                    print(row())
        self.step = step
        return None if refresh else listener.get(timeout=0.25)


class LiveDisplay:
    """One redrawable dashboard and input reader for the listening session."""

    def __init__(self, title):
        self.title = title
        self.codes = {}
        self.status = ""
        self.poll_errors = {}
        self.count = 0
        self.session = PromptSession(
            output=create_output(),
            input=create_input(),
            history=DummyHistory(),
            erase_when_done=True,
            refresh_interval=0.25,
        )

    def render(self, prompt=""):
        rows = [
            f"Vault: {self.title}",
            *(row() if callable(row) else row for row in self.codes.values()),
            "",
            f"Listening for mobile pushes on {self.count} key(s).",
        ]
        if not prompt:
            rows.append("- Enter: regenerate all passcodes")
        rows.append("- Ctrl+C: stop listening")
        if self.status:
            rows.extend(("", self.status))
        if self.poll_errors:
            rows.extend(("", *self.poll_errors.values()))
        return "\n".join(rows) + "\n" + prompt

    def get(self, listener):
        def poll(app):
            if app.is_done:
                return
            try:
                app.exit(result=listener.get(timeout=0))
            except Empty:
                pass
            except Exception as error:
                app.exit(exception=error)

        self.session.app.before_render += poll
        try:
            result = self.session.prompt(self.render)
            return result if isinstance(result, tuple) else None
        finally:
            self.session.app.before_render -= poll

    def _discard_input(self):
        # Input intended for a previous screen cannot approve a new push.
        source = self.session.app.input
        keys = get_typeahead(source) + source.read_keys() + source.flush_keys()
        for key in keys:
            if key.key == Keys.ControlC:
                raise KeyboardInterrupt
            if key.key in (Keys.ControlD, Keys.ControlZ):
                raise EOFError
        if source.closed:
            raise EOFError

    def ask(self, prompt):
        return self.session.prompt(
            lambda: self.render(prompt), pre_run=self._discard_input
        )

    def close(self):
        self.codes.clear()
        self.status = ""
        self.poll_errors.clear()
        self.session.default_buffer.reset()
        get_typeahead(self.session.app.input)
        self.session.app.input.close()


class PasswordStoreError(RuntimeError):
    """OS-protected password storage is unavailable or an operation failed."""


def _local_data_dir(platform):
    home = Path.home()
    if platform == "win32":
        base = Path(os.environ.get("LOCALAPPDATA") or home / "AppData" / "Local")
    elif platform == "darwin":
        base = home / "Library" / "Application Support"
    elif platform.startswith("linux"):
        configured = os.environ.get("XDG_STATE_HOME", "")
        base = (
            Path(configured)
            if configured and Path(configured).is_absolute()
            else home / ".local" / "state"
        )
    else:
        raise PasswordStoreError(
            "Secure password storage is unsupported on this operating system."
        )
    if not base.is_absolute():
        raise PasswordStoreError(
            "The local password-storage directory must be an absolute path."
        )
    return base / "DuoBreak" / "passwords"


class PasswordStore:
    """Lazily access a native store identified by the canonical vault path."""

    def __init__(self, vault_path, *, data_dir=None, platform=None):
        self._platform = platform or sys.platform
        self._data_dir = Path(data_dir) if data_dir is not None else None
        canonical_path = os.path.normcase(str(Path(vault_path).expanduser().resolve()))
        self._identity = hashlib.sha256(os.fsencode(canonical_path)).hexdigest()

    @property
    def location(self):
        """DPAPI blob on Windows, nonsecret keyring signal on macOS/Linux."""
        directory = self._data_dir or _local_data_dir(self._platform)
        return directory / (self._identity + ".bin")

    def _open(self):
        try:
            persistence = importlib.import_module("msal_extensions.persistence")
        except ImportError:
            raise PasswordStoreError(
                "Secure password storage requires msal-extensions, install the project requirements."
            ) from None
        try:
            location = self.location
            location.parent.mkdir(mode=0o700, parents=True, exist_ok=True)
            if self._platform == "win32":
                backend = persistence.FilePersistenceWithDataProtection(str(location))
            elif self._platform == "darwin":
                backend = persistence.KeychainPersistence(
                    str(location),
                    service_name="DuoBreak vault passwords",
                    account_name=self._identity,
                )
            elif self._platform.startswith("linux"):
                backend = persistence.LibsecretPersistence(
                    str(location),
                    schema_name="org.duobreak.vault-password",
                    attributes={"vault": self._identity},
                    label="DuoBreak vault password",
                )
            else:
                raise PasswordStoreError(
                    "Secure password storage is unsupported on this operating system."
                )
            if backend.is_encrypted is not True:
                raise PasswordStoreError(
                    "Refusing an unencrypted password-storage backend."
                )
            return backend, persistence.PersistenceNotFound
        except PasswordStoreError:
            raise
        except Exception:
            raise PasswordStoreError(
                "OS secure password storage is unavailable. Unlock manually or check your OS keyring."
            ) from None

    def load(self):
        """Missing signal or secret means no auto-unlock, backend errors raise."""
        try:
            mode = self.location.stat().st_mode
            if not stat.S_ISREG(mode):
                raise OSError("Invalid local storage state")
        except FileNotFoundError:
            return None
        except OSError:
            raise PasswordStoreError(
                "Could not access local password-storage state."
            ) from None
        backend, not_found = self._open()
        try:
            password = backend.load()
            if not isinstance(password, str):
                raise TypeError("Invalid secret type")
            return password or None
        except not_found:
            return None
        except Exception:
            raise PasswordStoreError(
                "Could not read the saved vault password. Unlock manually."
            ) from None

    def save(self, password):
        if not isinstance(password, str) or not password:
            raise PasswordStoreError(
                "A saved vault password must be a nonempty string."
            )
        self._write(password, "save")

    def _write(self, password, action):
        backend, _ = self._open()
        try:
            backend.save(password)
            # Libsecret can fail silently, verify both saves and empty tombstones.
            if backend.load() != password:
                raise ValueError("Password-storage verification failed")
        except Exception:
            raise PasswordStoreError(
                f"Could not {action} and verify the vault password in OS secure storage."
            ) from None

    def forget(self):
        """Remove the DPAPI blob, replace native-keyring secrets with empty text."""
        if self._platform == "win32":
            try:
                self.location.unlink(missing_ok=True)
            except OSError:
                raise PasswordStoreError(
                    "Could not remove the saved vault password."
                ) from None
            return
        # MSAL has no public keyring deletion API. Clear even without a signal:
        # a previous save may have stored the secret but failed to create it.
        self._write("", "clear")


def totp_line(secret):
    now = time.time()
    code = pyotp.TOTP(secret).at(datetime.fromtimestamp(now, timezone.utc))
    expires = datetime.fromtimestamp(
        (int(now) // 30 + 1) * 30, timezone.utc
    ).astimezone()
    return f"Duo Mobile Passcode: {code} (TOTP, expires {expires:%H:%M:%S})"


class PushResponseError(ValueError):
    """A mobile-push response failure with a safe, locally generated message."""


def push_transactions(result):
    if not isinstance(result, dict):
        raise PushResponseError("invalid mobile push response")
    if result.get("stat", "OK") != "OK":
        raise PushResponseError("Duo rejected the mobile push poll")
    response = result.get("response")
    if not isinstance(response, dict):
        raise PushResponseError("missing mobile push transaction list")
    transactions = response.get("transactions")
    if transactions is None and result.get("stat") == "OK":
        return []
    if not isinstance(transactions, list):
        raise PushResponseError("invalid mobile push transaction list")
    return transactions


class PushListener:
    """Poll each key independently and coalesce unread results by key name.

    ``poll(key)`` performs one GET and returns its response dictionary. Workers
    never print, prompt, approve, or modify a vault. A failed poll produces safe
    error text without discarding the last successful transaction snapshot.
    Returned response dictionaries should be treated as read-only by the caller.
    """

    def __init__(self, keys, poll, interval=5):
        if interval < 0:
            raise ValueError("Polling interval cannot be negative")
        self._keys = deepcopy(keys)
        self._poll = poll
        self._interval = interval
        self._stop = Event()
        self._lock = Lock()
        self._notifications = Queue(maxsize=max(1, len(keys)))
        self._updates = {}
        self._last_success = {}
        self._threads = []
        self._started = False

    def __enter__(self):
        if self._started or self._stop.is_set():
            raise RuntimeError("A push listener cannot be restarted")
        self._started = True
        try:
            for name, key in self._keys.items():
                worker = Thread(target=self._run, args=(name, key), daemon=True)
                worker.start()
                self._threads.append(worker)
        except BaseException:
            self.close()
            raise
        return self

    def _run(self, name, key):
        while not self._stop.is_set():
            try:
                result = self._poll(key)
                transactions = push_transactions(result)
            except Exception as error:  # noqa: BLE001 - isolate worker failures
                result = DuoAuthenticator.request_error(error)
            with self._lock:
                if self._stop.is_set():
                    return
                if isinstance(result, dict):
                    self._last_success[name] = transactions
                already_queued = name in self._updates
                self._updates[name] = result
                if not already_queued:
                    self._notifications.put_nowait(name)
            if self._stop.wait(self._interval):
                return

    def get(self, timeout=0.25):
        """Return (key name, latest result), raising queue.Empty on timeout."""
        name = self._notifications.get(timeout=timeout)
        with self._lock:
            return name, self._updates.pop(name)

    def is_pending(self, name, urgid):
        """Check the latest validated snapshot, excluding malformed entries."""
        with self._lock:
            transactions = self._last_success.get(name, [])
        return any(
            isinstance(transaction, dict)
            and isinstance(transaction.get("urgid"), str)
            and transaction["urgid"] == urgid
            for transaction in transactions
        )

    def close(self):
        """Stop publishing immediately, wait at most one second for all workers.

        An outstanding GET can outlast the join deadline. Daemon workers retain
        only their private key-data copies, and discard results after shutdown.
        """
        with self._lock:
            self._stop.set()
        deadline = monotonic() + 1
        for worker in self._threads:
            remaining = deadline - monotonic()
            if remaining <= 0:
                break
            worker.join(remaining)

    def __exit__(self, exc_type, exc_value, traceback):
        self.close()


class DuoAuthenticator:
    def __init__(self, config_file=None, password_store=None):
        self.config_file = Path(config_file) if config_file else None
        self.config = {}
        self.salt = self.encryption_key = self.vault_digest = None
        self.lock_file = None
        self.password_store = password_store
        self.display = None
        self.passcodes = {}

    def say(self, message):
        if self.display is None:
            print(message)
        else:
            self.display.status = message.strip()

    def show_passcode(self, name, row):
        formatted = (
            (lambda: f"- [{name}] {row()}") if callable(row) else f"- [{name}] {row}"
        )
        self.passcodes[name] = formatted
        if self.display is None:
            print(formatted() if callable(formatted) else formatted)

    def ask(self, prompt):
        try:
            read = self.display.ask if self.display is not None else input
            return read(prompt).strip()
        except (EOFError, KeyboardInterrupt):
            if self.display is None:
                print()
            return None

    @staticmethod
    def menu(title, *options, back="Back", default=None):
        """Return 1..N for an option, or None for Back/cancellation."""
        if default is not None and not 1 <= default <= len(options):
            raise ValueError("The default must identify a menu option")
        try:
            return (
                choice(
                    title,
                    options=[*enumerate(options, 1), (0, back)],
                    default=default or 0,
                )
                or None
            )
        except (EOFError, KeyboardInterrupt):
            return None

    def action_menu(self, title, actions, **options):
        while choice := self.menu(title, *actions, **options):
            tuple(actions.values())[choice - 1]()

    @staticmethod
    def password(prompt, confirm=False):
        try:
            while True:
                password = getpass.getpass(prompt)
                if not password or not confirm:
                    return password or None
                if len(password) < 12:
                    print("Use at least 12 characters for the vault password.")
                    continue
                if password == getpass.getpass("Confirm password: "):
                    return password
                print("Passwords do not match.")
        except (EOFError, KeyboardInterrupt):
            print()
            return None

    def select_vault(self):
        vaults = sorted(
            (path for path in Path.cwd().glob("*.duo") if path.is_file()),
            key=lambda path: path.name.lower(),
        )
        if vaults:
            choice = 1
            if len(vaults) > 1:
                choice = self.menu("Vaults", *(path.name for path in vaults), back="Exit")
            if not choice:
                return False
            self.config_file = vaults[choice - 1]
            return True

        print("No Duo vault found. Create one to continue.")
        while True:
            name = self.ask("Vault name (leave empty to exit): ")
            if not name:
                return False
            if Path(name).name != name:
                print("Enter a filename, not a path.")
                continue
            self.config_file = Path(
                name if name.lower().endswith(".duo") else name + ".duo"
            )
            return True

    @staticmethod
    def derive_key(password, salt):
        try:
            return bytearray(
                scrypt(
                    password.encode("utf-8"),
                    salt,
                    64,
                    N=SCRYPT_N,
                    r=SCRYPT_R,
                    p=SCRYPT_P,
                )
            )
        except (MemoryError, ValueError, UnicodeError) as error:
            raise RuntimeError("Vault key derivation failed") from error

    @staticmethod
    def wipe(value):
        if isinstance(value, bytearray):
            value[:] = b"\0" * len(value)

    @staticmethod
    def valid_vault_header(blob):
        return (
            isinstance(blob, bytes)
            and blob.startswith(DB_V2)
            and len(blob) > 4 + SALT_SIZE + NONCE_SIZE + TAG_SIZE
        )

    def decrypt_vault(self, blob, password):
        if not self.valid_vault_header(blob):
            raise ValueError("Invalid or unsupported vault. Expected DBv2 format.")
        key = plaintext = None
        try:
            salt, nonce = blob[4:20], blob[20:36]
            key = self.derive_key(password, salt)
            cipher = AES.new(key, AES.MODE_SIV, nonce=nonce)
            cipher.update(blob[:36])
            plaintext = bytearray(cipher.decrypt_and_verify(blob[52:], blob[36:52]))
            config = json.loads(plaintext.decode("utf-8"))
            if not isinstance(config, dict) or (
                "keys" in config and not isinstance(config["keys"], dict)
            ):
                raise ValueError("Invalid vault data")
            config.setdefault("keys", {})
            return config, key, salt
        except BaseException:
            self.wipe(key)
            raise
        finally:
            self.wipe(plaintext)

    def lock_vault(self):
        if self.lock_file:
            return True
        if not self.config_file:
            return False
        lock = portalocker.Lock(
            str(Path(self.config_file).absolute()) + ".lock",
            mode="a+b",
            timeout=0,
            opener=lambda path, flags: os.open(path, flags, 0o600),
        )
        try:
            lock.acquire()
        except (OSError, portalocker.exceptions.LockException):
            return False
        self.lock_file = lock
        return True

    def load_config(self):
        if not self.lock_vault():
            print("This vault is already open or could not be locked.")
            return False
        loaded = False
        try:
            path = Path(self.config_file)
            if not path.exists():
                password = self.password(
                    "Create a vault password (leave empty to cancel): ", confirm=True
                )
                if password is None:
                    return False
                self.config = {"keys": {}}
                self.reencrypt_vault(password)
                loaded = True
                return True

            blob = path.read_bytes()
            if not self.valid_vault_header(blob):
                print("Invalid or unsupported vault. Expected DBv2 format.")
                return False
            self.vault_digest = hashlib.sha256(blob).digest()

            try:
                saved_password = self.get_password_store().load()
            except PasswordStoreError:
                saved_password = None
                print("Saved password unavailable. Enter the vault password manually.")
            had_saved_password = saved_password is not None
            for _ in range(3 + int(had_saved_password)):
                using_saved_password = saved_password is not None
                password, saved_password = saved_password, None
                if not using_saved_password:
                    password = self.password("Vault password (leave empty to cancel): ")
                if password is None:
                    return False
                try:
                    self.config, self.encryption_key, self.salt = self.decrypt_vault(
                        blob, password
                    )
                except (ValueError, TypeError):
                    password = None
                    if using_saved_password:
                        print(
                            "Saved password did not unlock this vault. Enter it manually."
                        )
                    else:
                        print("Wrong password or damaged vault.")
                    continue

                loaded = True
                if had_saved_password and not using_saved_password:
                    self.save_password(password)
                return True

            print("Too many failed password attempts.")
            return False
        except RuntimeError:
            print("Not enough resources to secure or unlock the vault.")
            return False
        except (OSError, ValueError):
            print("Could not read or save the encrypted vault.")
            return False
        finally:
            password = None
            if not loaded:
                self.close()

    def reencrypt_vault(self, password):
        """Commit a fresh encryption key before replacing the unlocked key."""
        salt = get_random_bytes(SALT_SIZE)
        key = self.derive_key(password, salt)
        try:
            self.save_config(key=key, salt=salt)
        except BaseException:
            self.wipe(key)
            raise
        self.wipe(self.encryption_key)
        self.salt, self.encryption_key = salt, key

    def save_config(self, key=None, salt=None):
        if not self.lock_vault():
            raise OSError("Vault is already open in another process")
        key = key if key is not None else self.encryption_key
        salt = salt if salt is not None else self.salt
        if key is None or salt is None or len(key) != 64 or len(salt) != SALT_SIZE:
            raise ValueError("Vault is not unlocked")

        plaintext = bytearray(
            json.dumps(self.config, separators=(",", ":")).encode("utf-8")
        )
        temp_path = None
        try:
            nonce = get_random_bytes(NONCE_SIZE)
            header = DB_V2 + salt + nonce
            cipher = AES.new(key, AES.MODE_SIV, nonce=nonce)
            cipher.update(header)
            ciphertext, tag = cipher.encrypt_and_digest(plaintext)
            encrypted = header + tag + ciphertext

            path = Path(self.config_file)
            try:
                current_digest = hashlib.sha256(path.read_bytes()).digest()
            except FileNotFoundError:
                current_digest = None
            if current_digest != self.vault_digest:
                raise OSError("Vault was changed by another process")
            descriptor, temp_path = tempfile.mkstemp(
                dir=path.parent,
                prefix=f".{path.name}.",
                suffix=".tmp",
            )
            with os.fdopen(descriptor, "wb") as temporary:
                temporary.write(encrypted)
                temporary.flush()
                os.fsync(temporary.fileno())
            os.replace(temp_path, path)
            temp_path = None
            self.vault_digest = hashlib.sha256(encrypted).digest()
            if os.name == "posix":
                with suppress(OSError):
                    directory = os.open(path.parent, os.O_RDONLY)
                    try:
                        os.fsync(directory)
                    finally:
                        os.close(directory)
        finally:
            self.wipe(plaintext)
            if temp_path:
                with suppress(FileNotFoundError):
                    os.unlink(temp_path)

    def get_password_store(self):
        if self.password_store is None:
            self.password_store = PasswordStore(self.config_file)
        return self.password_store

    def verified_password(self):
        """Require a typed password for credential-management actions."""
        password = self.password("Current vault password (leave empty to cancel): ")
        if password is None:
            return None
        key = None
        try:
            key = self.derive_key(password, self.salt)
            if not hmac.compare_digest(key, self.encryption_key):
                print("Incorrect vault password.")
                return None
            return password
        except (RuntimeError, TypeError):
            print("Could not verify the vault password.")
            return None
        finally:
            self.wipe(key)

    def save_password(self, password):
        try:
            self.get_password_store().save(password)
            return True
        except PasswordStoreError:
            print("Could not securely save the password. Use manual unlock.")
            # Avoid leaving a stale or partially saved password after an update.
            try:
                self.get_password_store().forget()
            except PasswordStoreError:
                print(
                    "Could not clear the saved password. Retry Forget saved password."
                )
            return False

    def remember_password(self):
        print("This OS account will be able to unlock the vault automatically.")
        password = self.verified_password()
        if password is not None and self.save_password(password):
            print("Vault password saved securely on this device.")
        password = None

    def forget_password(self):
        try:
            self.get_password_store().forget()
        except PasswordStoreError:
            print(
                "Could not forget the saved password. Try again when storage is available."
            )
            return
        print("Saved password forgotten. Next launch requires manual unlock.")

    def vault_settings(self):
        self.action_menu(
            "Vault settings",
            {
                "Remember vault password on this device": self.remember_password,
                "Forget saved password": self.forget_password,
                "Change vault password": self.change_password,
            },
        )

    def change_password(self):
        if self.verified_password() is None:
            return
        password = self.password(
            "New vault password (leave empty to cancel): ", confirm=True
        )
        if password is None:
            return
        try:
            self.reencrypt_vault(password)
        except RuntimeError:
            print("Not enough resources to change the vault password.")
            return
        except (OSError, ValueError):
            print("Could not change the vault password.")
            return
        try:
            if self.get_password_store().load() is not None:
                self.save_password(password)
        except PasswordStoreError:
            print("Saved password could not be read, clearing it for manual unlock.")
            self.forget_password()
        password = None
        print("Vault password changed.")

    @staticmethod
    def parse_activation_url(activation_url):
        match = (
            ACTIVATION_URL.fullmatch(activation_url)
            if isinstance(activation_url, str)
            else None
        )
        if not match:
            raise ValueError("invalid Duo activation URL")
        return match[2], f"api-{match[1].lower()}.duosecurity.com"

    def parse_qr_code(self, file_path):
        try:
            from pyzbar.pyzbar import decode

            with Image.open(file_path) as image:
                decoded = decode(image)
            if len(decoded) != 1:
                raise ValueError("the image must contain exactly one QR code")
            url = decoded[0].data.decode("utf-8").strip()
            self.parse_activation_url(url)
            return url
        except (
            ImportError,
            OSError,
            ValueError,
            UnicodeDecodeError,
            Image.DecompressionBombError,
        ) as error:
            print(f"Could not read the QR code: {error}")
            return None

    def activate(self, code, host):
        key_pair = RSA.generate(2048)
        public_key = key_pair.publickey().export_key("PEM").decode("ascii")
        private_key = key_pair.export_key("PEM").decode("ascii")
        headers = {
            "User-Agent": "DuoMobileApp/4.117.1 (arm64; iOS 26.6); Client: Foundation",
            "Accept": "*/*",
            "Accept-Language": "en-us",
        }
        data = {
            "app_id": "com.duosecurity.DuoMobile",
            "app_version": "4.117.1",
            "ble_status": "allowed",
            "build_version": "23G71",
            "customer_protocol": "1",
            "device_name": "iPhone",
            "jailbroken": "false",
            "language": "en",
            "manufacturer": "Apple",
            "model": "arm64",
            "notification_status": "not_determined",
            "passcode_status": "true",
            "pkpush": "rsa-sha512",
            "platform": "iOS",
            "pubkey": public_key,
            "region": "US",
            "security_patch_level": "",
            "touchid_status": "true",
            "version": "26.6",
        }
        try:
            response = requests.post(
                f"https://{host}/push/v2/activation/{code}",
                headers=headers,
                data=data,
                timeout=REQUEST_TIMEOUT,
                allow_redirects=False,
            )
            if response.status_code in range(300, 400):
                raise ValueError("Duo activation redirected unexpectedly")
            response.raise_for_status()
            payload = response.json()
            activation = payload.get("response") if isinstance(payload, dict) else None
            if not isinstance(activation, dict):
                raise ValueError("Activation was rejected")
            return activation, public_key, private_key
        except (requests.RequestException, ValueError, TypeError):
            print("Duo activation failed. Check the code, host, and connection.")
            return None

    def add_key(self):
        print("\nWhen setting up a new Duo device, select Apple iOS tablet.")
        method = self.menu(
            "Add key",
            "Activation URL",
            "Activation code and host",
            "QR code image",
            default=1,
        )
        if not method:
            return

        while True:
            name = self.ask("Nickname (leave empty to cancel): ")
            if not name:
                return
            if name not in self.config["keys"]:
                break
            print("That nickname already exists.")

        while True:
            if method == 1:
                url = self.ask("Activation URL (leave empty to cancel): ")
                if not url:
                    return
            elif method == 2:
                code = self.ask("Activation code (leave empty to cancel): ")
                if not code:
                    return
                host = self.ask("API host (leave empty to cancel): ")
                if not host:
                    return
                host = host.lower().removeprefix("https://").rstrip("/")
                host_match = re.fullmatch(r"api-([0-9a-f]+)\.duosecurity\.com", host)
                if not host_match:
                    print("Invalid Duo activation code or API host. Try again.")
                    continue
                url = f"https://m-{host_match.group(1)}.duosecurity.com/activate/{code}"
            else:
                file_path = self.ask("QR image path (leave empty to cancel): ")
                if not file_path:
                    return
                url = self.parse_qr_code(file_path.strip('"'))
                if not url:
                    continue
            try:
                code, host = self.parse_activation_url(url)
            except ValueError as error:
                print(f"Invalid Duo activation URL: {error}")
                continue
            break

        activated = self.activate(code, host)
        while not activated:
            retry = self.ask("Retry this activation? [Y/n]: ")
            if retry is None or retry.lower() == "n":
                return
            activated = self.activate(code, host)

        response, public_key, private_key = activated
        self.config["keys"][name] = {
            "code": code,
            "host": host,
            "response": response,
            "pubkey": public_key,
            "privkey": private_key,
        }
        while True:
            try:
                self.save_config()
                print(f"Key '{name}' added.")
                return
            except (OSError, ValueError):
                print(
                    "Save failed. This activation may be one-use, leaving now permanently discards it."
                )
                retry = self.ask("Retry saving? [Y/n]: ")
                if retry is None or retry.lower() == "n":
                    self.config["keys"].pop(name, None)
                    print("The activated key was not saved.")
                    return

    def duo_request(self, key_config, method, path, data):
        # Duo verifies a canonical, alphabetically sorted parameter string.
        data = dict(sorted(data.items()))
        private_key = RSA.import_key(key_config["privkey"].encode("ascii"))
        duo_date = format_datetime(datetime.now(timezone.utc))
        message = "\n".join(
            (
                duo_date,
                method,
                key_config["host"].lower(),
                path,
                urlencode(data),
            )
        ).encode("ascii")
        signature = pkcs1_15.new(private_key).sign(SHA512.new(message))
        authorization = "Basic " + base64.b64encode(
            (
                key_config["response"]["pkey"]
                + ":"
                + base64.b64encode(signature).decode("ascii")
            ).encode("ascii")
        ).decode("ascii")
        headers = {
            "Authorization": authorization,
            "x-duo-date": duo_date,
            "host": key_config["host"],
        }
        if method == "POST":
            headers["txId"] = path.rsplit("/", 1)[-1]
        response = requests.request(
            method,
            f"https://{key_config['host']}{path}",
            headers=headers,
            params=data if method == "GET" else None,
            data=data if method == "POST" else None,
            timeout=REQUEST_TIMEOUT,
            allow_redirects=False,
        )
        if response.status_code in range(300, 400):
            raise ValueError("Duo request redirected unexpectedly")
        if method == "POST" and response.status_code == 400:
            with suppress(ValueError):
                rejection = response.json()
                if (
                    isinstance(rejection, dict)
                    and rejection.get("stat") == "FAIL"
                    and str(rejection.get("code")) == "40032"
                ):
                    return {"stat": "FAIL", "code": 40032}
        response.raise_for_status()
        result = response.json()
        if not isinstance(result, dict):
            raise ValueError("Invalid Duo response")
        return result

    @staticmethod
    def request_error(error):
        """Describe failures without printing request URLs, headers, or bodies."""
        if isinstance(error, PushResponseError):
            return str(error)
        if isinstance(error, requests.HTTPError) and error.response is not None:
            response = error.response
            detail = f"HTTP {response.status_code}"
            with suppress(ValueError):
                payload = response.json()
                code = str(payload.get("code", "")) if isinstance(payload, dict) else ""
                if re.fullmatch(r"[0-9]{5}", code):
                    detail += f" (Duo {code})"
            return detail
        for kind, detail in (
            (requests.Timeout, "request timed out"),
            (requests.exceptions.SSLError, "TLS connection failed"),
            (requests.ConnectionError, "connection failed"),
            (requests.exceptions.JSONDecodeError, "invalid JSON response"),
            ((ValueError, KeyError, TypeError), "invalid request or response data"),
        ):
            if isinstance(error, kind):
                return detail
        return "request failed"

    def prompt_step_up_code(self, step_up_code_info, key_name=None):
        digits = (
            step_up_code_info.get("num_digits")
            if isinstance(step_up_code_info, dict)
            else None
        )
        if (
            isinstance(digits, bool)
            or not isinstance(digits, int)
            or not 3 <= digits <= 7
        ):
            raise ValueError("invalid Verified Duo Push metadata")
        label = f"[{key_name}] " if key_name is not None else ""
        while True:
            code = self.ask(
                f"{label}Enter the {digits}-digit verification code (blank to stop): "
            )
            if not code:
                return None
            if len(code) == digits and code.isascii() and code.isdecimal():
                return code
            self.say(f"Enter exactly {digits} ASCII digits.")

    def validated_push_key(self, key_name):
        """Copy only the credentials needed by polling workers, never vault state."""
        key = self.config["keys"][key_name]
        response = key.get("response") if isinstance(key, dict) else None
        valid_host = (
            isinstance(key, dict)
            and isinstance(key.get("host"), str)
            and re.fullmatch(r"api-[0-9a-f]+\.duosecurity\.com", key["host"].lower())
        )
        if (
            not valid_host
            or not isinstance(key.get("privkey"), str)
            or not isinstance(response, dict)
            or not all(
                isinstance(response.get(field), str)
                and re.fullmatch(r"[A-Za-z0-9._~-]{1,512}", response[field])
                for field in ("akey", "pkey")
            )
        ):
            print(f"[{key_name}] This key has invalid Duo Mobile Push data.")
            return
        try:
            RSA.import_key(key["privkey"].encode("ascii"))
        except (ValueError, TypeError, IndexError, UnicodeError):
            print(f"[{key_name}] This key has an invalid Duo Mobile Push signing key.")
            return
        return {
            "host": key["host"],
            "privkey": key["privkey"],
            "response": {"akey": response["akey"], "pkey": response["pkey"]},
        }

    @staticmethod
    def push_parameters(key):
        return {
            "akey": key["response"]["akey"],
            "fips_status": "1",
            "hsm_status": "true",
            "pkpush": "rsa-sha512",
        }

    def poll_pushes(self, key):
        return self.duo_request(
            key, "GET", "/push/v2/device/transactions", self.push_parameters(key)
        )

    @staticmethod
    def push_expired(transaction):
        expiration = transaction.get("expiration")
        return (
            isinstance(expiration, (int, float))
            and not isinstance(expiration, bool)
            and time.time() >= expiration
        )

    def prompt_push_action(self, key_name):
        while True:
            action = self.ask(f"[{key_name}] [Enter/y] Approve, [s] skip, [q] stop: ")
            action = action.lower() if action else action
            if action in (None, "q"):
                return None
            if action in ("y", "", "s", "n"):
                return action in ("", "y")
            self.say("Press Enter to approve, or enter y, s, or q.")

    def process_pushes(self, key_name, key, result, handled, is_pending=None):
        """Handle a poll on the main thread, False means stop listening."""
        valid = {}
        for transaction in push_transactions(result):
            if (
                not isinstance(transaction, dict)
                or not isinstance(transaction.get("urgid"), str)
                or not re.fullmatch(r"[A-Za-z0-9_-]{1,128}", transaction["urgid"])
            ):
                self.say(f"[{key_name}] Skipped a malformed Duo transaction.")
                continue
            valid[transaction["urgid"]] = transaction
        handled.intersection_update(valid)
        for transaction_id, transaction in valid.items():
            if transaction_id in handled:
                continue
            info = transaction.get("step_up_code_info")
            push_name = "Verified Duo Push" if info is not None else "Duo Mobile Push"
            label = f"[{key_name}] {push_name}"
            summary = transaction.get("summary") or transaction.get("type") or "Sign-in"
            if self.push_expired(transaction):
                self.say(f"[{key_name}] Skipped an expired Duo transaction.")
                handled.add(transaction_id)
                continue
            if is_pending is not None and not is_pending(key_name, transaction_id):
                continue
            self.say(f"\n{label}: {summary}")
            while True:
                if self.push_expired(transaction):
                    self.say(f"{label} expired.")
                    break
                try:
                    answer = (
                        self.prompt_step_up_code(info, key_name=key_name)
                        if info is not None
                        else self.prompt_push_action(key_name)
                    )
                except ValueError as error:
                    self.say(f"[{key_name}] Cannot process {push_name}: {error}.")
                    break
                if answer is None:
                    return False
                if answer is False:
                    self.say(f"{label} skipped.")
                    break
                # Input can outlive the transaction or a later poll may cancel it.
                if self.push_expired(transaction) or (
                    is_pending is not None and not is_pending(key_name, transaction_id)
                ):
                    self.say(f"{label} is no longer pending.")
                    break
                reply_data = dict(self.push_parameters(key), answer="approve")
                if info is not None:
                    reply_data.update(
                        step_up_code=answer, step_up_code_autofilled="false"
                    )
                try:
                    reply = self.duo_request(
                        key,
                        "POST",
                        "/push/v2/device/transactions/" + transaction_id,
                        reply_data,
                    )
                except PUSH_ERRORS as error:
                    self.say(
                        f"{label} approval could not be confirmed: "
                        f"{self.request_error(error)}. Still listening."
                    )
                    return True
                if reply.get("stat") == "OK":
                    self.say(f"{label} approved.")
                    break
                if info is not None and str(reply.get("code")) == "40032":
                    self.say("Incorrect verification code.")
                    continue
                message = reply.get("message")
                self.say(f"{label} rejected" + (f": {message}" if message else "."))
                break
            handled.add(transaction_id)
        return True

    def push_loop(self, key_name):
        self.listen_for_pushes([key_name])

    def generate_passcodes(self):
        self.passcodes.clear()
        if self.display is None:
            print(
                f"\nVault: {Path(self.config_file).name if self.config_file else '(unsaved)'}"
            )
        for name in list(self.config["keys"]):
            self.generate_passcode(name)

    def listen_for_pushes(self, key_names, *, generate_passcodes=False):
        keys = {
            name: key
            for name in key_names
            if (key := self.validated_push_key(name)) is not None
        }
        handled = {name: set() for name in keys}
        failures, poll_errors = {}, {}
        self.passcodes.clear()
        if (
            sys.stdin.isatty()
            and sys.stdout.isatty()
            and (sys.platform == "win32" or not is_dumb_terminal())
        ):
            self.display = LiveDisplay(
                Path(self.config_file).name if self.config_file else "(unsaved)"
            )
            self.display.count = len(keys)
            self.display.poll_errors = poll_errors
        try:
            with (
                closing(
                    self.display if self.display is not None else EnterInput()
                ) as keyboard,
                PushListener(keys, self.poll_pushes, interval=POLL_SECONDS) as listener,
            ):
                keyboard.codes = self.passcodes
                if generate_passcodes:
                    self.generate_passcodes()
                if not keys:
                    self.say("No keys support mobile push. Use --menu to manage keys.")
                    if not any(callable(row) for row in self.passcodes.values()):
                        return
                if self.display is None:
                    print(
                        f"\nListening for mobile pushes on {len(keys)} key(s).",
                        "- Enter: regenerate all passcodes",
                        "- Ctrl+C: stop listening",
                        sep="\n",
                    )
                while True:
                    try:
                        update = keyboard.get(listener)
                    except Empty:
                        continue
                    if update is None:
                        self.generate_passcodes()
                        continue
                    name, result = update
                    try:
                        if isinstance(result, str):
                            raise PushResponseError(result)
                        push_transactions(result)
                        failures.pop(name, None)
                        if poll_errors.pop(name, None) and self.display is None:
                            print(f"[{name}] Mobile push connection restored.")
                        if not self.process_pushes(
                            name, keys[name], result, handled[name], listener.is_pending
                        ):
                            return
                    except PUSH_ERRORS as error:
                        detail = self.request_error(error)
                        failures[name] = failures.get(name, 0) + 1
                        if detail == "connection failed" and failures[name] == 1:
                            continue  # Retry an isolated connection drop quietly.
                        message = (
                            f"[{name}] Mobile push check failed: {detail}, retrying."
                        )
                        if poll_errors.get(name) != message:
                            poll_errors[name] = message
                            if self.display is None:
                                print(message)
        except (KeyboardInterrupt, EOFError):
            print("\nStopped checking for mobile pushes.")
        finally:
            self.display = None
            self.passcodes.clear()

    def run_default(self):
        names = list(self.config["keys"])
        if not names:
            print("No keys saved. Run with --menu to add a key.")
            return
        self.listen_for_pushes(names, generate_passcodes=True)

    def generate_passcode(self, key_name):
        key = self.config["keys"][key_name]
        response = key.get("response") if isinstance(key, dict) else None
        if not isinstance(response, dict):
            self.show_passcode(
                key_name, "This key has invalid Duo Mobile Passcode data."
            )
            return
        try:
            raw_secret = response["hotp_secret"]
            use_totp = response.get("use_totp", False)
            if (
                not isinstance(raw_secret, str)
                or not raw_secret
                or type(use_totp) is not bool
            ):
                raise TypeError
            secret = base64.b32encode(raw_secret.encode("ascii")).decode("ascii")
            # Duo's activation response selects the algorithm, despite the secret's name.
            if use_totp:
                self.show_passcode(key_name, partial(totp_line, secret))
                return
            counter = key.get("hotp_counter", 0)
            history = key.get("hotp_log", [])
            if (
                type(counter) is not int
                or not 0 <= counter < 2**64 - 1
                or not isinstance(history, list)
            ):
                raise ValueError
            counter += 1
            code = pyotp.HOTP(secret).at(counter)
        except (KeyError, TypeError, UnicodeError, ValueError):
            self.show_passcode(
                key_name, "This key does not support Duo Mobile Passcodes."
            )
            return

        entry = f"{datetime.now(timezone.utc):%Y-%m-%d %H:%M:%S} ({key_name}): {code}"
        self.config["keys"][key_name] = dict(
            key, hotp_counter=counter, hotp_log=[*history, entry]
        )
        try:
            self.save_config()
        except (OSError, ValueError):
            self.config["keys"][key_name] = key
            self.show_passcode(
                key_name, "Passcode not generated: the vault could not be saved."
            )
            return
        self.show_passcode(key_name, f"Duo Mobile Passcode: {code}")

    def passcode_history(self, key_name):
        key = self.config["keys"][key_name]
        history = key.get("hotp_log", []) if isinstance(key, dict) else None
        if not isinstance(history, list):
            print("This key has invalid passcode history.")
            return
        if not history:
            print("No Duo Mobile Passcode history.")
            return
        while True:
            print(
                f"\nNewest 10 of {len(history)} saved Duo Mobile Passcodes:",
                *history[-10:],
                sep="\n",
            )
            if not self.menu(
                "History actions", "Delete older history (keep newest 10)"
            ):
                return
            if len(history) <= 10:
                print("There is no older history to delete.")
                continue
            if self.ask(f"Delete {len(history) - 10} older entries? [y/N]: ") not in (
                "y",
                "Y",
            ):
                continue
            key["hotp_log"] = history[-10:]
            try:
                self.save_config()
            except (OSError, ValueError):
                key["hotp_log"] = history
                print("Could not save the history change.")
            else:
                history = key["hotp_log"]
                print("Older passcode history deleted.")

    def delete_key(self, name):
        if self.ask(
            f"Delete '{name}' locally? This does not revoke it in Duo. [y/N]: "
        ) not in ("y", "Y"):
            return
        deleted = self.config["keys"].pop(name)
        try:
            self.save_config()
            print(f"Key '{name}' deleted.")
        except (OSError, ValueError):
            self.config["keys"][name] = deleted
            print("Could not save the deletion.")

    def keys_menu(self):
        actions = {
            "Duo Mobile Push / Verified Duo Push": self.push_loop,
            "Generate Duo Mobile Passcode": self.generate_passcode,
            "Duo Mobile Passcode history": self.passcode_history,
            "Delete local key": self.delete_key,
        }
        while True:
            keys = list(self.config["keys"].items())
            if not keys:
                print("No keys saved.")
                return
            labels = []
            for name, key in keys:
                response = key.get("response") if isinstance(key, dict) else None
                organization = (
                    response.get("customer_name")
                    if isinstance(response, dict)
                    else None
                )
                labels.append(name + (f" ({organization})" if organization else ""))
            if not (choice := self.menu("Keys", *labels, default=1)):
                return
            name = keys[choice - 1][0]

            while name in self.config["keys"] and (
                choice := self.menu(name, *actions, default=1)
            ):
                tuple(actions.values())[choice - 1](name)

    def main_menu(self):
        self.action_menu(
            "Main menu",
            {
                "Keys": self.keys_menu,
                "Add key": self.add_key,
                "Vault settings": self.vault_settings,
            },
            back="Exit",
            default=1,
        )

    def close(self):
        lock_file, self.lock_file = self.lock_file, None
        if lock_file:
            with suppress(OSError, ValueError, portalocker.exceptions.LockException):
                lock_file.release()
        self.wipe(self.encryption_key)
        self.salt = self.encryption_key = self.vault_digest = None
        self.config.clear()
        self.passcodes.clear()


def main(argv=None):
    parser = argparse.ArgumentParser(
        description="Print a fresh passcode for each key and listen for mobile pushes."
    )
    parser.add_argument(
        "--menu",
        action="store_true",
        help="open interactive menus instead of automatic passcodes and push listening",
    )
    args = parser.parse_args(argv)
    with closing(DuoAuthenticator()) as app:
        try:
            if (app.config_file or app.select_vault()) and app.load_config():
                if args.menu:
                    app.main_menu()
                else:
                    app.run_default()
        except (KeyboardInterrupt, EOFError):
            print("\nExited safely.")


if __name__ == "__main__":
    main()
