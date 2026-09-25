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
from contextlib import closing, redirect_stdout, suppress
from copy import deepcopy
from datetime import datetime, timezone
from email.utils import format_datetime
from pathlib import Path
from queue import Empty
from threading import Condition, Event, Thread
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
from prompt_toolkit import PromptSession
from prompt_toolkit.history import DummyHistory
from prompt_toolkit.input import create_input
from prompt_toolkit.input.typeahead import get_typeahead
from prompt_toolkit.key_binding import KeyBindings
from prompt_toolkit.keys import Keys
from prompt_toolkit.layout.controls import FormattedTextControl
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
            if key in ("m", "M"):
                return "menu"
            if key == Keys.Enter or (key == Keys.ControlJ and previous != Keys.Enter):
                return True
        return False

    def close(self):
        if self.input is not None:
            self.input.close()

    def get(self, listener):
        refresh = self()
        if refresh == "menu":
            return "menu"
        step = int(time.time()) // 30
        if not refresh and step != self.step:
            timed = {name: row for name, row in self.codes.items() if row[0] == "TOTP"}
            if timed:
                print(*passcode_lines(timed), sep="\n")
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
            *passcode_lines(self.codes),
            "",
            f"Listening for pushes ({self.count} keys)",
        ]
        if not prompt:
            rows.extend(("- Enter: refresh passcodes", "- m: menu"))
        rows.append("- Ctrl+C: stop")
        if self.status:
            rows.extend(("", self.status))
        if self.poll_errors:
            rows.extend(("", *self.poll_errors.values()))
        return "\n".join(rows) + "\n" + prompt

    def get(self, listener):
        bindings = KeyBindings()

        @bindings.add("m")
        @bindings.add("M")
        def menu(event):
            event.app.exit(result="menu")

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
            result = self.session.prompt(self.render, key_bindings=bindings)
            return result if result == "menu" or isinstance(result, tuple) else None
        finally:
            self.session.app.before_render -= poll
            self.session.key_bindings = None

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
        return self.session.prompt(lambda: self.render(prompt), pre_run=self._discard_input)

    def close(self):
        self.codes.clear()
        self.status = ""
        self.poll_errors.clear()
        self.session.default_buffer.reset()
        get_typeahead(self.session.app.input)
        self.session.app.input.close()


class PasswordStoreError(RuntimeError):
    """Native password storage failed."""


def _local_data_dir(platform):
    home = Path.home()
    if platform == "win32":
        base = Path(os.environ.get("LOCALAPPDATA") or home / "AppData" / "Local")
    elif platform == "darwin":
        base = home / "Library" / "Application Support"
    elif platform.startswith("linux"):
        base = Path(os.environ.get("XDG_STATE_HOME", ""))
        if not base.is_absolute():
            base = home / ".local" / "state"
    else:
        raise PasswordStoreError("Secure storage is unsupported on this OS.")
    if not base.is_absolute():
        raise PasswordStoreError("Password storage requires an absolute path.")
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
                raise PasswordStoreError("Secure storage is unsupported on this OS.")
            if backend.is_encrypted is not True:
                raise PasswordStoreError("Refusing unencrypted password storage.")
            return backend, persistence.PersistenceNotFound
        except PasswordStoreError:
            raise
        except ImportError:
            raise PasswordStoreError(
                "Secure storage unavailable, check msal-extensions and your OS keyring."
            ) from None
        except Exception:
            raise PasswordStoreError("OS secure storage unavailable. Unlock manually.") from None

    def load(self):
        """Missing signal or secret means no auto-unlock, backend errors raise."""
        try:
            if not stat.S_ISREG(self.location.stat().st_mode):
                raise OSError
        except FileNotFoundError:
            return None
        except OSError:
            raise PasswordStoreError("Cannot access local password storage.") from None
        backend, not_found = self._open()
        try:
            password = backend.load()
            if not isinstance(password, str):
                raise TypeError
            return password or None
        except not_found:
            return None
        except Exception:
            raise PasswordStoreError("Cannot read saved password. Unlock manually.") from None

    def save(self, password):
        if not isinstance(password, str) or not password:
            raise PasswordStoreError("Password must be a nonempty string.")
        self._write(password, "save")

    def _write(self, password, action):
        backend, _ = self._open()
        try:
            backend.save(password)
            # Libsecret can fail silently, verify both saves and empty tombstones.
            if backend.load() != password:
                raise ValueError
        except Exception:
            raise PasswordStoreError(
                f"Cannot {action} and verify the password in OS secure storage."
            ) from None

    def forget(self):
        """Remove the DPAPI blob, replace native-keyring secrets with empty text."""
        if self._platform != "win32":
            # MSAL has no public keyring deletion API. Clear even without a signal:
            # a previous save may have stored the secret but failed to create it.
            return self._write("", "clear")
        try:
            self.location.unlink(missing_ok=True)
        except OSError:
            raise PasswordStoreError("Cannot remove saved password.") from None


def key_otp(key):
    """Build the configured OTP, HOTP starts at the next unused counter."""
    response = key["response"]
    raw_secret = response["hotp_secret"]
    use_totp = response.get("use_totp", False)
    if not isinstance(raw_secret, str) or not raw_secret or type(use_totp) is not bool:
        raise ValueError("Invalid OTP data")
    secret = base64.b32encode(raw_secret.encode("ascii")).decode("ascii")
    if use_totp:
        return pyotp.TOTP(secret)
    counter = key.get("hotp_counter", 0)
    if type(counter) is not int or not 0 <= counter < 2**64 - 1:
        raise ValueError("Invalid HOTP counter")
    return pyotp.HOTP(secret, initial_count=counter + 1)


def passcode_hidden(key):
    return isinstance(key, dict) and key.get("hide_passcode") is True


def passcode_lines(codes):
    now = time.time()
    timestamp = datetime.fromtimestamp(now, timezone.utc)
    for kind in ("TOTP", "HOTP", ""):
        group = [(name, value) for name, (mode, value) in codes.items() if mode == kind]
        if not group:
            continue
        heading = f"Passcodes ({kind})" if kind else "Unavailable"
        if kind == "TOTP":
            expires = datetime.fromtimestamp((int(now) // 30 + 1) * 30, timezone.utc)
            heading = f"Passcodes (TOTP, expires {expires.astimezone():%H:%M:%S})"
        yield heading
        for name, value in group:
            yield f"- [{name}] {value.at(timestamp) if kind == 'TOTP' else value}"


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


def response_json(response):
    if response.status_code in range(300, 400):
        raise ValueError("Duo request redirected unexpectedly")
    response.raise_for_status()
    result = response.json()
    if not isinstance(result, dict):
        raise ValueError("Invalid Duo response")
    return result


class PushListener:
    """Independent polling workers, at most one unread result per key."""

    def __init__(self, keys, poll, interval=5):
        if interval < 0:
            raise ValueError("Polling interval cannot be negative")
        self._keys = deepcopy(keys)
        self._poll = poll
        self._interval = interval
        self._stop = Event()
        self._condition = Condition()
        self._updates = {}
        self._pending = {}
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
                pending = {
                    transaction["urgid"]
                    for transaction in push_transactions(result)
                    if isinstance(transaction, dict) and isinstance(transaction.get("urgid"), str)
                }
            except Exception as error:  # noqa: BLE001 - isolate worker failures
                result = DuoAuthenticator.request_error(error)
            with self._condition:
                if self._stop.is_set():
                    return
                if isinstance(result, dict):
                    self._pending[name] = pending
                self._updates[name] = result
                self._condition.notify()
            if self._stop.wait(self._interval):
                return

    def get(self, timeout=0.25):
        """Return (key name, latest result), raising queue.Empty on timeout."""
        with self._condition:
            if not self._condition.wait_for(lambda: self._updates, timeout):
                raise Empty
            name = next(iter(self._updates))
            return name, self._updates.pop(name)

    def is_pending(self, name, urgid):
        """Check the latest validated snapshot, excluding malformed entries."""
        with self._condition:
            return isinstance(urgid, str) and urgid in self._pending.get(name, ())

    def close(self):
        """Discard late results, join all daemon workers within one second."""
        with self._condition:
            self._stop.set()
        deadline = monotonic() + 1
        for worker in self._threads:
            worker.join(max(0, deadline - monotonic()))

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

    def ask(self, prompt):
        try:
            read = self.display.ask if self.display is not None else input
            return read(prompt).strip()
        except (EOFError, KeyboardInterrupt):
            if self.display is None:
                print()
            return None

    def confirm(self, prompt, *, default=False):
        answer = self.ask(f"{prompt} [{'Y/n' if default else 'y/N'}]: ")
        return answer is not None and (answer.lower() != "n" if default else answer.lower() == "y")

    @staticmethod
    def menu(title, *options, back="Back", default=None):
        """Return 1..N for an option, or None for Back/cancellation."""
        if default is not None and not 1 <= default <= len(options):
            raise ValueError("The default must identify a menu option")
        bindings = KeyBindings()

        @bindings.add("up", eager=True)
        @bindings.add("down", eager=True)
        def move(event):
            control = event.app.layout.current_control

            def position():
                # Fresh content handles several keystrokes between redraws.
                content = FormattedTextControl(control.text).create_content(0, 0)
                return content.cursor_position

            previous = position()
            key = event.key_sequence[-1].key
            native = control.get_key_bindings()
            native.get_bindings_for_keys((key,))[-1].call(event)
            if position() == previous:
                opposite = Keys.Down if key == Keys.Up else Keys.Up
                step = native.get_bindings_for_keys((opposite,))[-1]
                for _ in options:
                    step.call(event)

        try:
            return (
                choice(
                    title,
                    options=[*enumerate(options, 1), (0, back)],
                    default=default or 0,
                    key_bindings=bindings,
                )
                or None
            )
        except (EOFError, KeyboardInterrupt):
            return None

    def action_menu(self, title, actions, **options):
        callbacks = tuple(actions.values())
        while choice := self.menu(title, *actions, **options):
            callbacks[choice - 1]()

    @staticmethod
    def password(prompt, confirm=False, *, min_length=12):
        try:
            while True:
                password = getpass.getpass(prompt)
                if not password or not confirm:
                    return password or None
                if len(password) < min_length:
                    print(f"Use at least {min_length} characters for the vault password.")
                    continue
                if password == getpass.getpass("Confirm password: "):
                    return password
                print("Passwords do not match.")
        except (EOFError, KeyboardInterrupt):
            print()
            return None

    @staticmethod
    def vault_filename(name):
        if not name:
            return None
        if (
            name in {".", ".."}
            or name.endswith((".", " "))
            or re.search(r'[<>:"/\\|?*\x00-\x1f]', name)
            or re.match(
                r"(?i:con|prn|aux|nul|com[1-9¹²³]|lpt[1-9¹²³]|conin\$|conout\$) *(?:\.|$)",
                name,
            )
        ):
            print("Enter a valid filename, without a path.")
            return None
        return name if name.lower().endswith(".duo") else name + ".duo"

    def select_vault(self, *, create=True):
        for directory in (Path.cwd(), Path(__file__).resolve().parent):
            vaults = sorted(
                (path for path in directory.glob("*.duo") if path.is_file()),
                key=lambda path: path.name.lower(),
            )
            if vaults:
                break
        if vaults:
            choice = 1
            if len(vaults) > 1:
                choice = self.menu("Vaults", *(path.name for path in vaults), back="Exit")
            if not choice:
                return False
            self.config_file = vaults[choice - 1]
            return True

        if not create:
            print("No Duo vault found.")
            return False
        print("No Duo vault found. Create one to continue.")
        while name := self.ask("Vault name (leave empty to exit): "):
            if filename := self.vault_filename(name):
                self.config_file = Path(filename)
                return True
        return False

    @staticmethod
    def derive_key(password, salt):
        try:
            return bytearray(scrypt(password.encode(), salt, 64, SCRYPT_N, SCRYPT_R, SCRYPT_P))
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
            if not isinstance(config, dict) or not isinstance(config.setdefault("keys", {}), dict):
                raise ValueError("Invalid vault data")
            return config, key, salt
        except BaseException:
            self.wipe(key)
            raise
        finally:
            self.wipe(plaintext)

    @staticmethod
    def acquire_vault_lock(path):
        lock = portalocker.Lock(
            str(Path(path).absolute()) + ".lock",
            mode="a+b",
            timeout=0,
            opener=lambda path, flags: os.open(path, flags, 0o600),
        )
        try:
            lock.acquire()
        except (OSError, portalocker.exceptions.LockException):
            return None
        return lock

    def lock_vault(self):
        if self.lock_file is None and self.config_file:
            self.lock_file = self.acquire_vault_lock(self.config_file)
        return self.lock_file is not None

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
                    self.config, self.encryption_key, self.salt = self.decrypt_vault(blob, password)
                except (ValueError, TypeError):
                    if using_saved_password:
                        print("Saved password did not unlock this vault. Enter it manually.")
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

        plaintext = bytearray(json.dumps(self.config, separators=(",", ":")).encode("utf-8"))
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
                dir=path.parent, prefix=f".{path.name}.", suffix=".tmp"
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
                Path(temp_path).unlink(missing_ok=True)

    def get_password_store(self):
        if self.password_store is None:
            self.password_store = PasswordStore(self.config_file)
        return self.password_store

    def verified_password(self, password=None):
        """Verify a supplied password, or prompt for the current one."""
        if password is None:
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
            self.forget_password()
            return False

    def remember_password(self):
        print("This OS account will be able to unlock the vault automatically.")
        password = self.verified_password()
        if password is not None and self.save_password(password):
            print("Vault password saved securely on this device.")

    def forget_password(self):
        try:
            self.get_password_store().forget()
        except PasswordStoreError:
            print("Could not forget the saved password. Try again.")
            return
        print("Saved password forgotten. Next launch requires manual unlock.")

    def vault_settings(self):
        self.action_menu(
            "Vault settings",
            {
                "Rename vault": self.rename_vault,
                "Remember vault password on this device": self.remember_password,
                "Forget saved password": self.forget_password,
                "Change vault password": self.change_password,
            },
        )

    def rename_vault(self):
        name = self.vault_filename(self.ask("New vault name (empty to cancel): "))
        if not name:
            return
        source = Path(self.config_file)
        target = source.with_name(name)
        if os.path.normcase(str(source.absolute())) == os.path.normcase(str(target.absolute())):
            return
        lock = None
        try:
            if not self.lock_vault() or source.is_symlink():
                raise OSError("Vault cannot be renamed")
            lock = self.acquire_vault_lock(target)
            if lock is None:
                raise OSError("Destination vault is locked")
            if hashlib.sha256(source.read_bytes()).digest() != self.vault_digest:
                raise OSError("Vault was changed by another process")
            if os.name == "nt":
                os.rename(source, target)  # Windows refuses an existing target.
            else:
                os.link(source, target)  # Atomically create without overwriting.
                try:
                    source.unlink()
                except OSError:
                    target.unlink()
                    raise
            self.lock_file, lock = lock, self.lock_file
        except (OSError, portalocker.exceptions.LockException):
            print("Could not rename vault. Check permissions and open copies.")
            return
        finally:
            if lock is not None:
                with suppress(OSError, ValueError, portalocker.exceptions.LockException):
                    lock.release()
        old_store = self.get_password_store()
        self.config_file = target
        self.password_store = PasswordStore(target)
        self.migrate_password(old_store)
        print(f"Vault renamed to {target.name}.")

    def migrate_password(self, old_store):
        """Move a verified saved password, never replace another store entry."""
        clear_old = True
        try:
            password = old_store.load()
            clear_old = password is not None
            if password is None:
                return
            if self.verified_password(password) is None:
                raise PasswordStoreError("Saved password is stale")
            if self.password_store.load() is not None:
                raise PasswordStoreError("Destination already has a saved password")
            self.save_password(password)
        except (PasswordStoreError, RuntimeError, TypeError):
            print("Saved password not moved. Unlock manually, then remember it again.")
        finally:
            if clear_old:
                try:
                    old_store.forget()
                except PasswordStoreError:
                    print("Could not clear the old vault's saved password.")

    def change_password(self):
        if self.verified_password() is None:
            return
        password = self.password("New vault password (leave empty to cancel): ", confirm=True)
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
        print("Vault password changed.")

    @staticmethod
    def parse_activation_url(activation_url):
        match = (
            ACTIVATION_URL.fullmatch(activation_url) if isinstance(activation_url, str) else None
        )
        if not match:
            raise ValueError("invalid Duo activation URL")
        return match[2], f"api-{match[1].lower()}.duosecurity.com"

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
            activation = response_json(response).get("response")
            if not isinstance(activation, dict):
                raise ValueError("Activation was rejected")
            return activation, public_key, private_key
        except (requests.RequestException, ValueError, TypeError):
            print("Duo activation failed. Check the code, host, and connection.")
            return None

    def add_key(self):
        print("\nWhen setting up a new Duo device, select Apple iOS tablet.")
        while name := self.ask("Nickname (leave empty to cancel): "):
            if name not in self.config["keys"]:
                break
            print("That nickname already exists.")
        else:
            return

        while url := self.ask("Activation URL (leave empty to cancel): "):
            try:
                code, host = self.parse_activation_url(url)
            except ValueError as error:
                print(f"Invalid Duo activation URL: {error}")
                continue
            break
        else:
            return

        while not (activated := self.activate(code, host)):
            if not self.confirm("Retry this activation?", default=True):
                return

        response, public_key, private_key = activated
        key = {
            "code": code,
            "host": host,
            "response": response,
            "pubkey": public_key,
            "privkey": private_key,
        }
        while not self.save_changes(self.config["keys"], {name: key}):
            print("Save failed. This activation may be one-use, leaving permanently discards it.")
            if not self.confirm("Retry saving?", default=True):
                print("The activated key was not saved.")
                return
        print(f"Key '{name}' added.")

    def duo_request(self, key, method, path, data):
        # Duo verifies a canonical, alphabetically sorted parameter string.
        data = dict(sorted(data.items()))
        private_key = RSA.import_key(key["privkey"].encode("ascii"))
        duo_date = format_datetime(datetime.now(timezone.utc))
        message = "\n".join((duo_date, method, key["host"].lower(), path, urlencode(data))).encode(
            "ascii"
        )
        signature = base64.b64encode(pkcs1_15.new(private_key).sign(SHA512.new(message))).decode(
            "ascii"
        )
        credentials = f"{key['response']['pkey']}:{signature}".encode("ascii")
        headers = {
            "Authorization": "Basic " + base64.b64encode(credentials).decode("ascii"),
            "x-duo-date": duo_date,
            "host": key["host"],
        }
        if method == "POST":
            headers["txId"] = path.rsplit("/", 1)[-1]
        response = requests.request(
            method,
            f"https://{key['host']}{path}",
            headers=headers,
            params=data if method == "GET" else None,
            data=data if method == "POST" else None,
            timeout=REQUEST_TIMEOUT,
            allow_redirects=False,
        )
        if method == "POST" and response.status_code == 400:
            with suppress(ValueError):
                rejection = response.json()
                if (
                    isinstance(rejection, dict)
                    and rejection.get("stat") == "FAIL"
                    and str(rejection.get("code")) == "40032"
                ):
                    return {"stat": "FAIL", "code": 40032}
        return response_json(response)

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

    def validated_push_key(self, key_name):
        """Copy only the credentials needed by polling workers, never vault state."""
        key = self.config["keys"][key_name]
        try:
            response = {field: key["response"][field] for field in ("akey", "pkey")}
            if not re.fullmatch(r"api-[0-9a-f]+\.duosecurity\.com", key["host"].lower()) or not all(
                re.fullmatch(r"[A-Za-z0-9._~-]{1,512}", v) for v in response.values()
            ):
                raise ValueError
            RSA.import_key(key["privkey"].encode("ascii"))
            return {"host": key["host"], "privkey": key["privkey"], "response": response}
        except (ValueError, TypeError, KeyError, AttributeError, IndexError):
            print(f"[{key_name}] This key has invalid Duo Mobile Push data.")

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

    def prompt_push_action(self, key_name, info=None):
        digits = info.get("num_digits") if isinstance(info, dict) else None
        if info is not None and (type(digits) is not int or not 3 <= digits <= 7):
            raise ValueError("invalid Verified Duo Push metadata")
        prompt = (
            f"Enter the {digits}-digit verification code (blank to stop): "
            if info is not None
            else "[Enter/y] Approve, [s] skip, [q] stop: "
        )
        while True:
            answer = self.ask(f"[{key_name}] {prompt}")
            if info is not None:
                if not answer:
                    return None
                if re.fullmatch(rf"[0-9]{{{digits}}}", answer):
                    return answer
                self.say(f"Enter exactly {digits} ASCII digits.")
            else:
                answer = answer.lower() if answer else answer
                if answer in (None, "q"):
                    return None
                if answer in ("y", "", "s", "n"):
                    return answer in ("", "y")
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
                    answer = self.prompt_push_action(key_name, info)
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
                    reply_data.update(step_up_code=answer, step_up_code_autofilled="false")
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
        for name, key in list(self.config["keys"].items()):
            if not passcode_hidden(key):
                self.passcodes[name] = self.make_passcode(name)
        if self.display is None:
            print(
                f"\nVault: {Path(self.config_file).name if self.config_file else '(unsaved)'}",
                *passcode_lines(self.passcodes),
                sep="\n",
            )

    def listen_for_pushes(self, key_names, *, generate_passcodes=False):
        keys = {
            name: key for name in key_names if (key := self.validated_push_key(name)) is not None
        }
        handled = {name: set() for name in keys}
        failures, poll_errors = set(), {}
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
                closing(self.display or EnterInput()) as keyboard,
                PushListener(keys, self.poll_pushes, interval=POLL_SECONDS) as listener,
            ):
                keyboard.codes = self.passcodes
                if generate_passcodes:
                    self.generate_passcodes()
                if not keys:
                    self.say("No keys support mobile push.")
                    if not any(kind for kind, _ in self.passcodes.values()):
                        return "menu" if generate_passcodes else None
                if self.display is None:
                    print(
                        f"\nListening for pushes ({len(keys)} keys)",
                        "- Enter: refresh passcodes",
                        "- m: menu",
                        "- Ctrl+C: stop",
                        sep="\n",
                    )
                while True:
                    try:
                        update = keyboard.get(listener)
                    except Empty:
                        continue
                    if update == "menu":
                        return "menu"
                    if update is None:
                        self.generate_passcodes()
                        continue
                    name, result = update
                    try:
                        if isinstance(result, str):
                            raise PushResponseError(result)
                        push_transactions(result)
                        failures.discard(name)
                        if poll_errors.pop(name, None) and self.display is None:
                            print(f"[{name}] Mobile push connection restored.")
                        if not self.process_pushes(
                            name, keys[name], result, handled[name], listener.is_pending
                        ):
                            return
                    except PUSH_ERRORS as error:
                        detail = self.request_error(error)
                        first_failure = name not in failures
                        failures.add(name)
                        if detail == "connection failed" and first_failure:
                            continue  # Retry an isolated connection drop quietly.
                        message = f"[{name}] Mobile push check failed: {detail}, retrying."
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
        if self.passcode_screen() == "menu":
            self.main_menu()

    def passcode_screen(self):
        names = list(self.config["keys"])
        if not names:
            print("No keys saved.")
            return "menu"
        return self.listen_for_pushes(names, generate_passcodes=True)

    def generate_passcode(self, key_name):
        self.passcodes[key_name] = self.make_passcode(key_name)
        if self.display is None:
            print(*passcode_lines({key_name: self.passcodes[key_name]}), sep="\n")

    def save_changes(self, mapping, changes):
        """Save an update, restoring the original objects if the write fails."""
        previous = mapping.copy()
        mapping.update(changes)
        try:
            self.save_config()
        except (OSError, ValueError):
            mapping.clear()
            mapping.update(previous)
            return False
        return True

    def make_passcode(self, key_name):
        key = self.config["keys"][key_name]
        try:
            otp = key_otp(key)
            if isinstance(otp, pyotp.TOTP):
                return "TOTP", otp
            history = key.get("hotp_log", [])
            if not isinstance(history, list):
                raise ValueError
            code = otp.at(0)
        except (KeyError, TypeError, UnicodeError, ValueError):
            return "", "Passcodes not supported."

        entry = f"{datetime.now(timezone.utc):%Y-%m-%d %H:%M:%S} ({key_name}): {code}"
        updated = dict(key, hotp_counter=otp.initial_count, hotp_log=[*history, entry])
        if not self.save_changes(self.config["keys"], {key_name: updated}):
            return "", "Passcode not generated: the vault could not be saved."
        return "HOTP", code

    def export_secret(self, name):
        try:
            otp = key_otp(self.config["keys"][name])
            uri = otp.provisioning_uri(name=name.replace(":", " -"), issuer_name="Duo")
        except (KeyError, TypeError, UnicodeError, ValueError):
            print("This key has invalid or unsupported OTP data.")
            return
        use_totp = isinstance(otp, pyotp.TOTP)
        print(
            f"\n[{name}] OTP export - keep this secret private.",
            f"Secret key (Base32): {otp.secret}",
            "TOTP: SHA-1, 6 digits, 30 seconds."
            if use_totp
            else f"HOTP: SHA-1, 6 digits, initial counter {otp.initial_count}.",
            f"Setup URI: {uri}",
            "KeePass: OTP Generator Settings > Import, paste the setup URI.",
            "KeePassXC: TOTP > Set up TOTP, paste the secret and use these settings."
            if use_totp
            else "KeePassXC does not support HOTP. After import, generate codes in KeePass only.",
            sep="\n",
        )

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
            if not self.menu("History actions", "Delete older history (keep newest 10)"):
                return
            if len(history) <= 10:
                print("There is no older history to delete.")
                continue
            if not self.confirm(f"Delete {len(history) - 10} older entries?"):
                continue
            if self.save_changes(key, {"hotp_log": history[-10:]}):
                history = key["hotp_log"]
                print("Older passcode history deleted.")
            else:
                print("Could not save the history change.")

    def set_key_password(self, name):
        key = self.config["keys"][name]
        if not isinstance(key, dict):
            print("Invalid key data.")
            return
        password = self.password("Key password (blank to cancel): ", confirm=True, min_length=0)
        if password is None:
            return
        saved = self.save_changes(self.config["keys"], {name: dict(key, password=password)})
        print("Password saved." if saved else "Could not save the password.")

    def forget_key_password(self, name):
        key = self.config["keys"][name]
        if not isinstance(key, dict) or "password" not in key:
            print("No password saved for this key.")
            return
        if not self.confirm(f"Forget the password for '{name}'?"):
            return
        updated = {field: value for field, value in key.items() if field != "password"}
        saved = self.save_changes(self.config["keys"], {name: updated})
        print("Password forgotten." if saved else "Could not remove the password.")

    def rename_key(self, name):
        keys = self.config["keys"]
        while True:
            new_name = self.ask(f"New name for '{name}' (blank to cancel): ")
            if not new_name or new_name == name:
                return
            if new_name not in keys:
                break
            print("A key with that name already exists.")
        renamed = {
            new_name if old_name == name else old_name: key for old_name, key in keys.items()
        }
        if self.save_changes(self.config, {"keys": renamed}):
            self.passcodes.pop(name, None)
            self.passcodes.pop(new_name, None)
            print(f"Key '{name}' renamed to '{new_name}'.")
        else:
            print("Could not save the name change.")

    def toggle_passcode_visibility(self, name):
        key = self.config["keys"][name]
        if not isinstance(key, dict):
            print("Invalid key data.")
            return
        hidden = not passcode_hidden(key)
        if self.save_changes(self.config["keys"], {name: dict(key, hide_passcode=hidden)}):
            self.passcodes.pop(name, None)
            print(f"[{name}] Passcode {'hidden' if hidden else 'shown'}.")
        else:
            print("Could not save passcode visibility.")

    def delete_key(self, name):
        if not self.confirm(f"Delete '{name}' locally? This does not revoke it in Duo."):
            return
        remaining = {n: key for n, key in self.config["keys"].items() if n != name}
        saved = self.save_changes(self.config, {"keys": remaining})
        print(f"Key '{name}' deleted." if saved else "Could not save the deletion.")

    def keys_menu(self):
        actions = {
            "Duo Mobile Push / Verified Duo Push": self.push_loop,
            "Generate Duo Mobile Passcode": self.generate_passcode,
            "Duo Mobile Passcode history": self.passcode_history,
            "Delete local key": self.delete_key,
            "Rename key": self.rename_key,
            "Export OTP secret to KeePass": self.export_secret,
            "Show/hide passcode": self.toggle_passcode_visibility,
            "Set key password": self.set_key_password,
            "Forget key password": self.forget_key_password,
        }
        while True:
            keys = list(self.config["keys"].items())
            labels = ["Add key"]
            for name, key in keys:
                response = key.get("response") if isinstance(key, dict) else None
                organization = response.get("customer_name") if isinstance(response, dict) else None
                labels.append(
                    name
                    + (f" ({organization})" if organization else "")
                    + (" [hidden]" if passcode_hidden(key) else "")
                )
            if not (choice := self.menu("Keys", *labels, default=1)):
                return
            if choice == 1:
                self.add_key()
                continue
            name = keys[choice - 2][0]

            while name in self.config["keys"] and (choice := self.menu(name, *actions, default=1)):
                tuple(actions.values())[choice - 1](name)

    def main_menu(self):
        self.action_menu(
            "Main menu",
            {
                "Passcode screen": self.passcode_screen,
                "Keys": self.keys_menu,
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
        description="Show passcodes and listen for pushes. Press m to open the menu."
    )
    options = parser.add_mutually_exclusive_group()
    options.add_argument("-k", dest="key", metavar="KEYNAME", help="print this key's OTP and exit")
    options.add_argument(
        "-p", dest="password", metavar="KEYNAME", help="print this key's saved password and exit"
    )
    args = parser.parse_args(argv)
    name = args.key if args.key is not None else args.password
    output = sys.stdout
    with (
        closing(DuoAuthenticator()) as app,
        redirect_stdout(sys.stderr if name is not None else output),
    ):
        try:
            if not (
                (app.config_file or app.select_vault(create=name is None)) and app.load_config()
            ):
                return 1
            if name is None:
                app.run_default()
                return 0
            if name not in app.config["keys"]:
                print(f"Unknown key: {name}")
                return 1
            if args.password is not None:
                key = app.config["keys"][name]
                value = key.get("password") if isinstance(key, dict) else None
                if not isinstance(value, str) or not value:
                    print(f"No password saved for key: {name}")
                    return 1
            else:
                kind, value = app.make_passcode(name)
                if not kind:
                    print(value)
                    return 1
                if kind == "TOTP":
                    value = value.at(datetime.fromtimestamp(time.time(), timezone.utc))
            print(value, file=output)
            return 0
        except (KeyboardInterrupt, EOFError):
            print("\nExited safely.")
            return 1


if __name__ == "__main__":
    raise SystemExit(main())
