#!/usr/bin/env python3
# SPDX-License-Identifier: AGPL-3.0-or-later
# Version: 2.0.0
# For security updates, visit github.com/JesseNaser/DuoBreak

# When setting up a new Duo device, select Apple iOS tablet

# If there's an error mentioning libzbar-64.dll, download and install vcredist_x64.exe from:
# https://www.microsoft.com/en-gb/download/details.aspx?id=40784

import base64
import datetime
import email.utils
import getpass
import json
import os
from pathlib import Path
import re
import tempfile
import time
import urllib.parse

if os.name == "nt":
    import msvcrt
else:
    import fcntl

from Crypto.Cipher import AES
from Crypto.Hash import SHA256, SHA512
from Crypto.Protocol.KDF import PBKDF2, scrypt
from Crypto.PublicKey import RSA
from Crypto.Random import get_random_bytes
from Crypto.Signature import pkcs1_15
from Crypto.Util.Padding import unpad
from PIL import Image
import pyotp
from pyzbar.pyzbar import decode as pyzbar_decode
import requests


DB_V1 = b"DBv1"
DB_V2 = b"DBv2"
SALT_SIZE = NONCE_SIZE = TAG_SIZE = 16
SCRYPT_N, SCRYPT_R, SCRYPT_P = 2**17, 8, 1
REQUEST_TIMEOUT = (5, 30)
POLL_SECONDS = 5


class DuoAuthenticator:
    def __init__(self, config_file=None):
        self.config_file = Path(config_file) if config_file else None
        self.config = {}
        self.salt = None
        self.encryption_key = None
        self.vault_digest = None
        self.lock_file = None

    @staticmethod
    def ask(prompt):
        try:
            return input(prompt).strip()
        except (EOFError, KeyboardInterrupt):
            print()
            return None

    @classmethod
    def menu(cls, title, *options, back="Back"):
        while True:
            print(f"\n{title}")
            for number, option in enumerate(options, 1):
                print(f"{number}. {option}")
            choice = cls.ask(f"0. {back}\nSelect: ")
            if choice in (None, ""):
                return 1
            if choice in map(str, range(0, len(options) + 1)):
                return int(choice)
            print("Invalid selection.")

    @staticmethod
    def password(prompt, confirm=False):
        while True:
            try:
                password = getpass.getpass(prompt)
            except (EOFError, KeyboardInterrupt):
                print()
                return None
            if not password:
                return None
            if confirm and len(password) < 12:
                print("Use at least 12 characters for the vault password.")
                continue
            if not confirm:
                return password
            try:
                repeated = getpass.getpass("Confirm password: ")
            except (EOFError, KeyboardInterrupt):
                print()
                return None
            if password == repeated:
                return password
            print("Passwords do not match.")

    def select_vault(self):
        vaults = sorted(
            (path for path in Path.cwd().glob("*.duo") if path.is_file()),
            key=lambda path: path.name.lower(),
        )
        if len(vaults) == 1:
            self.config_file = vaults[0]
            print(f"Vault: {vaults[0].name}")
            return True
        if vaults:
            choice = self.menu("Vaults", *(path.name for path in vaults), back="Exit")
            if choice is None:
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
    def derive_v2_key(password, salt):
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

    def decrypt_vault(self, blob, password):
        if not isinstance(blob, bytes) or len(blob) < 4:
            raise ValueError("Invalid vault")
        magic = blob[:4]
        key = plaintext = None
        try:
            if magic == DB_V2:
                if len(blob) <= 4 + SALT_SIZE + NONCE_SIZE + TAG_SIZE:
                    raise ValueError("Truncated vault")
                salt = blob[4:20]
                nonce = blob[20:36]
                tag = blob[36:52]
                ciphertext = blob[52:]
                key = self.derive_v2_key(password, salt)
                cipher = AES.new(key, AES.MODE_SIV, nonce=nonce)
                cipher.update(blob[:36])
                plaintext = bytearray(cipher.decrypt_and_verify(ciphertext, tag))
                legacy = False
            elif magic == DB_V1:
                encrypted = blob[20:]
                if (
                    len(blob) < 52
                    or len(encrypted[16:]) % AES.block_size
                    or not encrypted[16:]
                ):
                    raise ValueError("Truncated legacy vault")
                salt, iv, ciphertext = blob[4:20], encrypted[:16], encrypted[16:]
                key = bytearray(
                    PBKDF2(
                        password.encode("utf-8"),
                        salt,
                        32,
                        count=100000,
                        hmac_hash_module=SHA256,
                    )
                )
                plaintext = bytearray(
                    unpad(
                        AES.new(key, AES.MODE_CBC, iv).decrypt(ciphertext),
                        AES.block_size,
                    )
                )
                legacy = True
            else:
                raise ValueError("Unsupported vault version")

            config = json.loads(plaintext.decode("utf-8"))
            if not isinstance(config, dict) or (
                "keys" in config and not isinstance(config["keys"], dict)
            ):
                raise ValueError("Invalid vault data")
            config.setdefault("keys", {})
            return config, key, salt, legacy
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
        descriptor = lock_file = None
        try:
            lock_path = Path(str(Path(self.config_file).absolute()) + ".lock")
            descriptor = os.open(lock_path, os.O_RDWR | os.O_CREAT, 0o600)
            lock_file = os.fdopen(descriptor, "r+b", buffering=0)
            descriptor = None
            lock_file.seek(0, os.SEEK_END)
            if not lock_file.tell():
                lock_file.write(b"\0")
            lock_file.seek(0)
            if os.name == "nt":
                msvcrt.locking(lock_file.fileno(), msvcrt.LK_NBLCK, 1)
            else:
                fcntl.flock(lock_file.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
        except OSError:
            if lock_file:
                lock_file.close()
            elif descriptor is not None:
                os.close(descriptor)
            return False
        self.lock_file = lock_file
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
                salt = get_random_bytes(SALT_SIZE)
                try:
                    key = self.derive_v2_key(password, salt)
                except RuntimeError:
                    print("Not enough resources to secure the vault.")
                    return False
                password = None
                self.config = {"keys": {}}
                try:
                    self.save_config(key=key, salt=salt)
                except (OSError, ValueError):
                    self.wipe(key)
                    self.config.clear()
                    print("Could not create the encrypted vault.")
                    return False
                self.salt, self.encryption_key = salt, key
                loaded = True
                return True

            try:
                blob = path.read_bytes()
            except OSError:
                print("Could not read the vault.")
                return False
            self.vault_digest = SHA256.new(blob).digest()

            for attempt in range(3):
                password = self.password("Vault password (leave empty to cancel): ")
                if password is None:
                    return False
                try:
                    config, key, salt, legacy = self.decrypt_vault(blob, password)
                except RuntimeError:
                    print("Not enough resources to unlock the vault.")
                    return False
                except (ValueError, TypeError, UnicodeError, json.JSONDecodeError):
                    print("Wrong password or damaged vault.")
                    continue

                self.config = config
                if legacy:
                    new_salt = get_random_bytes(SALT_SIZE)
                    try:
                        new_key = self.derive_v2_key(password, new_salt)
                    except RuntimeError:
                        self.wipe(key)
                        self.config.clear()
                        print("Not enough resources to migrate the legacy vault.")
                        return False
                    try:
                        self.save_config(key=new_key, salt=new_salt)
                    except (OSError, ValueError):
                        self.wipe(key)
                        self.wipe(new_key)
                        self.config.clear()
                        print("The legacy vault could not be securely migrated.")
                        return False
                    self.wipe(key)
                    key, salt = new_key, new_salt
                    print("Vault security upgraded to DBv2.")
                password = None
                self.salt, self.encryption_key = salt, key
                loaded = True
                return True

            print("Too many failed password attempts.")
            return False
        finally:
            if not loaded:
                self.close()

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
            if self.vault_digest is None:
                if path.exists():
                    raise OSError("Vault appeared after it was opened")
            else:
                try:
                    current_digest = SHA256.new(path.read_bytes()).digest()
                except OSError as error:
                    raise OSError("Vault changed or disappeared") from error
                if current_digest != self.vault_digest:
                    raise OSError("Vault was changed by another process")
            descriptor, temp_path = tempfile.mkstemp(
                dir=str(path.parent or Path.cwd()),
                prefix=f".{path.name}.",
                suffix=".tmp",
            )
            with os.fdopen(descriptor, "wb") as temporary:
                temporary.write(encrypted)
                temporary.flush()
                os.fsync(temporary.fileno())
            os.replace(temp_path, path)
            temp_path = None
            self.vault_digest = SHA256.new(encrypted).digest()
            if os.name == "posix":
                try:
                    directory = os.open(path.parent, os.O_RDONLY)
                    try:
                        os.fsync(directory)
                    finally:
                        os.close(directory)
                except OSError:
                    pass
        finally:
            self.wipe(plaintext)
            if temp_path:
                try:
                    os.unlink(temp_path)
                except FileNotFoundError:
                    pass

    def change_password(self):
        password = self.password(
            "New vault password (leave empty to cancel): ", confirm=True
        )
        if password is None:
            return
        salt = get_random_bytes(SALT_SIZE)
        try:
            key = self.derive_v2_key(password, salt)
        except RuntimeError:
            print("Not enough resources to change the vault password.")
            return
        password = None
        try:
            self.save_config(key=key, salt=salt)
        except (OSError, ValueError):
            self.wipe(key)
            print("Could not change the vault password.")
            return
        self.wipe(self.encryption_key)
        self.salt, self.encryption_key = salt, key
        print("Vault password changed.")

    @staticmethod
    def parse_activation_url(activation_url):
        if not activation_url or any(
            character.isspace() for character in activation_url
        ):
            raise ValueError("expected one HTTPS activation URL")
        try:
            parsed = urllib.parse.urlsplit(activation_url)
            host = parsed.hostname.lower() if parsed.hostname else ""
            port = parsed.port
        except (AttributeError, ValueError) as error:
            raise ValueError("malformed activation URL") from error
        if (
            parsed.scheme.lower() != "https"
            or parsed.username is not None
            or parsed.password is not None
            or port is not None
            or parsed.query
            or parsed.fragment
        ):
            raise ValueError("invalid activation URL")
        host_match = re.fullmatch(r"m-([0-9a-f]{8})\.duosecurity\.com", host)
        path_match = re.fullmatch(r"/activate/([A-Za-z0-9_-]{20})", parsed.path)
        if not host_match or not path_match:
            raise ValueError("invalid Duo activation URL")
        return path_match.group(1), f"api-{host_match.group(1)}.duosecurity.com"

    def parse_qr_code(self, file_path):
        try:
            with Image.open(file_path) as image:
                decoded = pyzbar_decode(image)
            if len(decoded) != 1:
                raise ValueError("the image must contain exactly one QR code")
            url = decoded[0].data.decode("utf-8").strip()
            self.parse_activation_url(url)
            return url
        except (
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
            )
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
        method = self.menu("Add key", "Activation URL (m-HOST.duosecurity.com/activate/PATH)", "Activation code and host", "QR code image")
        if method is None:
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
                match = re.fullmatch(r"https://m-([0-9a-fA-F]+)\.duosecurity\.com/activate/([A-Za-z0-9_-]+)", url)
                if match is None:
                    print("Invalid Duo activation URL")
                    continue
                host, code = f"api-{match.group(1)}.duosecurity.com", match.group(2)
            elif method == 2:
                code = self.ask("Activation code (leave empty to cancel): ")
                if not code:
                    return
                host = self.ask("API host (leave empty to cancel): ")
                if not host:
                    return
                host = host.lower().removeprefix("https://").rstrip("/")
                if not re.fullmatch(r"[A-Za-z0-9_-]{20}", code) or not re.fullmatch(
                    r"api-[0-9a-f]{8}\.duosecurity\.com", host
                ):
                    print("Invalid Duo activation code or API host. Try again.")
                    continue
            elif method == 3:
                file_path = self.ask("QR image path (leave empty to cancel): ")
                if not file_path:
                    return
                url = self.parse_qr_code(file_path.strip('"'))
                if not url:
                    continue
                code, host = self.parse_activation_url(url)
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
                    "Save failed. This activation may be one-use; leaving now "
                    "permanently discards it."
                )
                retry = self.ask("Retry saving? [Y/n]: ")
                if retry is None or retry.lower() == "n":
                    self.config["keys"].pop(name, None)
                    print("The activated key was not saved.")
                    return

    def duo_request(self, key_config, method, path, data):
        private_key = RSA.import_key(key_config["privkey"].encode("ascii"))
        duo_date = email.utils.format_datetime(
            datetime.datetime.now(datetime.timezone.utc)
        )
        message = "\n".join(
            (
                duo_date,
                method,
                key_config["host"].lower(),
                path,
                urllib.parse.urlencode(data),
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
        )
        response.raise_for_status()
        result = response.json()
        if not isinstance(result, dict):
            raise ValueError("Invalid Duo response")
        return result

    @classmethod
    def prompt_step_up_code(cls, step_up_code_info):
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
        while True:
            code = cls.ask(
                f"Enter the {digits}-digit verification code (blank to stop): "
            )
            if not code:
                return None
            if len(code) == digits and code.isascii() and code.isdecimal():
                return code
            print(f"Enter exactly {digits} ASCII digits.")

    def push_loop(self, key_name):
        key = self.config["keys"][key_name]
        response = key.get("response") if isinstance(key, dict) else None
        valid_host = (
            isinstance(key, dict)
            and isinstance(key.get("host"), str)
            and re.fullmatch(r"api-[0-9a-f]{8}\.duosecurity\.com", key["host"].lower())
        )
        if (
            not valid_host
            or not isinstance(key.get("privkey"), str)
            or not isinstance(response, dict)
            or not isinstance(response.get("akey"), str)
            or not isinstance(response.get("pkey"), str)
            or not re.fullmatch(r"[A-Za-z0-9._~-]{1,512}", response["akey"])
            or not re.fullmatch(r"[A-Za-z0-9._~-]{1,512}", response["pkey"])
        ):
            print("This key has invalid Duo Mobile Push data.")
            return
        try:
            RSA.import_key(key["privkey"].encode("ascii"))
        except (ValueError, TypeError, IndexError, UnicodeError):
            print("This key has an invalid Duo Mobile Push signing key.")
            return
        handled = set()
        print("\nChecking continuously. Press Ctrl+C to return to the key menu.")
        try:
            while True:
                try:
                    common = {
                        "akey": key["response"]["akey"],
                        "fips_status": "1",
                        "hsm_status": "true",
                        "pkpush": "rsa-sha512",
                    }
                    result = self.duo_request(
                        key, "GET", "/push/v2/device/transactions", common
                    )
                    response = result.get("response")
                    transactions = (
                        response.get("transactions")
                        if isinstance(response, dict)
                        else None
                    )
                    if not isinstance(transactions, list):
                        raise ValueError("Invalid transaction list")
                    handled.intersection_update(
                        transaction.get("urgid")
                        for transaction in transactions
                        if isinstance(transaction, dict)
                    )

                    for transaction in transactions:
                        if (
                            not isinstance(transaction, dict)
                            or not isinstance(transaction.get("urgid"), str)
                            or not re.fullmatch(
                                r"[A-Za-z0-9_-]{1,128}", transaction["urgid"]
                            )
                        ):
                            print("Skipped a malformed Duo transaction.")
                            continue
                        if transaction["urgid"] in handled:
                            continue
                        expiration = transaction.get("expiration")
                        if (
                            isinstance(expiration, (int, float))
                            and not isinstance(expiration, bool)
                            and time.time() >= expiration
                        ):
                            print("Skipped an expired Duo transaction.")
                            handled.add(transaction["urgid"])
                            continue

                        info = transaction.get("step_up_code_info")
                        push_name = (
                            "Verified Duo Push"
                            if info is not None
                            else "Duo Mobile Push"
                        )
                        summary = (
                            transaction.get("summary")
                            or transaction.get("type")
                            or "Sign-in"
                        )
                        print(f"\n{push_name}: {summary}")
                        while True:
                            if (
                                isinstance(expiration, (int, float))
                                and not isinstance(expiration, bool)
                                and time.time() >= expiration
                            ):
                                print(f"{push_name} expired.")
                                break
                            code = None
                            if info is not None:
                                try:
                                    code = self.prompt_step_up_code(info)
                                except ValueError as error:
                                    print(f"Cannot process {push_name}: {error}.")
                                    handled.add(transaction["urgid"])
                                    break
                                if code is None:
                                    return
                            else:
                                while True:
                                    action = self.ask(
                                        "[y] Approve, [s] skip, [q] back: "
                                    )
                                    action = action.lower() if action else action
                                    if action in (None, "q"):
                                        return
                                    if action == "y":
                                        break
                                    if action in ("", "s", "n"):
                                        handled.add(transaction["urgid"])
                                        print("Duo Mobile Push skipped.")
                                        break
                                    print("Enter y, s, or q.")
                                if transaction["urgid"] in handled:
                                    break
                            reply_data = {
                                "akey": common["akey"],
                                "answer": "approve",
                                "fips_status": "1",
                                "hsm_status": "true",
                                "pkpush": "rsa-sha512",
                            }
                            if code is not None:
                                reply_data.update(
                                    step_up_code=code,
                                    step_up_code_autofilled="false",
                                )
                            reply = self.duo_request(
                                key,
                                "POST",
                                "/push/v2/device/transactions/" + transaction["urgid"],
                                reply_data,
                            )
                            if reply.get("stat") == "OK":
                                print(f"{push_name} approved.")
                                handled.add(transaction["urgid"])
                                break
                            if info is not None and str(reply.get("code")) == "40032":
                                print("Incorrect verification code.")
                                continue
                            message = reply.get("message")
                            print(
                                f"{push_name} rejected"
                                + (f": {message}" if message else ".")
                            )
                            handled.add(transaction["urgid"])
                            break
                except (
                    requests.RequestException,
                    ValueError,
                    KeyError,
                    TypeError,
                    UnicodeError,
                ):
                    print("Duo Mobile Push / Verified Duo Push check failed; retrying.")
                time.sleep(POLL_SECONDS)
        except (KeyboardInterrupt, EOFError):
            print("\nStopped checking for Duo Mobile Push / Verified Duo Push.")

    def generate_passcode(self, key_name):
        key = self.config["keys"][key_name]
        if not isinstance(key, dict):
            print("This key has invalid Duo Mobile Passcode data.")
            return
        response = key.get("response")
        counter = key.get("hotp_counter", 0)
        history = key.get("hotp_log", [])
        if (
            not isinstance(response, dict)
            or not isinstance(counter, int)
            or isinstance(counter, bool)
            or not 0 <= counter < 2**64 - 1
            or not isinstance(history, list)
        ):
            print("This key has invalid Duo Mobile Passcode data.")
            return
        try:
            raw_secret = response["hotp_secret"]
            if not isinstance(raw_secret, str):
                raise TypeError
            secret = base64.b32encode(raw_secret.encode("ascii")).decode("ascii")
            next_counter = counter + 1
            code = pyotp.HOTP(secret).at(next_counter)
        except (KeyError, TypeError, UnicodeError, ValueError):
            print("This key does not support Duo Mobile Passcodes.")
            return

        had_counter, had_history = "hotp_counter" in key, "hotp_log" in key
        old_counter, old_history = key.get("hotp_counter"), key.get("hotp_log")
        key["hotp_counter"] = next_counter
        if not had_history:
            key["hotp_log"] = history
        history.append(
            f"{datetime.datetime.now(datetime.timezone.utc):%Y-%m-%d %H:%M:%S} "
            f"({key_name}): {code}"
        )
        try:
            self.save_config()
        except (OSError, ValueError):
            if had_counter:
                key["hotp_counter"] = old_counter
            else:
                key.pop("hotp_counter", None)
            if had_history:
                history.pop()
            else:
                key.pop("hotp_log", None)
            print("Passcode was not generated because the vault could not be saved.")
            return
        print(f"Duo Mobile Passcode: {code}")

    def passcode_history(self, key_name):
        key = self.config["keys"][key_name]
        if not isinstance(key, dict):
            print("This key has invalid passcode history.")
            return
        history = key.get("hotp_log", [])
        if not isinstance(history, list):
            print("This key has invalid passcode history.")
            return
        if not history:
            print("No Duo Mobile Passcode history.")
            return
        while True:
            print(f"\nNewest 10 of {len(history)} saved Duo Mobile Passcodes:")
            for entry in history[-10:]:
                print(entry)
            choice = self.menu(
                "History actions", "Delete older history (keep newest 10)"
            )
            if choice == 0:
                return
            if choice == 1:
                if len(history) <= 10:
                    print("There is no older history to delete.")
                    continue
                confirm = self.ask(f"Delete {len(history) - 10} older entries? [y/N]: ")
                if confirm and confirm.lower() == "y":
                    old_history = history
                    history = history[-10:]
                    key["hotp_log"] = history
                    try:
                        self.save_config()
                        print("Older passcode history deleted.")
                    except (OSError, ValueError):
                        history = old_history
                        key["hotp_log"] = old_history
                        print("Could not save the history change.")

    def keys_menu(self):
        while True:
            names = list(self.config["keys"])
            if not names:
                print("No keys saved.")
                return
            labels = []
            for name in names:
                key = self.config["keys"][name]
                response = key.get("response") if isinstance(key, dict) else None
                organization = (
                    response.get("customer_name")
                    if isinstance(response, dict)
                    else None
                )
                labels.append(name + (f" ({organization})" if organization else ""))
            choice = self.menu("Keys", *labels)
            if choice == 0:
                return
            name = names[choice - 1]

            while name in self.config["keys"]:
                action = self.menu(
                    name,
                    "Duo Mobile Push / Verified Duo Push",
                    "Generate Duo Mobile Passcode",
                    "Duo Mobile Passcode history",
                    "Delete key",
                )
                if action == 0:
                    break
                if action == 1:
                    self.push_loop(name)
                elif action == 2:
                    self.generate_passcode(name)
                elif action == 3:
                    self.passcode_history(name)
                elif action == 4:
                    if self.ask(f"Delete '{name}'? [y/N]: ") not in ("y", "Y"):
                        continue
                    deleted = self.config["keys"].pop(name)
                    try:
                        self.save_config()
                        print(f"Key '{name}' deleted.")
                    except (OSError, ValueError):
                        self.config["keys"][name] = deleted
                        print("Could not save the deletion.")
                    break

    def main_menu(self):
        while True:
            choice = self.menu(
                "Main menu", "Keys", "Add key", "Change vault password", back="Exit"
            )
            if choice is None or choice == 0:
                return
            elif choice == 1:
                self.keys_menu()
            elif choice == 2:
                self.add_key()
            elif choice == 3:
                self.change_password()

    def close(self):
        lock_file, self.lock_file = self.lock_file, None
        if lock_file:
            try:
                lock_file.seek(0)
                if os.name == "nt":
                    msvcrt.locking(lock_file.fileno(), msvcrt.LK_UNLCK, 1)
                else:
                    fcntl.flock(lock_file.fileno(), fcntl.LOCK_UN)
            except (OSError, ValueError):
                pass
            try:
                lock_file.close()
            except OSError:
                pass
        self.wipe(self.encryption_key)
        self.encryption_key = None
        self.salt = None
        self.vault_digest = None
        self.config.clear()


if __name__ == "__main__":
    app = DuoAuthenticator()
    try:
        if (app.config_file or app.select_vault()) and app.load_config():
            app.main_menu()
    except (KeyboardInterrupt, EOFError):
        print("\nExited safely.")
    finally:
        app.close()