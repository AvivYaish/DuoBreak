import io
import json
from pathlib import Path
import tempfile
import unittest
from types import SimpleNamespace
from unittest.mock import MagicMock, patch

from Crypto.Cipher import AES
from Crypto.Hash import SHA256, SHA512
from Crypto.Protocol.KDF import PBKDF2
from Crypto.Util.Padding import pad
import requests

from duobreak import DB_V1, DB_V2, DuoAuthenticator


PASSWORD = "correct horse battery staple"
NEW_PASSWORD = "new correct horse battery staple"
ACTIVATION_TOKEN = "A1b2C3d4E5f6G7h8I9j0"
ACTIVATION_URL = f"https://m-deadbeef.duosecurity.com/activate/{ACTIVATION_TOKEN}"


def sample_config():
    return {
        "keys": {
            "Cisco Duo": {
                "code": ACTIVATION_TOKEN,
                "host": "api-deadbeef.duosecurity.com",
                "response": {
                    "akey": "test-akey",
                    "pkey": "test-pkey",
                    "hotp_secret": "test-secret",
                    "customer_name": "Test Organization",
                    "unknown_response_field": {"keep": True},
                },
                "pubkey": "PUBLIC KEY",
                "privkey": "PRIVATE KEY",
                "hotp_counter": 2,
                "hotp_log": ["first", "second"],
                "unknown_key_field": [1, 2, 3],
            }
        },
        "unknown_top_level_field": "preserve me",
    }


def legacy_vault(config, password=PASSWORD):
    salt, iv = b"s" * 16, b"i" * 16
    key = PBKDF2(
        password.encode("utf-8"),
        salt,
        32,
        count=100000,
        hmac_hash_module=SHA256,
    )
    plaintext = json.dumps(config, ensure_ascii=False).encode("utf-8")
    ciphertext = AES.new(key, AES.MODE_CBC, iv).encrypt(pad(plaintext, AES.block_size))
    return DB_V1 + salt + iv + ciphertext


@patch("duobreak.SCRYPT_N", 2**12)
class DuoVaultTests(unittest.TestCase):
    def setUp(self):
        self.temp_dir = tempfile.TemporaryDirectory()
        self.path = Path(self.temp_dir.name) / "vault.duo"

    def tearDown(self):
        self.temp_dir.cleanup()

    def make_v2_vault(self, config=None, password=PASSWORD):
        authenticator = DuoAuthenticator(self.path)
        authenticator.config = config or sample_config()
        authenticator.salt = b"v" * 16
        authenticator.encryption_key = authenticator.derive_v2_key(
            password, authenticator.salt
        )
        authenticator.save_config()
        return authenticator

    def decrypt(self, authenticator, password=PASSWORD):
        config, key, _salt, _legacy = authenticator.decrypt_vault(
            self.path.read_bytes(), password
        )
        authenticator.wipe(key)
        return config

    def test_dbv2_round_trip_preserves_json_and_hides_plaintext(self):
        expected = sample_config()
        authenticator = self.make_v2_vault(expected)
        blob = self.path.read_bytes()

        self.assertTrue(blob.startswith(DB_V2))
        self.assertNotIn(b"Cisco Duo", blob)
        self.assertNotIn(b"test-secret", blob)
        self.assertEqual(self.decrypt(authenticator), expected)
        authenticator.close()

    def test_each_save_uses_fresh_encryption(self):
        authenticator = self.make_v2_vault()
        first = self.path.read_bytes()
        authenticator.save_config()
        second = self.path.read_bytes()

        self.assertNotEqual(first, second)
        self.assertEqual(self.decrypt(authenticator), sample_config())
        authenticator.close()

    def test_wrong_password_and_tampering_are_rejected(self):
        authenticator = self.make_v2_vault()
        original = self.path.read_bytes()

        with self.assertRaises(ValueError):
            authenticator.decrypt_vault(original, "wrong password")

        for offset in (4, 20, 36, len(original) - 1):
            damaged = bytearray(original)
            damaged[offset] ^= 1
            with self.subTest(offset=offset):
                with self.assertRaises(ValueError):
                    authenticator.decrypt_vault(bytes(damaged), PASSWORD)
        authenticator.close()

    def test_legacy_dbv1_is_loaded_and_migrated_without_json_changes(self):
        expected = sample_config()
        self.path.write_bytes(legacy_vault(expected))
        authenticator = DuoAuthenticator(self.path)

        with patch.object(authenticator, "password", return_value=PASSWORD):
            with patch("sys.stdout", new_callable=io.StringIO):
                self.assertTrue(authenticator.load_config())

        self.assertEqual(authenticator.config, expected)
        self.assertTrue(self.path.read_bytes().startswith(DB_V2))
        authenticator.close()

        reopened = DuoAuthenticator(self.path)
        with patch.object(reopened, "password", return_value=PASSWORD):
            self.assertTrue(reopened.load_config())
        self.assertEqual(reopened.config, expected)
        reopened.close()

    def test_legacy_empty_object_gets_the_historical_keys_default(self):
        self.path.write_bytes(legacy_vault({}))
        authenticator = DuoAuthenticator(self.path)
        with patch.object(authenticator, "password", return_value=PASSWORD):
            with patch("sys.stdout", new_callable=io.StringIO):
                self.assertTrue(authenticator.load_config())
        self.assertEqual(authenticator.config, {"keys": {}})
        authenticator.close()

    def test_vault_lock_prevents_a_simultaneous_second_instance(self):
        creator = self.make_v2_vault()
        creator.close()
        first = DuoAuthenticator(self.path)
        with patch.object(first, "password", return_value=PASSWORD):
            self.assertTrue(first.load_config())

        second = DuoAuthenticator(self.path)
        with patch.object(second, "password", return_value=PASSWORD) as password:
            with patch("sys.stdout", new_callable=io.StringIO) as output:
                self.assertFalse(second.load_config())
        password.assert_not_called()
        self.assertIn("already open", output.getvalue())

        first.config["first-change"] = True
        first.save_config()
        first.close()
        second.close()

        reopened = DuoAuthenticator(self.path)
        with patch.object(reopened, "password", return_value=PASSWORD):
            self.assertTrue(reopened.load_config())
        self.assertIn("first-change", reopened.config)
        reopened.close()

    def test_external_vault_change_is_detected_while_locked(self):
        authenticator = self.make_v2_vault()
        self.path.write_bytes(self.path.read_bytes() + b"external change")
        authenticator.config["must-not-save"] = True
        with self.assertRaises(OSError):
            authenticator.save_config()
        authenticator.close()

    def test_truncated_or_unknown_vault_never_populates_config(self):
        for blob in (b"", b"DBv2", b"NOPE" + b"x" * 64):
            with self.subTest(blob=blob[:4]):
                self.path.write_bytes(blob)
                authenticator = DuoAuthenticator(self.path)
                with patch.object(
                    authenticator, "password", side_effect=[PASSWORD] * 3
                ):
                    with patch("sys.stdout", new_callable=io.StringIO):
                        self.assertFalse(authenticator.load_config())
                self.assertEqual(authenticator.config, {})

    def test_kdf_resource_failure_is_handled_without_creating_a_file(self):
        authenticator = DuoAuthenticator(self.path)
        with patch.object(authenticator, "password", return_value=PASSWORD):
            with patch.object(
                authenticator,
                "derive_v2_key",
                side_effect=RuntimeError("synthetic resource failure"),
            ):
                with patch("sys.stdout", new_callable=io.StringIO):
                    self.assertFalse(authenticator.load_config())
        self.assertFalse(self.path.exists())
        self.assertEqual(authenticator.config, {})

    def test_password_change_reencrypts_with_only_the_new_password(self):
        authenticator = self.make_v2_vault()
        with patch.object(authenticator, "password", return_value=NEW_PASSWORD):
            with patch("sys.stdout", new_callable=io.StringIO):
                authenticator.change_password()
        blob = self.path.read_bytes()

        with self.assertRaises(ValueError):
            authenticator.decrypt_vault(blob, PASSWORD)
        config, key, _salt, _legacy = authenticator.decrypt_vault(blob, NEW_PASSWORD)
        authenticator.wipe(key)
        self.assertEqual(config, sample_config())
        authenticator.close()

    def test_atomic_write_failure_keeps_original_and_removes_temp_file(self):
        authenticator = self.make_v2_vault()
        original = self.path.read_bytes()
        authenticator.config["new-secret"] = "must remain encrypted"
        written_temp = []

        def fail_replace(source, _destination):
            written_temp.append(Path(source).read_bytes())
            raise OSError("synthetic replace failure")

        with patch("duobreak.os.replace", side_effect=fail_replace):
            with self.assertRaises(OSError):
                authenticator.save_config()

        self.assertEqual(self.path.read_bytes(), original)
        self.assertNotIn(b"must remain encrypted", written_temp[0])
        self.assertEqual(list(self.path.parent.glob(".vault.duo.*.tmp")), [])
        authenticator.close()


class DuoActivationUrlTests(unittest.TestCase):
    def test_parses_duo_activation_url(self):
        code, host = DuoAuthenticator.parse_activation_url(ACTIVATION_URL)
        self.assertEqual(code, ACTIVATION_TOKEN)
        self.assertEqual(host, "api-deadbeef.duosecurity.com")

    def test_rejects_untrusted_or_malformed_urls(self):
        invalid_urls = (
            "http://m-deadbeef.duosecurity.com/activate/" + ACTIVATION_TOKEN,
            "https://m-deadbeef.duosecurity.com.evil.test/activate/" + ACTIVATION_TOKEN,
            "https://user@m-deadbeef.duosecurity.com/activate/" + ACTIVATION_TOKEN,
            "https://m-deadbeef.duosecurity.com:443/activate/" + ACTIVATION_TOKEN,
            ACTIVATION_URL + "?x=1",
            "https://m-deadbeef.duosecurity.com/activate/too-short",
        )
        for url in invalid_urls:
            with self.subTest(url=url):
                with self.assertRaises(ValueError):
                    DuoAuthenticator.parse_activation_url(url)

    @patch("duobreak.pyzbar_decode")
    @patch("duobreak.Image.open")
    def test_qr_reader_returns_the_activation_url(self, image_open, qr_decode):
        image_open.return_value.__enter__.return_value = MagicMock()
        qr_decode.return_value = [SimpleNamespace(data=ACTIVATION_URL.encode())]
        authenticator = DuoAuthenticator()
        self.assertEqual(authenticator.parse_qr_code("synthetic.png"), ACTIVATION_URL)

    @patch("duobreak.pyzbar_decode", return_value=[])
    @patch("duobreak.Image.open")
    def test_qr_reader_handles_missing_code(self, image_open, _qr_decode):
        image_open.return_value.__enter__.return_value = MagicMock()
        with patch("sys.stdout", new_callable=io.StringIO):
            self.assertIsNone(DuoAuthenticator().parse_qr_code("synthetic.png"))


class DuoActivationRequestTests(unittest.TestCase):
    @patch("duobreak.requests.post")
    @patch("duobreak.RSA.generate")
    def test_activation_uses_requested_device_metadata(self, rsa_generate, post):
        key_pair = MagicMock()
        key_pair.publickey.return_value.export_key.return_value = b"PUBLIC KEY"
        key_pair.export_key.return_value = b"PRIVATE KEY"
        rsa_generate.return_value = key_pair
        post.return_value.json.return_value = {"response": {"akey": "test"}}

        result = DuoAuthenticator().activate(
            ACTIVATION_TOKEN, "api-deadbeef.duosecurity.com"
        )

        self.assertIsNotNone(result)
        call = post.call_args
        self.assertEqual(
            call.args[0],
            "https://api-deadbeef.duosecurity.com/push/v2/activation/"
            + ACTIVATION_TOKEN,
        )
        self.assertEqual(
            call.kwargs["headers"]["User-Agent"],
            "DuoMobileApp/4.117.1 (arm64; iOS 26.6); Client: Foundation",
        )
        self.assertEqual(call.kwargs["data"]["app_version"], "4.117.1")
        self.assertEqual(call.kwargs["data"]["version"], "26.6")
        self.assertEqual(call.kwargs["data"]["build_version"], "23G71")
        self.assertEqual(call.kwargs["data"]["device_name"], "iPhone")
        self.assertEqual(call.kwargs["timeout"], (5, 30))
        post.return_value.raise_for_status.assert_called_once()

    @patch("duobreak.requests.post", side_effect=requests.Timeout)
    @patch("duobreak.RSA.generate")
    def test_activation_error_returns_to_the_menu(self, rsa_generate, _post):
        key_pair = MagicMock()
        key_pair.publickey.return_value.export_key.return_value = b"PUBLIC KEY"
        key_pair.export_key.return_value = b"PRIVATE KEY"
        rsa_generate.return_value = key_pair
        with patch("sys.stdout", new_callable=io.StringIO):
            result = DuoAuthenticator().activate(
                ACTIVATION_TOKEN, "api-deadbeef.duosecurity.com"
            )
        self.assertIsNone(result)

    @patch("duobreak.requests.post")
    @patch("duobreak.RSA.generate")
    def test_non_object_activation_response_is_handled(self, rsa_generate, post):
        key_pair = MagicMock()
        key_pair.publickey.return_value.export_key.return_value = b"PUBLIC KEY"
        key_pair.export_key.return_value = b"PRIVATE KEY"
        rsa_generate.return_value = key_pair
        post.return_value.json.return_value = []
        with patch("sys.stdout", new_callable=io.StringIO):
            result = DuoAuthenticator().activate(
                ACTIVATION_TOKEN, "api-deadbeef.duosecurity.com"
            )
        self.assertIsNone(result)


class DuoApiRequestTests(unittest.TestCase):
    def setUp(self):
        self.authenticator = DuoAuthenticator()
        self.key = {
            "host": "api-deadbeef.duosecurity.com",
            "privkey": "PRIVATE KEY",
            "response": {"akey": "test-akey", "pkey": "test-pkey"},
        }

    def call_request(self, method, path, data):
        with patch("duobreak.RSA.import_key") as import_key:
            with patch("duobreak.pkcs1_15.new") as signer:
                with patch("duobreak.requests.request") as request:
                    signer.return_value.sign.return_value = b"signature"
                    request.return_value.json.return_value = {"stat": "OK"}
                    result = self.authenticator.duo_request(
                        self.key, method, path, data
                    )
                    return result, import_key, signer, request

    def test_post_body_matches_the_signed_verified_push_data(self):
        path = "/push/v2/device/transactions/test-urgid"
        data = {
            "akey": "test-akey",
            "answer": "approve",
            "fips_status": "1",
            "hsm_status": "true",
            "pkpush": "rsa-sha512",
            "step_up_code": "074",
            "step_up_code_autofilled": "false",
        }
        result, _import_key, signer, request = self.call_request("POST", path, data)

        self.assertEqual(result, {"stat": "OK"})
        call = request.call_args
        self.assertEqual(call.kwargs["data"], data)
        self.assertIsNone(call.kwargs["params"])
        self.assertEqual(call.kwargs["headers"]["txId"], "test-urgid")
        duo_date = call.kwargs["headers"]["x-duo-date"]
        expected = "\n".join(
            (
                duo_date,
                "POST",
                self.key["host"],
                path,
                "akey=test-akey&answer=approve&fips_status=1&hsm_status=true&"
                "pkpush=rsa-sha512&step_up_code=074&step_up_code_autofilled=false",
            )
        ).encode("ascii")
        signed_hash = signer.return_value.sign.call_args.args[0]
        self.assertEqual(signed_hash.digest(), SHA512.new(expected).digest())
        request.return_value.raise_for_status.assert_called_once()

    def test_get_uses_query_parameters_and_no_transaction_header(self):
        data = {"akey": "test-akey"}
        _result, _import_key, _signer, request = self.call_request(
            "GET", "/push/v2/device/transactions", data
        )
        call = request.call_args
        self.assertEqual(call.kwargs["params"], data)
        self.assertIsNone(call.kwargs["data"])
        self.assertNotIn("txId", call.kwargs["headers"])


class DuoPushTests(unittest.TestCase):
    def setUp(self):
        self.key = {
            "host": "api-deadbeef.duosecurity.com",
            "privkey": "PRIVATE KEY",
            "response": {"akey": "test-akey", "pkey": "test-pkey"},
        }
        self.authenticator = DuoAuthenticator()
        self.authenticator.config = {"keys": {"Cisco Duo": self.key}}
        self.authenticator.duo_request = MagicMock()
        self.import_key_patcher = patch(
            "duobreak.RSA.import_key", return_value=MagicMock()
        )
        self.import_key = self.import_key_patcher.start()
        self.addCleanup(self.import_key_patcher.stop)

    @staticmethod
    def transactions(*items):
        return {"response": {"transactions": list(items)}}

    @patch("duobreak.time.sleep")
    def test_normal_push_missing_or_null_flag_confirms_without_code(self, _sleep):
        first = {"urgid": "normal-1", "summary": "First"}
        second = {
            "urgid": "normal-2",
            "summary": "Second",
            "step_up_code_info": None,
        }
        self.authenticator.duo_request.side_effect = [
            self.transactions(first, second),
            {"stat": "OK"},
            {"stat": "OK"},
            KeyboardInterrupt(),
        ]

        with patch("builtins.input", side_effect=["y", "y"]) as user_input:
            with patch("sys.stdout", new_callable=io.StringIO) as output:
                self.authenticator.push_loop("Cisco Duo")

        self.assertEqual(user_input.call_count, 2)
        calls = self.authenticator.duo_request.call_args_list
        self.assertEqual(len(calls), 4)
        for call in calls[1:3]:
            sent = call.args[3]
            self.assertNotIn("step_up_code", sent)
            self.assertNotIn("step_up_code_autofilled", sent)
        self.assertEqual(output.getvalue().count("Duo Mobile Push approved"), 2)

    @patch("duobreak.time.sleep")
    def test_verified_push_prompts_retries_and_preserves_leading_zero(self, _sleep):
        transaction = {
            "urgid": "verified",
            "summary": "Admin Panel",
            "step_up_code_info": {"num_digits": 3},
        }
        self.authenticator.duo_request.side_effect = [
            self.transactions(transaction),
            {"stat": "FAIL", "code": 40032},
            {"stat": "OK"},
            KeyboardInterrupt(),
        ]

        with patch("builtins.input", side_effect=["111", "074"]):
            with patch("sys.stdout", new_callable=io.StringIO) as output:
                self.authenticator.push_loop("Cisco Duo")

        calls = self.authenticator.duo_request.call_args_list
        self.assertEqual(calls[1].args[3]["step_up_code"], "111")
        self.assertEqual(calls[2].args[3]["step_up_code"], "074")
        self.assertEqual(calls[2].args[3]["step_up_code_autofilled"], "false")
        self.assertIn("Verified Duo Push approved", output.getvalue())

    @patch("duobreak.time.sleep")
    def test_idle_and_network_failures_keep_polling_until_cancelled(self, sleep):
        self.authenticator.duo_request.side_effect = [
            self.transactions(),
            requests.Timeout(),
            self.transactions(),
            KeyboardInterrupt(),
        ]

        with patch("sys.stdout", new_callable=io.StringIO) as output:
            self.authenticator.push_loop("Cisco Duo")

        self.assertEqual(self.authenticator.duo_request.call_count, 4)
        self.assertEqual(sleep.call_count, 3)
        self.assertIn("retrying", output.getvalue())
        self.assertIn("Stopped checking", output.getvalue())

    @patch("duobreak.time.sleep")
    def test_null_transaction_response_retries_without_crashing(self, _sleep):
        self.authenticator.duo_request.side_effect = [
            {"response": None},
            KeyboardInterrupt(),
        ]
        with patch("sys.stdout", new_callable=io.StringIO) as output:
            self.authenticator.push_loop("Cisco Duo")
        self.assertEqual(self.authenticator.duo_request.call_count, 2)
        self.assertIn("retrying", output.getvalue())

    @patch("duobreak.time.sleep")
    def test_malformed_verified_metadata_is_never_downgraded(self, _sleep):
        transaction = {
            "urgid": "verified",
            "step_up_code_info": {"num_digits": True},
        }
        self.authenticator.duo_request.side_effect = [
            self.transactions(transaction),
            KeyboardInterrupt(),
        ]

        with patch("builtins.input") as user_input:
            with patch("sys.stdout", new_callable=io.StringIO) as output:
                self.authenticator.push_loop("Cisco Duo")

        user_input.assert_not_called()
        self.assertEqual(self.authenticator.duo_request.call_count, 2)
        self.assertIn("Cannot process Verified Duo Push", output.getvalue())

    def test_blank_verified_code_leaves_without_replying(self):
        transaction = {
            "urgid": "verified",
            "step_up_code_info": {"num_digits": 3},
        }
        self.authenticator.duo_request.return_value = self.transactions(transaction)

        with patch("builtins.input", return_value=""):
            with patch("sys.stdout", new_callable=io.StringIO):
                self.authenticator.push_loop("Cisco Duo")

        self.authenticator.duo_request.assert_called_once()

    @patch("duobreak.time.sleep")
    def test_skipped_normal_push_is_not_replied_to(self, _sleep):
        self.authenticator.duo_request.side_effect = [
            self.transactions({"urgid": "normal"}),
            KeyboardInterrupt(),
        ]
        with patch("builtins.input", return_value="s"):
            with patch("sys.stdout", new_callable=io.StringIO):
                self.authenticator.push_loop("Cisco Duo")
        self.assertEqual(self.authenticator.duo_request.call_count, 2)
        self.assertTrue(
            all(
                call.args[1] == "GET"
                for call in self.authenticator.duo_request.call_args_list
            )
        )

    @patch("duobreak.time.sleep")
    def test_skip_one_normal_push_then_approve_the_next(self, _sleep):
        self.authenticator.duo_request.side_effect = [
            self.transactions(
                {"urgid": "skip-this", "summary": "First"},
                {"urgid": "approve-this", "summary": "Second"},
            ),
            {"stat": "OK"},
            KeyboardInterrupt(),
        ]
        with patch("builtins.input", side_effect=["s", "y"]):
            with patch("sys.stdout", new_callable=io.StringIO) as output:
                self.authenticator.push_loop("Cisco Duo")

        calls = self.authenticator.duo_request.call_args_list
        self.assertEqual(len(calls), 3)
        self.assertEqual(calls[1].args[1], "POST")
        self.assertTrue(calls[1].args[2].endswith("/approve-this"))
        self.assertIn("Duo Mobile Push skipped", output.getvalue())
        self.assertIn("Duo Mobile Push approved", output.getvalue())

    @patch("duobreak.time.sleep")
    def test_skipped_pending_push_is_not_prompted_again(self, _sleep):
        transaction = {"urgid": "still-pending"}
        self.authenticator.duo_request.side_effect = [
            self.transactions(transaction),
            self.transactions(transaction),
            KeyboardInterrupt(),
        ]
        with patch("builtins.input", return_value="s") as user_input:
            with patch("sys.stdout", new_callable=io.StringIO):
                self.authenticator.push_loop("Cisco Duo")
        user_input.assert_called_once()

    def test_invalid_loaded_host_is_rejected_before_network_use(self):
        self.key["host"] = "api-deadbeef.duosecurity.com.evil.test"
        with patch("sys.stdout", new_callable=io.StringIO) as output:
            self.authenticator.push_loop("Cisco Duo")
        self.authenticator.duo_request.assert_not_called()
        self.assertIn("invalid Duo Mobile Push data", output.getvalue())

    def test_empty_or_non_ascii_push_credentials_are_rejected_locally(self):
        for field, value in (("akey", ""), ("pkey", "p-k\u00e9y")):
            with self.subTest(field=field):
                self.key["response"] = {
                    "akey": "test-akey",
                    "pkey": "test-pkey",
                    field: value,
                }
                with patch("sys.stdout", new_callable=io.StringIO):
                    self.authenticator.push_loop("Cisco Duo")
                self.authenticator.duo_request.assert_not_called()

    @patch("duobreak.time.sleep")
    def test_rejection_is_not_reported_as_approved(self, _sleep):
        transaction = {"urgid": "normal"}
        self.authenticator.duo_request.side_effect = [
            self.transactions(transaction),
            {"stat": "FAIL", "message": "Rejected"},
            KeyboardInterrupt(),
        ]

        with patch("builtins.input", return_value="y"):
            with patch("sys.stdout", new_callable=io.StringIO) as output:
                self.authenticator.push_loop("Cisco Duo")

        self.assertNotIn("approved", output.getvalue())
        self.assertIn("Duo Mobile Push rejected", output.getvalue())

    def test_step_up_prompt_accepts_only_declared_ascii_digits(self):
        with patch(
            "builtins.input",
            side_effect=["12", "abc", "\u0660\u0667\u0664", "074"],
        ):
            with patch("sys.stdout", new_callable=io.StringIO):
                code = self.authenticator.prompt_step_up_code({"num_digits": 3})
        self.assertEqual(code, "074")

    def test_step_up_prompt_enforces_supported_metadata_boundaries(self):
        for digits, value in ((3, "123"), (7, "1234567")):
            with self.subTest(digits=digits):
                with patch("builtins.input", return_value=value):
                    self.assertEqual(
                        self.authenticator.prompt_step_up_code({"num_digits": digits}),
                        value,
                    )
        for digits in (2, 8, True, "3"):
            with self.subTest(invalid=digits):
                with self.assertRaises(ValueError):
                    self.authenticator.prompt_step_up_code({"num_digits": digits})


class DuoPasscodeTests(unittest.TestCase):
    def setUp(self):
        self.key = {
            "response": {"hotp_secret": "test-secret"},
            "unknown": "preserve",
        }
        self.authenticator = DuoAuthenticator()
        self.authenticator.config = {"keys": {"Cisco Duo": self.key}}
        self.authenticator.save_config = MagicMock()

    def test_history_is_unlimited_and_existing_entries_are_preserved(self):
        self.key["hotp_counter"] = 1000
        self.key["hotp_log"] = [f"entry-{number}" for number in range(1000)]

        with patch("sys.stdout", new_callable=io.StringIO):
            self.authenticator.generate_passcode("Cisco Duo")

        self.assertEqual(self.key["hotp_counter"], 1001)
        self.assertEqual(len(self.key["hotp_log"]), 1001)
        self.assertEqual(self.key["hotp_log"][0], "entry-0")
        self.assertEqual(self.key["unknown"], "preserve")

    def test_save_failure_does_not_expose_or_reuse_a_passcode(self):
        self.key["hotp_counter"] = 7
        self.key["hotp_log"] = ["old"]
        self.authenticator.save_config.side_effect = OSError

        with patch("sys.stdout", new_callable=io.StringIO) as output:
            self.authenticator.generate_passcode("Cisco Duo")

        self.assertEqual(self.key["hotp_counter"], 7)
        self.assertEqual(self.key["hotp_log"], ["old"])
        self.assertNotIn("Duo Mobile Passcode:", output.getvalue())

    def test_trim_history_keeps_exactly_the_newest_ten(self):
        history = [f"entry-{number}" for number in range(15)]
        self.key.update(hotp_counter=15, hotp_log=history)

        with patch("builtins.input", side_effect=["1", "y", "0"]):
            with patch("sys.stdout", new_callable=io.StringIO):
                self.authenticator.passcode_history("Cisco Duo")

        self.assertEqual(self.key["hotp_log"], history[-10:])
        self.assertEqual(self.key["hotp_counter"], 15)
        self.assertEqual(self.key["unknown"], "preserve")
        self.authenticator.save_config.assert_called_once()

    def test_trim_save_failure_restores_the_complete_history(self):
        history = [f"entry-{number}" for number in range(15)]
        self.key["hotp_log"] = history.copy()
        self.authenticator.save_config.side_effect = OSError
        with patch("builtins.input", side_effect=["1", "y", "0"]):
            with patch("sys.stdout", new_callable=io.StringIO):
                self.authenticator.passcode_history("Cisco Duo")
        self.assertEqual(self.key["hotp_log"], history)

    def test_history_with_ten_entries_is_not_modified(self):
        history = [f"entry-{number}" for number in range(10)]
        self.key["hotp_log"] = history.copy()

        with patch("builtins.input", side_effect=["1", "0"]):
            with patch("sys.stdout", new_callable=io.StringIO):
                self.authenticator.passcode_history("Cisco Duo")

        self.assertEqual(self.key["hotp_log"], history)
        self.authenticator.save_config.assert_not_called()

    def test_malformed_passcode_state_returns_without_crashing(self):
        self.key["hotp_counter"] = True
        with patch("sys.stdout", new_callable=io.StringIO):
            self.authenticator.generate_passcode("Cisco Duo")
        self.authenticator.save_config.assert_not_called()

    def test_malformed_key_and_secret_types_return_without_crashing(self):
        self.authenticator.config["keys"]["Cisco Duo"] = []
        with patch("sys.stdout", new_callable=io.StringIO):
            self.authenticator.generate_passcode("Cisco Duo")
            self.authenticator.passcode_history("Cisco Duo")
        self.authenticator.config["keys"]["Cisco Duo"] = {
            "response": {"hotp_secret": 123}
        }
        with patch("sys.stdout", new_callable=io.StringIO):
            self.authenticator.generate_passcode("Cisco Duo")
        self.authenticator.save_config.assert_not_called()


class DuoProductionCryptoTests(unittest.TestCase):
    def test_production_scrypt_profile_is_supported(self):
        authenticator = DuoAuthenticator()
        key = authenticator.derive_v2_key(PASSWORD, b"p" * 16)
        self.assertEqual(len(key), 64)
        authenticator.wipe(key)
        self.assertEqual(key, b"\0" * 64)


class DuoMenuTests(unittest.TestCase):
    def setUp(self):
        self.authenticator = DuoAuthenticator()
        self.authenticator.config = {"keys": {}}
        self.authenticator.save_config = MagicMock()

    def test_main_menu_has_only_the_compact_top_level_actions(self):
        self.authenticator.add_key = MagicMock()
        self.authenticator.keys_menu = MagicMock()
        self.authenticator.change_password = MagicMock()

        with patch("builtins.input", side_effect=["1", "2", "3", "0"]) as user_input:
            with patch("sys.stdout", new_callable=io.StringIO) as output:
                self.authenticator.main_menu()

        self.authenticator.add_key.assert_called_once()
        self.authenticator.keys_menu.assert_called_once()
        self.authenticator.change_password.assert_called_once()
        menu = output.getvalue() + "".join(
            call.args[0] for call in user_input.call_args_list
        )
        self.assertIn("1. Add key", menu)
        self.assertIn("2. Keys", menu)
        self.assertNotIn("Delete key\n4. List", menu)

    def test_extremely_long_menu_input_is_rejected_without_crashing(self):
        with patch("builtins.input", side_effect=["9" * 10_000, "0"]):
            with patch("sys.stdout", new_callable=io.StringIO) as output:
                self.assertIsNone(self.authenticator.menu("Test", "Choice"))
        self.assertIn("Invalid selection", output.getvalue())

    def test_add_key_asks_for_one_activation_method(self):
        activation = ({"akey": "a"}, "PUBLIC", "PRIVATE")
        self.authenticator.activate = MagicMock(return_value=activation)

        with patch(
            "builtins.input",
            side_effect=[
                "2",
                "Cisco Duo",
                ACTIVATION_TOKEN,
                "api-deadbeef.duosecurity.com",
            ],
        ):
            with patch("sys.stdout", new_callable=io.StringIO):
                self.authenticator.add_key()

        self.assertIn("Cisco Duo", self.authenticator.config["keys"])
        self.authenticator.activate.assert_called_once_with(
            ACTIVATION_TOKEN, "api-deadbeef.duosecurity.com"
        )
        self.authenticator.save_config.assert_called_once()

    def test_add_key_warns_before_discarding_a_one_use_activation(self):
        self.authenticator.activate = MagicMock(
            return_value=({"akey": "a"}, "PUBLIC", "PRIVATE")
        )
        self.authenticator.save_config.side_effect = OSError
        with patch(
            "builtins.input",
            side_effect=[
                "2",
                "Cisco Duo",
                ACTIVATION_TOKEN,
                "api-deadbeef.duosecurity.com",
                "n",
            ],
        ):
            with patch("sys.stdout", new_callable=io.StringIO) as output:
                self.authenticator.add_key()

        self.assertNotIn("Cisco Duo", self.authenticator.config["keys"])
        self.assertIn("permanently discards", output.getvalue())

    def test_activation_retry_reuses_the_entered_code_and_host(self):
        activation = ({"akey": "a"}, "PUBLIC", "PRIVATE")
        self.authenticator.activate = MagicMock(side_effect=[None, activation])
        with patch(
            "builtins.input",
            side_effect=[
                "2",
                "Cisco Duo",
                ACTIVATION_TOKEN,
                "api-deadbeef.duosecurity.com",
                "",
            ],
        ):
            with patch("sys.stdout", new_callable=io.StringIO):
                self.authenticator.add_key()

        self.assertEqual(self.authenticator.activate.call_count, 2)
        self.authenticator.activate.assert_called_with(
            ACTIVATION_TOKEN, "api-deadbeef.duosecurity.com"
        )
        self.assertIn("Cisco Duo", self.authenticator.config["keys"])

    def test_keys_menu_uses_requested_names_and_deletes_selected_key(self):
        self.authenticator.config = sample_config()

        with patch(
            "builtins.input", side_effect=["1", "0", "1", "4", "y"]
        ) as user_input:
            with patch("sys.stdout", new_callable=io.StringIO) as output:
                self.authenticator.keys_menu()

        menu = output.getvalue() + "".join(
            call.args[0] for call in user_input.call_args_list
        )
        self.assertIn("Duo Mobile Push / Verified Duo Push", menu)
        self.assertIn("Generate Duo Mobile Passcode", menu)
        self.assertNotIn("Cisco Duo", self.authenticator.config["keys"])
        self.authenticator.save_config.assert_called_once()


if __name__ == "__main__":
    unittest.main()