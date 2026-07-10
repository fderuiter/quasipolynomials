"""
Tests for verify_cert.py

Covers the PR changes:
- Simplified payload format: "{manifest_hash}_{verified_logic_hash}_{total_branches}_{target_max_log10}"
- Removed environment/lockfile hash verification
- Removed docstrings
"""

import hashlib
import json
import os
import sys
import tempfile
import pytest

# Import cryptography for creating test keypairs
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey
from cryptography.hazmat.primitives.serialization import Encoding, PublicFormat

# Add project root to path so we can import verify_cert
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))
from verify_cert import verify_certificate


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------


def make_manifest(theorems=None):
    """Return a minimal proof manifest dict."""
    if theorems is None:
        name = "UALBF.Pure.Arithmetic.foo"
        file = "UALBF/Pure/Arithmetic.lean"
        status = "proven"
        payload = f"{name}|{file}|{status}"
        checksum = hashlib.sha256(payload.encode("utf-8")).hexdigest()
        theorems = [
            {"name": name, "file": file, "status": status, "checksum": checksum},
        ]
    else:
        for t in theorems:
            if t.get("checksum") in ["x", "y", "allowed"]:
                payload = f"{t['name']}|{t['file']}|{t['status']}"
                t["checksum"] = hashlib.sha256(payload.encode("utf-8")).hexdigest()

    return {"theorems": theorems}


def sign_payload(payload_str: str) -> tuple[str, str]:
    """Return (public_key_hex, signature_hex) for the given payload string."""
    private_key = Ed25519PrivateKey.generate()
    sig = private_key.sign(payload_str.encode("utf-8"))
    pub = private_key.public_key().public_bytes(Encoding.Raw, PublicFormat.Raw)
    return pub.hex(), sig.hex()


def build_cert(
    manifest_hash: str,
    verified_logic_hash: str = "aabbccdd" * 8,
    total_branches: int = 42,
    target_max_log10: int = 37,
    target_min_log10: int = 35,
    tamper_sig: bool = False,
) -> dict:
    """Construct a minimal valid (or optionally tampered) certificate."""
    payload = f"{manifest_hash}_{verified_logic_hash}_{total_branches}_{target_max_log10}"
    pub_hex, sig_hex = sign_payload(payload)
    if tamper_sig:
        # Flip first byte of signature
        sig_bytes = bytearray(bytes.fromhex(sig_hex))
        sig_bytes[0] ^= 0xFF
        sig_hex = sig_bytes.hex()
    return {
        "manifest_hash": manifest_hash,
        "verified_logic_hash": verified_logic_hash,
        "telemetry": {
            "target_min_log10": target_min_log10,
            "target_max_log10": target_max_log10,
            "sieve_limit": 250000,
            "max_exponent": 4,
            "prefix_stop": 100000000000,
            "total_branches_searched": total_branches,
            "abundance_pruned": 5000,
            "search_space_density": 0.0042,
            "phase2_execution_time_ms": 12345,
        },
        "signature": sig_hex,
        "public_key": pub_hex,
    }


def write_files(manifest: dict, cert: dict) -> tuple[str, str]:
    """Write manifest and cert to temp files, return (cert_path, manifest_path)."""
    tmpdir = tempfile.mkdtemp()
    cert_path = os.path.join(tmpdir, "formal_certificate.json")
    manifest_path = os.path.join(tmpdir, "proof_manifest.json")
    bounds_path = os.path.join(tmpdir, "bounds_manifest.json")

    # Create dummy bounds manifest
    bounds_content = b'{"dummy": "bounds"}'
    with open(bounds_path, "wb") as f:
        f.write(bounds_content)

    if "bounds_manifest_hash" not in manifest:
        manifest["bounds_manifest_hash"] = hashlib.sha256(bounds_content).hexdigest()

    manifest_content = json.dumps(manifest)
    manifest_hash = hashlib.sha256(manifest_content.encode("utf-8")).hexdigest()
    cert["manifest_hash"] = manifest_hash
    # Re-sign with correct manifest hash
    tel = cert["telemetry"]
    total_branches = tel["total_branches_searched"]
    target_max_log10 = tel["target_max_log10"]
    target_min_log10 = tel.get("target_min_log10", 35)
    trace_hash = tel.get("trace_hash", "")
    factorization_depth = tel.get("factorization_depth", 0)
    verified_logic_hash = cert["verified_logic_hash"]

    map_obj = {
        "manifest_hash": manifest_hash,
        "verified_logic_hash": verified_logic_hash,
        "total_branches_searched": total_branches,
        "target_min_log10": target_min_log10,
        "target_max_log10": target_max_log10,
        "trace_hash": trace_hash,
        "factorization_depth": factorization_depth,
    }
    payload = json.dumps(map_obj, separators=(",", ":"), sort_keys=True)
    pub_hex, sig_hex = sign_payload(payload)
    cert["signature"] = sig_hex
    cert["public_key"] = pub_hex

    with open(cert_path, "w") as f:
        json.dump(cert, f)
    with open(manifest_path, "w") as f:
        f.write(manifest_content)
    return cert_path, manifest_path


# ---------------------------------------------------------------------------
# Tests: missing files
# ---------------------------------------------------------------------------


class TestMissingFiles:
    def test_missing_cert_exits_1(self, tmp_path):
        cert_path = str(tmp_path / "nonexistent_cert.json")
        manifest_path = str(tmp_path / "proof_manifest.json")
        # Create manifest but not cert
        with open(manifest_path, "w") as f:
            json.dump(make_manifest(), f)
        with pytest.raises(SystemExit) as exc_info:
            verify_certificate(cert_path, manifest_path)
        assert exc_info.value.code != 0

    def test_missing_manifest_exits_1(self, tmp_path):
        manifest = make_manifest()
        manifest_content = json.dumps(manifest)
        manifest_hash = hashlib.sha256(manifest_content.encode()).hexdigest()
        cert = build_cert(manifest_hash)
        cert_path = str(tmp_path / "formal_certificate.json")
        manifest_path = str(tmp_path / "nonexistent_manifest.json")
        with open(cert_path, "w") as f:
            json.dump(cert, f)
        with pytest.raises(SystemExit) as exc_info:
            verify_certificate(cert_path, manifest_path)
        assert exc_info.value.code != 0


# ---------------------------------------------------------------------------
# Tests: manifest hash verification
# ---------------------------------------------------------------------------


class TestManifestHashVerification:
    def test_correct_manifest_hash_passes(self, tmp_path, capsys):
        manifest = make_manifest()
        cert = build_cert("placeholder")
        cert_path, manifest_path = write_files(manifest, cert)
        # Should not raise SystemExit
        verify_certificate(cert_path, manifest_path)
        captured = capsys.readouterr()
        assert "signature is valid" in captured.out.lower()

    def test_tampered_manifest_exits(self, tmp_path):
        manifest = make_manifest()
        manifest_content = json.dumps(manifest)
        manifest_hash = hashlib.sha256(manifest_content.encode()).hexdigest()
        cert = build_cert(manifest_hash)

        cert_path = str(tmp_path / "formal_certificate.json")
        manifest_path = str(tmp_path / "proof_manifest.json")

        # Put correct manifest hash in cert but different content in file
        with open(cert_path, "w") as f:
            json.dump(cert, f)
        with open(manifest_path, "w") as f:
            f.write('{"theorems": []}')  # different content

        with pytest.raises(SystemExit) as exc_info:
            verify_certificate(cert_path, manifest_path)
        assert exc_info.value.code != 0


# ---------------------------------------------------------------------------
# Tests: signature verification
# ---------------------------------------------------------------------------


class TestSignatureVerification:
    def test_valid_signature_passes(self, capsys):
        manifest = make_manifest()
        cert = build_cert("placeholder")
        cert_path, manifest_path = write_files(manifest, cert)
        verify_certificate(cert_path, manifest_path)
        captured = capsys.readouterr()
        assert "valid" in captured.out.lower()

    def test_invalid_signature_exits(self, tmp_path):
        manifest = make_manifest()
        manifest_content = json.dumps(manifest)
        manifest_hash = hashlib.sha256(manifest_content.encode()).hexdigest()
        cert = build_cert(manifest_hash, tamper_sig=True)

        cert_path = str(tmp_path / "formal_certificate.json")
        manifest_path = str(tmp_path / "proof_manifest.json")
        with open(cert_path, "w") as f:
            json.dump(cert, f)
        with open(manifest_path, "w") as f:
            f.write(manifest_content)

        with pytest.raises(SystemExit) as exc_info:
            verify_certificate(cert_path, manifest_path)
        assert exc_info.value.code != 0

    def test_wrong_public_key_exits(self, tmp_path):
        """Signature from one key cannot be verified with a different key."""
        manifest = make_manifest()
        manifest_content = json.dumps(manifest)
        manifest_hash = hashlib.sha256(manifest_content.encode()).hexdigest()
        cert = build_cert(manifest_hash)

        # Replace public key with a fresh random key
        different_key = Ed25519PrivateKey.generate()
        wrong_pub = different_key.public_key().public_bytes(Encoding.Raw, PublicFormat.Raw)
        cert["public_key"] = wrong_pub.hex()

        cert_path = str(tmp_path / "formal_certificate.json")
        manifest_path = str(tmp_path / "proof_manifest.json")
        with open(cert_path, "w") as f:
            json.dump(cert, f)
        with open(manifest_path, "w") as f:
            f.write(manifest_content)

        with pytest.raises(SystemExit) as exc_info:
            verify_certificate(cert_path, manifest_path)
        assert exc_info.value.code != 0


# ---------------------------------------------------------------------------
# Tests: payload format (PR change — new simple string format)
# ---------------------------------------------------------------------------


class TestPayloadFormat:
    def test_payload_uses_new_format(self, tmp_path):
        """
        The PR changed the payload to canonical JSON.
        Ensure the exact format is expected by signing with the new format and verifying.
        """
        manifest = make_manifest()
        bounds_content = b'{"dummy": "bounds"}'
        manifest["bounds_manifest_hash"] = hashlib.sha256(bounds_content).hexdigest()
        manifest_content = json.dumps(manifest)
        manifest_hash = hashlib.sha256(manifest_content.encode()).hexdigest()

        verified_logic_hash = "deadbeef" * 8
        total_branches = 999
        target_max_log10 = 37
        target_min_log10 = 35
        trace_hash = "dummytrace"
        factorization_depth = 1000000

        map_obj = {
            "manifest_hash": manifest_hash,
            "verified_logic_hash": verified_logic_hash,
            "total_branches_searched": total_branches,
            "target_min_log10": target_min_log10,
            "target_max_log10": target_max_log10,
            "trace_hash": trace_hash,
            "factorization_depth": factorization_depth,
        }
        payload = json.dumps(map_obj, separators=(",", ":"), sort_keys=True)
        pub_hex, sig_hex = sign_payload(payload)

        cert = {
            "manifest_hash": manifest_hash,
            "verified_logic_hash": verified_logic_hash,
            "telemetry": {
                "target_min_log10": target_min_log10,
                "target_max_log10": target_max_log10,
                "sieve_limit": 250000,
                "max_exponent": 4,
                "prefix_stop": 100000000000,
                "total_branches_searched": total_branches,
                "abundance_pruned": 0,
                "search_space_density": 0.0,
                "phase2_execution_time_ms": 0,
                "trace_hash": trace_hash,
                "factorization_depth": factorization_depth,
            },
            "signature": sig_hex,
            "public_key": pub_hex,
        }

        cert_path = str(tmp_path / "cert.json")
        manifest_path = str(tmp_path / "manifest.json")
        bounds_path = str(tmp_path / "bounds_manifest.json")
        with open(cert_path, "w") as f:
            json.dump(cert, f)
        with open(manifest_path, "w") as f:
            f.write(manifest_content)
        with open(bounds_path, "wb") as f:
            f.write(bounds_content)

        # Should succeed without SystemExit
        verify_certificate(cert_path, manifest_path)

    def test_old_json_payload_format_fails(self, tmp_path):
        """
        The old payload was a JSON dict; signing with old format must fail verification
        because the verifier now uses the new string format.
        """
        manifest = make_manifest()
        bounds_content = b'{"dummy": "bounds"}'
        manifest["bounds_manifest_hash"] = hashlib.sha256(bounds_content).hexdigest()
        manifest_content = json.dumps(manifest)
        manifest_hash = hashlib.sha256(manifest_content.encode()).hexdigest()

        verified_logic_hash = "deadbeef" * 8
        total_branches = 999
        target_max_log10 = 37

        # Sign using old JSON format
        old_payload = json.dumps(
            {
                "manifest_hash": manifest_hash,
                "telemetry": {
                    "total_branches_searched": total_branches,
                    "target_max_log10": target_max_log10,
                },
                "verified_logic_hash": verified_logic_hash,
            },
            separators=(",", ":"),
            sort_keys=True,
        )
        pub_hex, sig_hex = sign_payload(old_payload)

        cert = {
            "manifest_hash": manifest_hash,
            "verified_logic_hash": verified_logic_hash,
            "telemetry": {
                "target_min_log10": 35,
                "target_max_log10": target_max_log10,
                "sieve_limit": 250000,
                "max_exponent": 4,
                "prefix_stop": 100000000000,
                "total_branches_searched": total_branches,
                "abundance_pruned": 0,
                "search_space_density": 0.0,
                "phase2_execution_time_ms": 0,
            },
            "signature": sig_hex,
            "public_key": pub_hex,
        }

        cert_path = str(tmp_path / "cert.json")
        manifest_path = str(tmp_path / "manifest.json")
        bounds_path = str(tmp_path / "bounds_manifest.json")
        with open(cert_path, "w") as f:
            json.dump(cert, f)
        with open(manifest_path, "w") as f:
            f.write(manifest_content)
        with open(bounds_path, "wb") as f:
            f.write(bounds_content)

        with pytest.raises(SystemExit) as exc_info:
            verify_certificate(cert_path, manifest_path)
        assert exc_info.value.code != 0


# ---------------------------------------------------------------------------
# Tests: manifest theorem checking
# ---------------------------------------------------------------------------


class TestTheoremChecking:
    def test_no_sorries_passes(self, capsys):
        manifest = make_manifest(
            [
                {"name": "UALBF.Foo", "file": "F.lean", "status": "proven", "checksum": "x"},
                {"name": "UALBF.Bar", "file": "F.lean", "status": "proven", "checksum": "y"},
            ]
        )
        cert = build_cert("placeholder")
        cert_path, manifest_path = write_files(manifest, cert)
        verify_certificate(cert_path, manifest_path)
        captured = capsys.readouterr()
        assert "0 sorries" in captured.out

    def test_sorry_theorem_exits(self, tmp_path):
        manifest = make_manifest(
            [
                {"name": "UALBF.Foo", "file": "F.lean", "status": "proven", "checksum": "x"},
                {
                    "name": "UALBF.BrokenTheorem",
                    "file": "B.lean",
                    "status": "sorry",
                    "checksum": "z",
                },
            ]
        )
        cert = build_cert("placeholder")
        cert_path, manifest_path = write_files(manifest, cert)
        with pytest.raises(SystemExit) as exc_info:
            verify_certificate(cert_path, manifest_path)
        assert exc_info.value.code != 0

    def test_axiom_theorem_exits(self, tmp_path):
        manifest = make_manifest(
            [
                {"name": "UALBF.SomeAxiom", "file": "A.lean", "status": "axiom", "checksum": "a"},
            ]
        )
        cert = build_cert("placeholder")
        cert_path, manifest_path = write_files(manifest, cert)
        with pytest.raises(SystemExit) as exc_info:
            verify_certificate(cert_path, manifest_path)
        assert exc_info.value.code != 0

    def test_allowed_axiom_rust_is_prime_sound_passes(self, capsys):
        """UALBF.FFI.rust_is_prime_sound is no longer whitelisted, so this should fail."""
        manifest = make_manifest(
            [
                {
                    "name": "UALBF.FFI.rust_is_prime_sound",
                    "file": "FFI.lean",
                    "status": "axiom",
                    "checksum": "allowed",
                },
            ]
        )
        cert = build_cert("placeholder")
        cert_path, manifest_path = write_files(manifest, cert)
        # Should exit due to zero-axiom policy
        import pytest

        with pytest.raises(SystemExit) as exc_info:
            verify_certificate(cert_path, manifest_path)
        assert exc_info.value.code != 0

    def test_multiple_sorries_all_reported(self, tmp_path, capsys):
        manifest = make_manifest(
            [
                {"name": "UALBF.Foo", "file": "F.lean", "status": "sorry", "checksum": "a"},
                {"name": "UALBF.Bar", "file": "B.lean", "status": "sorry", "checksum": "b"},
            ]
        )
        cert = build_cert("placeholder")
        cert_path, manifest_path = write_files(manifest, cert)
        with pytest.raises(SystemExit):
            verify_certificate(cert_path, manifest_path)

    def test_empty_theorems_list_passes(self, capsys):
        manifest = make_manifest([])
        cert = build_cert("placeholder")
        cert_path, manifest_path = write_files(manifest, cert)
        verify_certificate(cert_path, manifest_path)
        captured = capsys.readouterr()
        assert "0 sorries" in captured.out


# ---------------------------------------------------------------------------
# Tests: bound output
# ---------------------------------------------------------------------------


class TestBoundOutput:
    def test_bound_printed_correctly(self, capsys):
        manifest = make_manifest()
        cert = build_cert("placeholder", target_min_log10=35, target_max_log10=37)
        cert_path, manifest_path = write_files(manifest, cert)
        verify_certificate(cert_path, manifest_path)
        captured = capsys.readouterr()
        assert "10^35" in captured.out
        assert "10^37" in captured.out

    def test_custom_bounds_printed(self, capsys):
        manifest = make_manifest()
        cert = build_cert("placeholder", target_min_log10=10, target_max_log10=20)
        cert_path, manifest_path = write_files(manifest, cert)
        verify_certificate(cert_path, manifest_path)
        captured = capsys.readouterr()
        assert "10^10" in captured.out
        assert "10^20" in captured.out
