"""
Tests for paper/ingest_cert.py

Covers the PR changes:
- Removed verify_certificate import and call
- Removed manifest_path env var
- Simplified to only read cert and write telemetry.tex
- Dummy output written when cert not found
"""
import json
import os
import subprocess
import sys
import tempfile

import pytest

INGEST_CERT_PATH = os.path.abspath(
    os.path.join(os.path.dirname(__file__), '..', 'paper', 'ingest_cert.py')
)


def run_ingest_cert(env_overrides=None, cwd=None):
    """Run ingest_cert.py as a subprocess and return (returncode, stdout, stderr)."""
    env = os.environ.copy()
    if env_overrides:
        env.update(env_overrides)
    result = subprocess.run(
        [sys.executable, INGEST_CERT_PATH],
        capture_output=True,
        text=True,
        env=env,
        cwd=cwd,
    )
    return result.returncode, result.stdout, result.stderr


def make_cert(
    total_branches=12345,
    pruned=5000,
    max_log=37,
    time_ms=9876,
    manifest_hash="abcdef012345",
):
    return {
        "manifest_hash": manifest_hash,
        "verified_logic_hash": "cafebabe" * 8,
        "telemetry": {
            "target_min_log10": 35,
            "target_max_log10": max_log,
            "sieve_limit": 250000,
            "max_exponent": 4,
            "prefix_stop": 100000000000,
            "total_branches_searched": total_branches,
            "abundance_pruned": pruned,
            "search_space_density": 0.0042,
            "phase2_execution_time_ms": time_ms,
        },
        "signature": "aa" * 64,
        "public_key": "bb" * 32,
    }


# ---------------------------------------------------------------------------
# Tests: dummy output when cert is missing
# ---------------------------------------------------------------------------

class TestDummyOutput:
    def test_exits_0_when_cert_missing(self, tmp_path):
        rc, _, _ = run_ingest_cert(
            env_overrides={"UALBF_CERT_PATH": str(tmp_path / "nonexistent.json")},
            cwd=str(tmp_path),
        )
        assert rc == 0

    def test_writes_telemetry_tex_with_zeros_when_cert_missing(self, tmp_path):
        run_ingest_cert(
            env_overrides={"UALBF_CERT_PATH": str(tmp_path / "nonexistent.json")},
            cwd=str(tmp_path),
        )
        tex_path = tmp_path / "telemetry.tex"
        assert tex_path.exists(), "telemetry.tex should be written even when cert is missing"
        content = tex_path.read_text()
        assert "\\newcommand{\\TelemetryPhaseTwoTime}{0}" in content
        assert "\\newcommand{\\TelemetryPhaseTwoBranches}{0}" in content
        assert "\\newcommand{\\TelemetryPruned}{0}" in content

    def test_dummy_output_uses_max_log_37(self, tmp_path):
        run_ingest_cert(
            env_overrides={"UALBF_CERT_PATH": str(tmp_path / "nonexistent.json")},
            cwd=str(tmp_path),
        )
        content = (tmp_path / "telemetry.tex").read_text()
        assert "\\newcommand{\\TelemetryMaxLog}{37}" in content

    def test_dummy_cert_hash_is_zeros(self, tmp_path):
        run_ingest_cert(
            env_overrides={"UALBF_CERT_PATH": str(tmp_path / "nonexistent.json")},
            cwd=str(tmp_path),
        )
        content = (tmp_path / "telemetry.tex").read_text()
        assert "\\newcommand{\\TelemetryCertHash}{000000000000}" in content


# ---------------------------------------------------------------------------
# Tests: real cert reading
# ---------------------------------------------------------------------------

class TestRealCertReading:
    def test_reads_cert_and_writes_telemetry_tex(self, tmp_path):
        cert = make_cert(total_branches=99999, time_ms=5000, max_log=37)
        cert_path = tmp_path / "formal_certificate.json"
        cert_path.write_text(json.dumps(cert))

        run_ingest_cert(
            env_overrides={"UALBF_CERT_PATH": str(cert_path)},
            cwd=str(tmp_path),
        )

        tex_path = tmp_path / "telemetry.tex"
        assert tex_path.exists()
        content = tex_path.read_text()
        # Time should be converted from ms to seconds
        assert "5.00" in content
        assert "\\TelemetryPhaseTwoTime" in content

    def test_branches_formatted_with_commas(self, tmp_path):
        cert = make_cert(total_branches=1234567)
        cert_path = tmp_path / "cert.json"
        cert_path.write_text(json.dumps(cert))

        run_ingest_cert(
            env_overrides={"UALBF_CERT_PATH": str(cert_path)},
            cwd=str(tmp_path),
        )
        content = (tmp_path / "telemetry.tex").read_text()
        assert "1,234,567" in content

    def test_pruned_formatted_with_commas(self, tmp_path):
        cert = make_cert(pruned=9876543)
        cert_path = tmp_path / "cert.json"
        cert_path.write_text(json.dumps(cert))

        run_ingest_cert(
            env_overrides={"UALBF_CERT_PATH": str(cert_path)},
            cwd=str(tmp_path),
        )
        content = (tmp_path / "telemetry.tex").read_text()
        assert "9,876,543" in content

    def test_max_log_written_correctly(self, tmp_path):
        cert = make_cert(max_log=37)
        cert_path = tmp_path / "cert.json"
        cert_path.write_text(json.dumps(cert))

        run_ingest_cert(
            env_overrides={"UALBF_CERT_PATH": str(cert_path)},
            cwd=str(tmp_path),
        )
        content = (tmp_path / "telemetry.tex").read_text()
        assert "\\newcommand{\\TelemetryMaxLog}{37}" in content

    def test_cert_hash_uses_first_12_chars_of_manifest_hash(self, tmp_path):
        manifest_hash = "1234567890abcdef" * 4  # 64 hex chars
        cert = make_cert(manifest_hash=manifest_hash)
        cert_path = tmp_path / "cert.json"
        cert_path.write_text(json.dumps(cert))

        run_ingest_cert(
            env_overrides={"UALBF_CERT_PATH": str(cert_path)},
            cwd=str(tmp_path),
        )
        content = (tmp_path / "telemetry.tex").read_text()
        # First 12 chars of the manifest hash
        assert f"\\newcommand{{\\TelemetryCertHash}}{{{manifest_hash[:12]}}}" in content

    def test_time_conversion_ms_to_seconds(self, tmp_path):
        cert = make_cert(time_ms=123456)
        cert_path = tmp_path / "cert.json"
        cert_path.write_text(json.dumps(cert))

        run_ingest_cert(
            env_overrides={"UALBF_CERT_PATH": str(cert_path)},
            cwd=str(tmp_path),
        )
        content = (tmp_path / "telemetry.tex").read_text()
        # 123456 ms = 123.46 s
        assert "123.46" in content

    def test_abundance_pruned_fallback_to_branches(self, tmp_path):
        """When abundance_pruned is missing, it should fall back to total_branches."""
        cert = make_cert(total_branches=9999, pruned=9999)
        # Remove abundance_pruned from telemetry
        del cert["telemetry"]["abundance_pruned"]
        cert_path = tmp_path / "cert.json"
        cert_path.write_text(json.dumps(cert))

        run_ingest_cert(
            env_overrides={"UALBF_CERT_PATH": str(cert_path)},
            cwd=str(tmp_path),
        )
        content = (tmp_path / "telemetry.tex").read_text()
        # fallback: pruned = branches = 9999
        assert "9,999" in content


# ---------------------------------------------------------------------------
# Tests: env var configuration
# ---------------------------------------------------------------------------

class TestEnvVarConfiguration:
    def test_ualbf_cert_path_env_var_used(self, tmp_path):
        """UALBF_CERT_PATH should point to the certificate file."""
        cert = make_cert(total_branches=77777)
        custom_cert_path = tmp_path / "custom_cert.json"
        custom_cert_path.write_text(json.dumps(cert))

        run_ingest_cert(
            env_overrides={"UALBF_CERT_PATH": str(custom_cert_path)},
            cwd=str(tmp_path),
        )
        content = (tmp_path / "telemetry.tex").read_text()
        assert "77,777" in content

    def test_no_manifest_path_env_var_needed(self, tmp_path):
        """
        PR removed manifest_path / UALBF_MANIFEST_PATH — verify_certificate
        is no longer called, so no manifest path is needed.
        """
        cert = make_cert()
        cert_path = tmp_path / "cert.json"
        cert_path.write_text(json.dumps(cert))

        # Intentionally do NOT set UALBF_MANIFEST_PATH
        env = {"UALBF_CERT_PATH": str(cert_path)}
        rc, stdout, stderr = run_ingest_cert(env_overrides=env, cwd=str(tmp_path))
        # Should succeed without a manifest
        assert rc == 0
        assert (tmp_path / "telemetry.tex").exists()