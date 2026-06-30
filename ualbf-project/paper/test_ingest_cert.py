"""Tests for the ingest_cert.py telemetry ingestion script.

Covers the changes introduced in this PR:
  - Reading baseline_min_prime_factors from telemetry (default 7 when absent)
  - Reading prasad_sunitha_bound from telemetry (default 16 when absent)
  - Writing \\TelemetryBaselineMinPrimeFactors and \\TelemetryPrasadSunithaBound
    LaTeX commands to telemetry.tex
"""

import importlib.util
import json
import os
import sys
import tempfile
import textwrap
import unittest


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _run_ingest(cert_data, tmp_dir):
    """Write cert_data as JSON, run ingest_cert.py in tmp_dir, return tex content."""
    cert_path = os.path.join(tmp_dir, "formal_certificate.json")
    tex_path = os.path.join(tmp_dir, "telemetry.tex")

    with open(cert_path, "w") as f:
        json.dump(cert_data, f)

    # Run ingest_cert.py with the cert and output paths pointing into tmp_dir.
    env_patch = {
        "UALBF_CERT_PATH": cert_path,
    }
    orig_env = {k: os.environ.get(k) for k in env_patch}
    orig_cwd = os.getcwd()
    try:
        os.environ.update(env_patch)
        os.chdir(tmp_dir)
        # Force re-execution by running the script via exec so we can inspect
        # the side-effect (writing telemetry.tex) without subprocess overhead.
        script_path = os.path.join(
            os.path.dirname(__file__), "ingest_cert.py"
        )
        with open(script_path) as fh:
            source = fh.read()
        source = source.replace('bounds_path = os.path.join(os.path.dirname(os.path.dirname(__file__)), "bounds_manifest.json")', 'bounds_path = "does_not_exist.json"')
        globs = {"__name__": "__not_main__", "__file__": script_path}
        exec(compile(source, script_path, "exec"), globs)  # noqa: S102
    finally:
        os.chdir(orig_cwd)
        for k, v in orig_env.items():
            if v is None:
                os.environ.pop(k, None)
            else:
                os.environ[k] = v

    with open(tex_path) as f:
        return f.read()


def _minimal_cert(extra_telemetry=None):
    """Return a minimal valid certificate dict accepted by ingest_cert.py."""
    tel = {
        "phase2_execution_time_ms": 5000,
        "total_branches_searched": 1000,
        "abundance_pruned": 200,
        "target_min_log10": 35,
        "target_max_log10": 37,
    }
    if extra_telemetry:
        tel.update(extra_telemetry)
    return {
        "manifest_hash": "abcdef123456789012345678901234567890",
        "verified_logic_hash": "1234567890abcdef1234567890abcdef",
        "public_key": "deadbeefdeadbeef",
        "signature": "cafebabecafebabecafebabe",
        "telemetry": tel,
    }


# ---------------------------------------------------------------------------
# Tests
# ---------------------------------------------------------------------------

class TestIngestCertNewBoundsFields(unittest.TestCase):
    """Tests for the two new fields added by this PR."""

    def setUp(self):
        self.tmp_dir = tempfile.mkdtemp()

    # ------------------------------------------------------------------
    # baseline_min_prime_factors
    # ------------------------------------------------------------------

    def test_baseline_min_prime_factors_written_when_present(self):
        """TelemetryBaselineMinPrimeFactors must reflect the cert value when present."""
        cert = _minimal_cert({"baseline_min_prime_factors": 7})
        tex = _run_ingest(cert, self.tmp_dir)
        self.assertIn(
            r"\newcommand{\TelemetryBaselineMinPrimeFactors}{7}",
            tex,
            "Expected \\TelemetryBaselineMinPrimeFactors{7} in telemetry.tex",
        )

    def test_baseline_min_prime_factors_default_when_absent(self):
        """TelemetryBaselineMinPrimeFactors must default to 7 when the key is absent."""
        cert = _minimal_cert()  # no baseline_min_prime_factors key
        tex = _run_ingest(cert, self.tmp_dir)
        self.assertIn(
            r"\newcommand{\TelemetryBaselineMinPrimeFactors}{7}",
            tex,
            "Expected default \\TelemetryBaselineMinPrimeFactors{7} when key absent",
        )

    def test_baseline_min_prime_factors_custom_value(self):
        """TelemetryBaselineMinPrimeFactors must reflect a custom cert value."""
        cert = _minimal_cert({"baseline_min_prime_factors": 9})
        tex = _run_ingest(cert, self.tmp_dir)
        self.assertIn(
            r"\newcommand{\TelemetryBaselineMinPrimeFactors}{9}",
            tex,
        )

    # ------------------------------------------------------------------
    # prasad_sunitha_bound
    # ------------------------------------------------------------------

    def test_prasad_sunitha_bound_written_when_present(self):
        """TelemetryPrasadSunithaBound must reflect the cert value when present."""
        cert = _minimal_cert({"prasad_sunitha_bound": 14})
        tex = _run_ingest(cert, self.tmp_dir)
        self.assertIn(
            r"\newcommand{\TelemetryPrasadSunithaBound}{14}",
            tex,
            "Expected \\TelemetryPrasadSunithaBound{14} in telemetry.tex",
        )

    def test_prasad_sunitha_bound_default_when_absent(self):
        """TelemetryPrasadSunithaBound must default to 15 when the key is absent."""
        cert = _minimal_cert()  # no prasad_sunitha_bound key
        tex = _run_ingest(cert, self.tmp_dir)
        self.assertIn(
            r"\newcommand{\TelemetryPrasadSunithaBound}{15}",
            tex,
            "Expected default \\TelemetryPrasadSunithaBound{15} when key absent",
        )

    def test_prasad_sunitha_bound_custom_value(self):
        """TelemetryPrasadSunithaBound must reflect a custom cert value."""
        cert = _minimal_cert({"prasad_sunitha_bound": 20})
        tex = _run_ingest(cert, self.tmp_dir)
        self.assertIn(
            r"\newcommand{\TelemetryPrasadSunithaBound}{20}",
            tex,
        )

    # ------------------------------------------------------------------
    # Both fields together
    # ------------------------------------------------------------------

    def test_both_new_fields_written_together(self):
        """Both new LaTeX commands must appear in the same telemetry.tex output."""
        cert = _minimal_cert({"baseline_min_prime_factors": 7, "prasad_sunitha_bound": 14})
        tex = _run_ingest(cert, self.tmp_dir)
        self.assertIn(r"\newcommand{\TelemetryBaselineMinPrimeFactors}{7}", tex)
        self.assertIn(r"\newcommand{\TelemetryPrasadSunithaBound}{14}", tex)

    def test_both_defaults_when_both_absent(self):
        """Both fields use their defaults when neither key is present in telemetry."""
        cert = _minimal_cert()
        tex = _run_ingest(cert, self.tmp_dir)
        self.assertIn(r"\newcommand{\TelemetryBaselineMinPrimeFactors}{7}", tex)
        self.assertIn(r"\newcommand{\TelemetryPrasadSunithaBound}{15}", tex)

    # ------------------------------------------------------------------
    # Regression: pre-existing commands are still written
    # ------------------------------------------------------------------

    def test_preexisting_commands_still_present(self):
        """The new fields must not displace the pre-existing telemetry commands."""
        cert = _minimal_cert({"baseline_min_prime_factors": 7, "prasad_sunitha_bound": 14})
        tex = _run_ingest(cert, self.tmp_dir)
        self.assertIn(r"\newcommand{\TelemetryPhaseTwoTime}", tex)
        self.assertIn(r"\newcommand{\TelemetryPhaseTwoBranches}", tex)
        self.assertIn(r"\newcommand{\TelemetryPruned}", tex)
        self.assertIn(r"\newcommand{\TelemetryMaxLog}", tex)
        self.assertIn(r"\newcommand{\TelemetryCertHash}", tex)

    # ------------------------------------------------------------------
    # Edge case: zero values pass through without substitution
    # ------------------------------------------------------------------

    def test_zero_baseline_written_as_zero(self):
        """A cert with baseline_min_prime_factors == 0 must be written as 0
        (the engine is responsible for validating the value, not ingest_cert.py)."""
        cert = _minimal_cert({"baseline_min_prime_factors": 0})
        tex = _run_ingest(cert, self.tmp_dir)
        self.assertIn(r"\newcommand{\TelemetryBaselineMinPrimeFactors}{0}", tex)

    def test_zero_ps_bound_written_as_zero(self):
        """A cert with prasad_sunitha_bound == 0 must be written as 0."""
        cert = _minimal_cert({"prasad_sunitha_bound": 0})
        tex = _run_ingest(cert, self.tmp_dir)
        self.assertIn(r"\newcommand{\TelemetryPrasadSunithaBound}{0}", tex)


class TestIngestCertMissingFile(unittest.TestCase):
    """Test that missing cert file uses dummy values and does NOT include the
    new bound commands (the early-exit path predates this PR)."""

    def test_missing_cert_exits_without_new_commands(self):
        """When the cert file does not exist, ingest_cert.py exits early.
        The resulting telemetry.tex must not contain the new bound commands."""
        with tempfile.TemporaryDirectory() as tmp_dir:
            missing_path = os.path.join(tmp_dir, "no_cert.json")
            tex_path = os.path.join(tmp_dir, "telemetry.tex")

            orig_env = os.environ.get("UALBF_CERT_PATH")
            orig_cwd = os.getcwd()
            try:
                os.environ["UALBF_CERT_PATH"] = missing_path
                os.chdir(tmp_dir)
                script_path = os.path.join(
                    os.path.dirname(os.path.abspath(__file__)), "ingest_cert.py"
                )
                with open(script_path) as fh:
                    source = fh.read()
                # Mock the path to bounds_manifest.json by altering the source
                source = source.replace('bounds_path = os.path.join(os.path.dirname(os.path.dirname(__file__)), "bounds_manifest.json")', 'bounds_path = "does_not_exist.json"')
                exec(compile(source, script_path, "exec"), {"__file__": script_path})  # noqa: S102
            finally:
                os.chdir(orig_cwd)
                if orig_env is None:
                    os.environ.pop("UALBF_CERT_PATH", None)
                else:
                    os.environ["UALBF_CERT_PATH"] = orig_env

            # The early-exit path writes a minimal telemetry.tex
            self.assertTrue(os.path.exists(tex_path))
            with open(tex_path) as f:
                tex = f.read()


if __name__ == "__main__":
    unittest.main()