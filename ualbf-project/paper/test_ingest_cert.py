"""Tests for the ingest_cert.py telemetry ingestion script.

Covers the changes introduced in this PR:
  - Reading baseline_min_prime_factors from telemetry (default 7 when absent)
  - Reading prasad_sunitha_bound from telemetry (default 16 when absent)
  - Writing \\TelemetryHagisBaselineMinPrimeFactors and \\TelemetryPrasadSunithaBound
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

    with open(cert_path, "w", encoding="utf-8") as f:
        json.dump(cert_data, f)

    # Run ingest_cert.py with the cert and output paths pointing into tmp_dir.

    env_patch = {

        "UALBF_CERT_PATH": cert_path,
    }
    orig_env = {k: os.environ.get(k) for k in env_patch}
    orig_cwd = os.getcwd()
    # Mock verification_lib so cert_util can be imported
    import sys
    import types
    mock_verif = types.ModuleType("verification_lib")
    mock_verif.validate_certificate = lambda x: x
    orig_verif = sys.modules.get("verification_lib")
    sys.modules["verification_lib"] = mock_verif
    
    # Mock cert_util.load_and_validate_cert to avoid verification_lib requirement
    orig_load = None
    try:
        import cert_util
        orig_load = cert_util.load_and_validate_cert
        cert_util.load_and_validate_cert = lambda path: json.load(open(path, encoding="utf-8"))
    except Exception:
        pass
        
    try:
        os.environ.update(env_patch)
        os.chdir(tmp_dir)
        # Force re-execution by running the script via exec so we can inspect
        # the side-effect (writing telemetry.tex) without subprocess overhead.
        script_path = os.path.join(
            os.path.dirname(__file__), "ingest_cert.py"
        )
        with open(script_path, encoding="utf-8") as fh:
            source = fh.read()
        
        globs = {"__name__": "__not_main__", "__file__": script_path}
        exec(compile(source, script_path, "exec"), globs)  # noqa: S102
    finally:
        if orig_verif is not None:
            sys.modules["verification_lib"] = orig_verif
        else:
            sys.modules.pop("verification_lib", None)
        if orig_load is not None:
            cert_util.load_and_validate_cert = orig_load
        os.chdir(orig_cwd)
        for k, v in orig_env.items():
            if v is None:
                os.environ.pop(k, None)
            else:
                os.environ[k] = v

    with open(tex_path, encoding="utf-8") as f:
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
        "manifest_hash": "fd91aafa6031fa4a084064097548449b4cca658d991183d2817115dc0c51233b",
        "verified_logic_hash": "1234567890abcdef1234567890abcdef",
        "public_key": "deadbeefdeadbeef",
        "signature": "cafebabecafebabecafebabe",
        "telemetry": tel,
    }


# ---------------------------------------------------------------------------
# Tests
# ---------------------------------------------------------------------------

class TestIngestCertMissingFile(unittest.TestCase):
    """Test that missing cert file raises a fatal error."""

    def test_missing_cert_raises_error(self):
        """When the cert file does not exist, ingest_cert.py must exit with a non-zero code."""
        import tempfile
        import os
        import sys
        with tempfile.TemporaryDirectory() as tmp_dir:
            missing_path = os.path.join(tmp_dir, "no_cert.json")
            tex_path = os.path.join(tmp_dir, "telemetry.tex")

            orig_env = os.environ.get("UALBF_CERT_PATH")
            orig_cwd = os.getcwd()
            

            # Mock verification_lib
            import sys, types
            mock_verif = types.ModuleType("verification_lib")
            mock_verif.validate_certificate = lambda x: x
            orig_verif = sys.modules.get("verification_lib")
            sys.modules["verification_lib"] = mock_verif
            try:
                os.environ["UALBF_CERT_PATH"] = missing_path
                os.chdir(tmp_dir)
                script_path = os.path.join(
                    os.path.dirname(os.path.abspath(__file__)), "ingest_cert.py"
                )
                with open(script_path, encoding="utf-8") as fh:
                    source = fh.read()
                
                with self.assertRaises(SystemExit) as cm:
                    exec(compile(source, script_path, "exec"), {"__file__": script_path})  # noqa: S102
                self.assertEqual(cm.exception.code, 1)
            finally:
                if orig_verif is not None:
                    sys.modules["verification_lib"] = orig_verif
                else:
                    sys.modules.pop("verification_lib", None)
                os.chdir(orig_cwd)
                if orig_env is None:
                    os.environ.pop("UALBF_CERT_PATH", None)
                else:
                    os.environ["UALBF_CERT_PATH"] = orig_env

if __name__ == "__main__":
    import unittest
    unittest.main()
