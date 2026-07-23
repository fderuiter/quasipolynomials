import pytest

# Python representation of the bash `is_core_file` logic used in .github/workflows/auto-merge.yml
def is_core_file(f: str) -> bool:
    # Block if it touches core directories
    if "rust-engine/" in f or "lean4-proofs/" in f or "verification-lib/" in f:
        return True
    
    # Block if it is a critical manifest/config file
    manifests_and_configs = [
        "bounds_manifest.json",
        "metadata_manifest.json",
        "schema_manifest.json",
        "proof_manifest.json",
        "docs_manifest.json",
        "Cargo.toml",
        "Cargo.lock",
        "flake.nix",
        "flake.lock",
        "Makefile"
    ]
    if any(m in f for m in manifests_and_configs):
        return True
        
    # Block if it is a core python script/library (direct files under ualbf-project/)
    core_python_files = [
        "ualbf-project/auditor.py",
        "ualbf-project/cert_util.py",
        "ualbf-project/verify_cert.py",
        "ualbf-project/verify_metadata.py",
        "ualbf-project/time_utils.py"
    ]
    if f in core_python_files:
        return True
        
    # Block if it is a .github workflow or action
    if ".github/" in f:
        return True
        
    return False


def test_core_files_are_blocked():
    blocked_paths = [
        "ualbf-project/rust-engine/src/main.rs",
        "ualbf-project/lean4-proofs/Validator.lean",
        "ualbf-project/verification-lib/Cargo.toml",
        "ualbf-project/bounds_manifest.json",
        "ualbf-project/metadata_manifest.json",
        "ualbf-project/schema_manifest.json",
        "ualbf-project/proof_manifest.json",
        "docs_manifest.json",
        "ualbf-project/auditor.py",
        "ualbf-project/cert_util.py",
        "ualbf-project/verify_cert.py",
        "ualbf-project/verify_metadata.py",
        "ualbf-project/time_utils.py",
        "ualbf-project/Makefile",
        ".github/workflows/auto-merge.yml",
        "Cargo.toml",
        "Cargo.lock",
        "flake.nix",
        "flake.lock"
    ]
    for path in blocked_paths:
        assert is_core_file(path) is True, f"Expected path to be blocked as core: {path}"


def test_helper_and_non_core_files_are_allowed():
    allowed_paths = [
        "ualbf-project/prototypes/pyproject.toml",
        "ualbf-project/prototypes/proto_violation.py",
        "ualbf-project/scripts/check_literals.py",
        "ualbf-project/scripts/test_style_violation.py",
        "README.md",
        "ualbf-project/TODO.md",
        "ualbf-project/tests/test_bounds_validation.py"
    ]
    for path in allowed_paths:
        assert is_core_file(path) is False, f"Expected path to be allowed: {path}"
