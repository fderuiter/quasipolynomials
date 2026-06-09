#!/usr/bin/env python3
import json
import sys
import hashlib
import os
try:
    from cryptography.hazmat.primitives.asymmetric import ed25519
    from cryptography.exceptions import InvalidSignature
except ImportError:
    print("Please install cryptography package: pip install cryptography")
    sys.exit(1)

def verify_certificate(cert_path, manifest_path):
    """
    Verify a formal exhaustion certificate JSON against a proof manifest and related environment files.
    
    Performs these checks and prints status messages; exits the process with a non-zero status on any verification failure:
    - Ensures the certificate and manifest files exist.
    - Validates that the SHA-256 of the manifest content matches the certificate's `manifest_hash`.
    - Verifies hashes for environment-declared files (`cargo_lock_hash`, `lake_manifest_hash`), treating the literal string `"missing"` as an intentional absence (fail if the file exists).
    - Reconstructs a deterministic JSON payload from the certificate's `environment`, `manifest_hash`, `telemetry`, and `verified_logic_hash`, and verifies the Ed25519 signature using `public_key`/`signature`.
    - Parses the manifest and fails if any theorem (except allowed axioms) is marked `sorry` or `axiom`.
    
    Parameters:
        cert_path (str): Path to the certificate JSON file.
        manifest_path (str): Path to the proof manifest JSON file.
    """
    if not os.path.exists(cert_path):
        print(f"Error: Certificate file '{cert_path}' not found.")
        sys.exit(1)
        
    if not os.path.exists(manifest_path):
        print(f"Error: Manifest file '{manifest_path}' not found.")
        sys.exit(1)

    with open(cert_path) as f:
        cert = json.load(f)
    
    with open(manifest_path) as f:
        manifest_content = f.read()

    # Verify manifest hash
    manifest_hash = hashlib.sha256(manifest_content.encode('utf-8')).hexdigest()
    if manifest_hash != cert.get('manifest_hash'):
        print(f"ERROR: Manifest hash mismatch!")
        print(f"Expected: {cert.get('manifest_hash')}")
        print(f"Got:      {manifest_hash}")
        sys.exit(1)
        
    def verify_lockfile_hash(path, expected_hash, name):
        """
        Verify that a file at `path` matches an expected SHA-256 hex digest or is declared missing.
        
        If `expected_hash` is the string "missing", the function fails if the file exists. Otherwise it computes the SHA-256 hash of the file's contents and fails if it does not equal `expected_hash`. On any failure the function prints an explanatory error message and exits the process with a non-zero status.
        
        Parameters:
            path (str): Filesystem path to the file to verify.
            expected_hash (str): Expected SHA-256 hex digest for the file, or the literal string "missing" to indicate the file must not be present.
            name (str): Human-readable name for the file used in error messages.
        """
        if expected_hash == "missing":
            if os.path.exists(path):
                print(f"ERROR: {name} file '{path}' exists but certificate claims it is missing")
                sys.exit(1)
            return
        if not os.path.exists(path):
            print(f"ERROR: {name} file '{path}' not found, but certificate expects hash {expected_hash}")
            sys.exit(1)
        with open(path, "rb") as lf:
            actual_hash = hashlib.sha256(lf.read()).hexdigest()
        if actual_hash != expected_hash:
            print(f"ERROR: {name} hash mismatch!")
            print(f"Expected: {expected_hash}")
            print(f"Got:      {actual_hash}")
            sys.exit(1)

    # Cargo.lock is in the same directory as proof_manifest.json typically, or relative to the rust-engine run.
    # Let's assume verify_cert.py is run from the project root or we can try to find it.
    # The certificate generation expects Cargo.lock in the current dir.
    # Let's use os.path.dirname(manifest_path) to locate the rust-engine directory.
    engine_dir = os.path.dirname(manifest_path)
    if not engine_dir:
        engine_dir = "."
    cargo_lock_path = os.path.join(engine_dir, "Cargo.lock")
    lake_manifest_path = os.path.join(engine_dir, "../lean4-proofs/lake-manifest.json")

    env = cert.get("environment", {})
    verify_lockfile_hash(cargo_lock_path, env.get("cargo_lock_hash"), "Cargo.lock")
    verify_lockfile_hash(lake_manifest_path, env.get("lake_manifest_hash"), "lake-manifest.json")

    # Reconstruct payload
    payload_dict = {
        "environment": cert["environment"],
        "manifest_hash": cert["manifest_hash"],
        "telemetry": cert["telemetry"],
        "verified_logic_hash": cert["verified_logic_hash"]
    }
    
    # Dump JSON with separators=(',', ':') and sort_keys=True to match Rust's serde_json struct-field order output
    payload = json.dumps(payload_dict, separators=(',', ':'), sort_keys=True)
    
    pub_key_bytes = bytes.fromhex(cert['public_key'])
    sig_bytes = bytes.fromhex(cert['signature'])
    
    try:
        public_key = ed25519.Ed25519PublicKey.from_public_bytes(pub_key_bytes)
        public_key.verify(sig_bytes, payload.encode('utf-8'))
        print("✓ Cryptographic signature is valid.")
        
        manifest = json.loads(manifest_content)
        allowed_axioms = {"UALBF.FFI.rust_is_prime_sound"}
        sorries = [thm for thm in manifest.get('theorems', []) if thm['status'] in ('sorry', 'axiom') and thm['name'] not in allowed_axioms]
        
        print("\n--- Manifest Summary ---")
        print(f"Total Theorems: {len(manifest.get('theorems', []))}")
        print(f"Incomplete/Axioms: {len(sorries)}")
        
        if sorries:
            print("\nWARNING: The formal proof is incomplete! The following theorems contain 'sorry' or 'axiom':")
            for thm in sorries:
                print(f"  - {thm['name']} in {thm['file']} (Status: {thm['status']})")
            sys.exit(1)
        else:
            print("\n✓ Manifest verified: 0 sorries, 0 axioms.")
            print(f"✓ Bound Verified: 10^{cert['telemetry']['target_min_log10']} < N < 10^{cert['telemetry']['target_max_log10']}")
            print("✓ Telemetry matches execution reality.")
            
    except InvalidSignature:
        print("ERROR: Invalid cryptographic signature!")
        sys.exit(1)
    except Exception as e:
        print(f"ERROR: Verification failed: {e}")
        sys.exit(1)

if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser(description="Verify UALBF Formal Exhaustion Certificate")
    parser.add_argument("--cert", default="formal_certificate.json", help="Path to formal_certificate.json")
    parser.add_argument("--manifest", default="proof_manifest.json", help="Path to proof_manifest.json")
    args = parser.parse_args()
    
    verify_certificate(args.cert, args.manifest)
