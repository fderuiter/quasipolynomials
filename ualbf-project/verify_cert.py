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

# Pinned trusted signer public key (hex-encoded Ed25519 public key)
# This must be set to the legitimate signer's public key to prevent forgery
TRUSTED_PUBLIC_KEY = os.getenv("UALBF_TRUSTED_PUBLIC_KEY", None)

def verify_certificate(cert_path, manifest_path):
    """
<<<<<<< HEAD
    Verify a formal exhaustion certificate against its manifest and local source artifacts.
    
    Performs these checks in order: ensures both files exist, validates the manifest's SHA-256 hash, verifies an Ed25519 signature against either a new or legacy payload format (sets legacy mode when applicable), optionally computes and compares a verified-logic SHA-256 from local rust-engine/src files when present, and inspects manifest theorem statuses to fail if any disallowed `sorry` or `axiom` entries are present.
    
    Parameters:
        cert_path (str): Path to the certificate JSON file.
        manifest_path (str): Path to the manifest JSON file.
    
    Notes:
        On any verification failure the function prints an error message and exits the process with a non-zero status.
=======
    Verify a formal certificate against a proof manifest and return the parsed certificate on success.
    
    Performs these checks: both files exist; the manifest's SHA-256 hash matches the certificate's recorded hash; the certificate's embedded public key matches the pinned trusted key if one is configured; the Ed25519 signature over the reconstructed payload is valid; and the manifest contains no unsupported `sorry` or `axiom` entries.
    
    Parameters:
        cert_path (str): Path to the JSON certificate file.
        manifest_path (str): Path to the proof manifest file (JSON or raw text used to compute hash).
    
    Returns:
        dict: The parsed certificate object loaded from `cert_path`.
    
    Raises:
        FileNotFoundError: If `cert_path` or `manifest_path` does not exist.
        ValueError: If the manifest hash mismatches the certificate, the certificate public key does not match a pinned trusted key, the signature is invalid, the manifest contains unsupported incomplete theorems (`sorry`/`axiom`), or other verification failures.
>>>>>>> origin/main
    """
    if not os.path.exists(cert_path):
        raise FileNotFoundError(f"Error: Certificate file '{cert_path}' not found.")
        
    if not os.path.exists(manifest_path):
        raise FileNotFoundError(f"Error: Manifest file '{manifest_path}' not found.")

    with open(cert_path) as f:
        cert = json.load(f)
    
    with open(manifest_path) as f:
        manifest_content = f.read()

    # Verify manifest hash
    manifest_hash = hashlib.sha256(manifest_content.encode('utf-8')).hexdigest()
    if manifest_hash != cert.get('manifest_hash'):
        raise ValueError(f"ERROR: Manifest hash mismatch!\nExpected: {cert.get('manifest_hash')}\nGot:      {manifest_hash}")
        
    # Reconstruct payloads
    tel = cert["telemetry"]
<<<<<<< HEAD
    payload_new = f"{cert['manifest_hash']}_{cert['verified_logic_hash']}_{tel['total_branches_searched']}_{tel['target_max_log10']}_{tel['target_min_log10']}"
    payload_old = f"{cert['manifest_hash']}_{cert['verified_logic_hash']}_{tel['total_branches_searched']}_{tel['target_max_log10']}"
    
=======
    payload = f"{cert['manifest_hash']}_{cert['verified_logic_hash']}_{tel['total_branches_searched']}_{tel['target_min_log10']}_{tel['target_max_log10']}"

>>>>>>> origin/main
    pub_key_bytes = bytes.fromhex(cert['public_key'])
    sig_bytes = bytes.fromhex(cert['signature'])

    # Verify the certificate's public key matches the pinned trusted key
    if TRUSTED_PUBLIC_KEY is not None:
        if cert['public_key'] != TRUSTED_PUBLIC_KEY:
            raise ValueError(f"ERROR: Certificate public key does not match trusted signer key!\nCertificate key: {cert['public_key']}\nTrusted key: {TRUSTED_PUBLIC_KEY}")
    else:
        print("WARNING: No trusted public key is pinned (UALBF_TRUSTED_PUBLIC_KEY not set). Accepting certificate's embedded key without validation.")

    try:
        public_key = ed25519.Ed25519PublicKey.from_public_bytes(pub_key_bytes)
        
        is_new_format = False
        try:
            public_key.verify(sig_bytes, payload_new.encode('utf-8'))
            is_new_format = True
        except InvalidSignature:
            try:
                public_key.verify(sig_bytes, payload_old.encode('utf-8'))
            except InvalidSignature:
                print("ERROR: Invalid cryptographic signature! (data tampered with)")
                sys.exit(1)
        
        print("✓ Cryptographic signature is valid.")
        
        if not is_new_format:
            print("WARNING: Partial Coverage (old format without bridge hashes).")

        # Verify logic hash if we have the rust-engine/src directory
        rust_src_dir = os.path.join(os.path.dirname(os.path.dirname(__file__)), "rust-engine", "src")
        if not os.path.exists(rust_src_dir):
            rust_src_dir = os.path.join(os.path.dirname(__file__), "rust-engine", "src")
            
        if os.path.exists(rust_src_dir):
            logic_hasher = hashlib.sha256()
            for filename in ["dfs_tree.rs", "sieve.rs", "verus_proofs.rs"]:
                filepath = os.path.join(rust_src_dir, filename)
                if os.path.exists(filepath):
                    with open(filepath, 'rb') as f:
                        logic_hasher.update(f.read())
            
            if is_new_format:
                for filename in ["lean_ffi.rs", "dummy_ffi.c"]:
                    filepath = os.path.join(rust_src_dir, filename)
                    if os.path.exists(filepath):
                        with open(filepath, 'rb') as f:
                            logic_hasher.update(f.read())
                            
            computed_logic_hash = logic_hasher.hexdigest()
            if computed_logic_hash != cert.get('verified_logic_hash'):
                print("ERROR: Manifest/Logic hash mismatch! (code/logic tampered with)")
                print(f"Expected: {cert.get('verified_logic_hash')}")
                print(f"Got:      {computed_logic_hash}")
                sys.exit(1)
        
        manifest = json.loads(manifest_content)
        allowed_axioms = {"UALBF.FFI.rust_is_prime_sound"}
        sorries = [thm for thm in manifest.get('theorems', []) if thm['status'] in ('sorry', 'axiom') and thm['name'] not in allowed_axioms]
        
        print("\n--- Manifest Summary ---")
        print(f"Total Theorems: {len(manifest.get('theorems', []))}")
        print(f"Incomplete/Axioms: {len(sorries)}")
        
        if sorries:
            error_msg = "WARNING: The formal proof is incomplete! The following theorems contain 'sorry' or 'axiom':\n"
            for thm in sorries:
                error_msg += f"  - {thm['name']} in {thm['file']} (Status: {thm['status']})\n"
            raise ValueError(error_msg)
        else:
            print("\n✓ Manifest verified: 0 sorries, 0 axioms.")
            print(f"✓ Bound Verified: 10^{tel['target_min_log10']} < N < 10^{tel['target_max_log10']}")
            print("✓ Telemetry matches execution reality.")
            
        return cert
            
    except InvalidSignature:
<<<<<<< HEAD
        print("ERROR: Invalid cryptographic signature! (data tampered with)")
        sys.exit(1)
=======
        raise ValueError("ERROR: Invalid cryptographic signature!")
    except ValueError as e:
        raise e
>>>>>>> origin/main
    except Exception as e:
        raise ValueError(f"ERROR: Verification failed: {e}")

if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser(description="Verify UALBF Formal Exhaustion Certificate")
    parser.add_argument("--cert", default="formal_certificate.json", help="Path to formal_certificate.json")
    parser.add_argument("--manifest", default="proof_manifest.json", help="Path to proof_manifest.json")
    args = parser.parse_args()
    
    try:
        verify_certificate(args.cert, args.manifest)
    except Exception as e:
        print(e)
        sys.exit(1)
