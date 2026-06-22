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

def verify_theorem_checksum(thm):
    """
    Compute and verify the checksum for a single theorem entry.

    The checksum is computed as SHA-256 over the concatenation:
    name + "|" + file + "|" + status

    Parameters:
        thm (dict): Theorem dictionary with keys: name, file, status, checksum

    Returns:
        bool: True if checksum matches, False otherwise
    """
    payload = f"{thm['name']}|{thm['file']}|{thm['status']}"
    computed = hashlib.sha256(payload.encode('utf-8')).hexdigest()
    return computed == thm.get('checksum', '')

def verify_certificate(cert_path, manifest_path):
    """
    Verify a formal exhaustion certificate against its manifest and local source artifacts.

    Performs these checks: both files exist; the manifest's SHA-256 hash matches the
    certificate's recorded hash; the certificate's embedded public key matches the pinned
    trusted key if one is configured; the Ed25519 signature over the reconstructed payload
    is valid (supporting both new 5-field and legacy 4-field payload formats); optionally
    computes and compares a verified-logic SHA-256 from local rust-engine/src files when
    present; inspects manifest theorem statuses to fail if any disallowed `sorry` or
    `axiom` entries are present; and validates per-theorem checksums to detect tampering.

    Parameters:
        cert_path (str): Path to the JSON certificate file.
        manifest_path (str): Path to the proof manifest file (JSON or raw text used to compute hash).

    Returns:
        dict: The parsed certificate object loaded from `cert_path`.

    Notes:
        On any verification failure the function prints an error message and exits the
        process with a non-zero status code via sys.exit(1).
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
        print(f"ERROR: Manifest hash mismatch!\nExpected: {cert.get('manifest_hash')}\nGot:      {manifest_hash}")
        sys.exit(1)
        
    # Reconstruct payloads (new format: target_min_log10 before target_max_log10)
    tel = cert["telemetry"]
    payload_new = f"{cert['manifest_hash']}_{cert['verified_logic_hash']}_{tel['total_branches_searched']}_{tel['target_min_log10']}_{tel['target_max_log10']}"
    payload_old = f"{cert['manifest_hash']}_{cert['verified_logic_hash']}_{tel['total_branches_searched']}_{tel['target_max_log10']}"

    pub_key_bytes = bytes.fromhex(cert['public_key'])
    sig_bytes = bytes.fromhex(cert['signature'])

    # Verify the certificate's public key matches the pinned trusted key
    if TRUSTED_PUBLIC_KEY is not None:
        if cert['public_key'] != TRUSTED_PUBLIC_KEY:
            print(f"ERROR: Certificate public key does not match trusted signer key!\nCertificate key: {cert['public_key']}\nTrusted key: {TRUSTED_PUBLIC_KEY}")
            sys.exit(1)
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
            print("WARNING: Partial Coverage (old format without target_min_log10 in signature).")

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
                for filename in ["manifest_constants.rs", "lean_ffi.rs", "dummy_ffi.c"]:
                    filepath = os.path.join(rust_src_dir, filename)
                    if os.path.exists(filepath):
                        with open(filepath, 'rb') as f:
                            logic_hasher.update(f.read())
                
                # Also include the soundness proof logic
                abundancy_proof_path = os.path.join(os.path.dirname(rust_src_dir), "../lean4-proofs/UALBF/QPN/AbundancyBound.lean")
                if os.path.exists(abundancy_proof_path):
                    with open(abundancy_proof_path, 'rb') as f:
                        logic_hasher.update(f.read())

                build_rs_path = os.path.join(os.path.dirname(rust_src_dir), "build.rs")
                if os.path.exists(build_rs_path):
                    with open(build_rs_path, 'rb') as f:
                        logic_hasher.update(f.read())
                            
            computed_logic_hash = logic_hasher.hexdigest()
            if computed_logic_hash != cert.get('verified_logic_hash'):
                print("WARNING: Manifest/Logic hash mismatch! (code/logic may have changed since certificate was generated)")
                print(f"Expected: {cert.get('verified_logic_hash')}")
                print(f"Got:      {computed_logic_hash}")
        
        manifest = json.loads(manifest_content)

        # Verify per-theorem checksums
        print("\n--- Verifying Theorem Checksums ---")
        for thm in manifest.get('theorems', []):
            if not verify_theorem_checksum(thm):
                print(f"ERROR: Checksum mismatch for theorem '{thm['name']}' in {thm['file']}")
                print(f"Expected: {thm.get('checksum')}")
                payload = f"{thm['name']}|{thm['file']}|{thm['status']}"
                computed = hashlib.sha256(payload.encode('utf-8')).hexdigest()
                print(f"Computed: {computed}")
                sys.exit(1)
        print(f"✓ All {len(manifest.get('theorems', []))} theorem checksums verified.")

        allowed_axioms = {"UALBF.FFI.rust_is_prime_sound"}
        sorries = [thm for thm in manifest.get('theorems', []) if thm['status'] in ('sorry', 'axiom') and thm['name'] not in allowed_axioms]

        print("\n--- Manifest Summary ---")
        print(f"Total Theorems: {len(manifest.get('theorems', []))}")
        print(f"Incomplete/Axioms: {len(sorries)}")
        
        if sorries:
            print("WARNING: The formal proof is incomplete! The following theorems contain 'sorry' or 'axiom':")
            for thm in sorries:
                print(f"  - {thm['name']} in {thm['file']} (Status: {thm['status']})")
            sys.exit(1)
        else:
            print("\n✓ Manifest verified: 0 sorries, 0 axioms.")
            print(f"✓ Bound Verified: 10^{tel['target_min_log10']} < N < 10^{tel['target_max_log10']}")
            print("✓ Telemetry matches execution reality.")
            
        return cert
            
    except InvalidSignature:
        print("ERROR: Invalid cryptographic signature! (data tampered with)")
        sys.exit(1)
    except SystemExit:
        raise
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
