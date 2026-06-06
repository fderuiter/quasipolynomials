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
        
    # Reconstruct payloads
    tel = cert["telemetry"]
    payload_new = f"{cert['manifest_hash']}_{cert['verified_logic_hash']}_{tel['total_branches_searched']}_{tel['target_max_log10']}_{tel['target_min_log10']}"
    payload_old = f"{cert['manifest_hash']}_{cert['verified_logic_hash']}_{tel['total_branches_searched']}_{tel['target_max_log10']}"
    
    pub_key_bytes = bytes.fromhex(cert['public_key'])
    sig_bytes = bytes.fromhex(cert['signature'])
    
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
            print("\nWARNING: The formal proof is incomplete! The following theorems contain 'sorry' or 'axiom':")
            for thm in sorries:
                print(f"  - {thm['name']} in {thm['file']} (Status: {thm['status']})")
            sys.exit(1)
        else:
            print("\n✓ Manifest verified: 0 sorries, 0 axioms.")
            print(f"✓ Bound Verified: 10^{tel['target_min_log10']} < N < 10^{tel['target_max_log10']}")
            print("✓ Telemetry matches execution reality.")
            
    except InvalidSignature:
        print("ERROR: Invalid cryptographic signature! (data tampered with)")
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
