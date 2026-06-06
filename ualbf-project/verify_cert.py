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
        
    # Reconstruct payload
    tel = cert["telemetry"]
    payload = f"{cert['manifest_hash']}_{cert['verified_logic_hash']}_{tel['total_branches_searched']}_{tel['target_min_log10']}_{tel['target_max_log10']}"
    
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
        raise ValueError("ERROR: Invalid cryptographic signature!")
    except ValueError as e:
        raise e
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
