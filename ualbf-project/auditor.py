#!/usr/bin/env python3
import subprocess
import json
import sys
import os
import hashlib

CORE_THEOREMS = [
    "UALBF.Engine.SieveSoundness.rust_sieve_soundness",
    "UALBF.Engine.Bipartition.prefix_sigma_coprime",
    "UALBF.Engine.Bipartition.ambs_suffix_target",
    "UALBF.Engine.Bipartition.no_solution_no_qpn",
    "UALBF.QPN.AbundancyBound.qpn_abundancy_target",
    "UALBF.QPN.AbundancyBound.qpn_totient_bound",
    "UALBF.QPN.AbundancyBound.abundancy_starvation",
    "UALBF.QPN.Obstruction.legendre_cattaneo_obstruction",
    "UALBF.QPN.BasicProperties.qpn_is_odd_square",
    "UALBF.QPN.PrasadSunitha.qpn_coprime_15_omega_14"
]

def hash_file(filepath):
    hasher = hashlib.sha256()
    if os.path.exists(filepath):
        with open(filepath, 'rb') as f:
            hasher.update(f.read())
        return hasher.hexdigest()
    return "unknown"

def generate_manifest():
    manifest = {"theorems": []}
    
    # Check Lean axioms using the compiler
    cwd = os.path.join(os.path.dirname(__file__), "lean4-proofs")
    
    for thm in CORE_THEOREMS:
        lean_file = "find_axioms.lean"
        lean_path = os.path.join(cwd, lean_file)
        with open(lean_path, "w") as f:
            f.write("import UALBF\n")
            f.write(f"#print axioms {thm}\n")
            
        result = subprocess.run(["lake", "env", "lean", lean_file], cwd=cwd, capture_output=True, text=True)
        
        status = "proven"
        if result.returncode != 0:
            status = "error"
            print(f"Error resolving {thm}: {result.stderr}", file=sys.stderr)
        else:
            output = result.stdout + result.stderr
            if "sorryAx" in output:
                status = "sorry"
            elif "depends on axioms:" in output:
                # check if there are other axioms
                # allow UALBF.FFI.rust_is_prime_sound
                axioms_line = [line for line in output.split('\n') if "depends on axioms:" in line]
                if axioms_line:
                    ax_str = axioms_line[0].split("depends on axioms:")[1].strip()
                    ax_str = ax_str.strip("[]")
                    axioms = [a.strip() for a in ax_str.split(",")]
                    # if any axiom is not the whitelisted one, mark as axiom
                    for ax in axioms:
                        if ax == "sorryAx":
                            status = "sorry"
                            break
                        elif ax not in ["UALBF.FFI.rust_is_prime_sound", "propext", "Classical.choice", "Quot.sound"]:
                            status = "axiom"
        
        # map name to file
        # simple heuristic
        parts = thm.split(".")
        if len(parts) >= 3:
            rel_file = "/".join(parts[:-1]) + ".lean"
        else:
            rel_file = "UALBF.lean"
            
        checksum = hash_file(os.path.join(cwd, rel_file))
        
        manifest["theorems"].append({
            "name": thm,
            "file": rel_file,
            "status": status,
            "checksum": checksum
        })
        
        # cleanup
        if os.path.exists(lean_path):
            os.remove(lean_path)
            
    # Add Verus-verified Rust component hashes
    rust_src_dir = os.path.join(os.path.dirname(__file__), "rust-engine", "src")
    verus_files = ["dfs_tree.rs", "sieve.rs", "verus_proofs.rs", "lean_ffi.rs", "dummy_ffi.c"]
    logic_hasher = hashlib.sha256()
    verus_hashes = {}
    for filename in verus_files:
        filepath = os.path.join(rust_src_dir, filename)
        if os.path.exists(filepath):
            with open(filepath, 'rb') as f:
                content = f.read()
                logic_hasher.update(content)
                file_hasher = hashlib.sha256()
                file_hasher.update(content)
                verus_hashes[filename] = file_hasher.hexdigest()
    
    manifest["verified_logic_hash"] = logic_hasher.hexdigest()
    manifest["verus_hashes"] = verus_hashes
            
    with open("proof_manifest.json", "w") as f:
        json.dump(manifest, f, indent=2)
        
    print("Proof manifest generated at proof_manifest.json")

if __name__ == "__main__":
    generate_manifest()
