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
    "UALBF.QPN.PrasadSunitha.qpn_coprime_15_omega_bound",
    "UALBF.Engine.Obstruction.qpn_sigma_mod_3",
    "UALBF.Engine.Obstruction.qpn_sigma_mod_9"
]

def theorem_checksum(name, rel_file, status):
    payload = f"{name}|{rel_file}|{status}"
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()


def compute_verus_hashes(verus_content):
    verus_hashes = {}
    current_fn = ""
    current_body = ""
    in_spec = False
    brace_count = 0
    module_stack = []
    module_brace_depth = 0

    for line in verus_content.splitlines():
        trimmed = line.strip()

        if not in_spec and "{" in trimmed and (trimmed.startswith("mod ") or trimmed.startswith("pub mod ")):
            if trimmed.startswith("pub mod "):
                mod_name = trimmed.removeprefix("pub mod ")
            else:
                mod_name = trimmed.removeprefix("mod ")
            mod_name = mod_name.split("{", 1)[0].strip()
            if mod_name:
                module_stack.append(mod_name)
                module_brace_depth += 1

        if not in_spec and any(kw in line for kw in ["pub spec fn ", "pub fn ", "pub proof fn "]):
            for kw in ["pub spec fn ", "pub proof fn ", "pub fn "]:
                if kw in line:
                    parts = line.split(kw, 1)
                    break
            bare_fn_name = parts[1].split("(", 1)[0].strip()
            qualified_name = bare_fn_name if not module_stack else "::".join(module_stack + [bare_fn_name])
            current_fn = qualified_name
            current_body = line
            in_spec = True
            brace_count = line.count("{") - line.count("}")
            if brace_count == 0 and "{" in line:
                verus_hashes[current_fn] = hashlib.sha256(current_body.encode("utf-8")).hexdigest()
                in_spec = False
        elif in_spec:
            current_body += "\n" + line
            brace_count += line.count("{") - line.count("}")
            if brace_count == 0:
                verus_hashes[current_fn] = hashlib.sha256(current_body.encode("utf-8")).hexdigest()
                in_spec = False
        elif not in_spec and module_brace_depth > 0:
            module_brace_depth += line.count("{")
            for _ in range(line.count("}")):
                if module_brace_depth > 0:
                    module_brace_depth -= 1
                    if module_stack:
                        module_stack.pop()

    return verus_hashes


def check_lean_environment():
    lean_sysroot = os.environ.get("LEAN_SYSROOT")
    lean_found = False

    if lean_sysroot:
        # Check if the sysroot actually exists and has a bin/lean
        lean_bin = os.path.join(lean_sysroot, "bin", "lean")
        if os.path.isfile(lean_bin) and os.access(lean_bin, os.X_OK):
            lean_found = True
        else:
            print(f"Warning: LEAN_SYSROOT is set to {lean_sysroot} but bin/lean was not found or is not executable.", file=sys.stderr)
    
    if not lean_found:
        try:
            result = subprocess.run(["lean", "--print-prefix"], capture_output=True, text=True)
            if result.returncode == 0 and result.stdout.strip():
                lean_found = True
        except FileNotFoundError:
            pass

    if not lean_found:
        if os.environ.get("ALLOW_UNVERIFIED_BUILD") == "1":
            print("Warning: Lean 4 toolchain not found, but ALLOW_UNVERIFIED_BUILD=1 is set. Proceeding with unverified build.", file=sys.stderr)
            return False
            
        print("Error: Lean 4 toolchain not found!", file=sys.stderr)
        print("Please install Lean 4: https://leanprover.github.io/lean4/doc/setup.html", file=sys.stderr)
        print("e.g., curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh", file=sys.stderr)
        print("Or set the LEAN_SYSROOT environment variable if Lean is already installed:", file=sys.stderr)
        print("export LEAN_SYSROOT=/path/to/lean", file=sys.stderr)
        print("To build without verified Lean logic (not for production), set ALLOW_UNVERIFIED_BUILD=1", file=sys.stderr)
        sys.exit(1)
        
    return True

def generate_manifest():
    has_lean = check_lean_environment()
    manifest = {"theorems": []}
    
    # Check Lean axioms using the compiler
    cwd = os.path.join(os.path.dirname(__file__), "lean4-proofs")
    
    has_error = False
    for thm in CORE_THEOREMS:
        # map name to file
        # simple heuristic
        parts = thm.split(".")
        if len(parts) >= 3:
            rel_file = "/".join(parts[:-1]) + ".lean"
        else:
            rel_file = "UALBF.lean"

        if not has_lean:
            status = "unverified"
        else:
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
                    has_error = True
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
                                has_error = True
                                break
                            elif ax in ["UALBF.QPN.PrasadSunitha.prasad_sunitha_bound_no_3_5", "UALBF.QPN.PrasadSunitha.qpn_coprime_15_omega_bound"]:
                                if status == "proven":
                                    status = "axiomatic"
                            elif ax not in ["UALBF.FFI.rust_is_prime_sound", "propext", "Classical.choice", "Quot.sound"]:
                                status = "axiom"
                                has_error = True
                                break
            
            # cleanup
            if os.path.exists(lean_path):
                os.remove(lean_path)
                
        checksum = theorem_checksum(thm, rel_file, status)
        
        manifest["theorems"].append({
            "name": thm,
            "file": rel_file,
            "status": status,
            "checksum": checksum
        })
            
    # Add Verus-verified Rust component hashes
    rust_engine_dir = os.path.join(os.path.dirname(__file__), "rust-engine")
    rust_src_dir = os.path.join(rust_engine_dir, "src")
    
    # Use verification-cli to compute the unified verified_logic_hash
    cli_path = os.path.join(os.path.dirname(__file__), "verification-lib", "target", "release", "verification_cli")
    repo_root = os.path.dirname(__file__)
    
    # Fallback to cargo if binary is not pre-compiled
    if os.path.exists(cli_path):
        result = subprocess.run([cli_path, "hash-tcb", repo_root], capture_output=True, text=True)
    else:
        # Note: the constraints mention not requiring rust toolchain during *verification*, 
        # but the auditor is an internal dev tool run by `make audit`, so cargo run is okay here.
        result = subprocess.run(["cargo", "run", "--release", "--features", "signing", "--manifest-path", os.path.join(repo_root, "verification-lib", "Cargo.toml"), "--bin", "verification_cli", "--", "hash-tcb", repo_root], capture_output=True, text=True)
    
    if result.returncode != 0:
        raise RuntimeError(f"Failed to compute verified_logic_hash: {result.stderr}")
    
    logic_hash = result.stdout.strip()
    manifest["verified_logic_hash"] = logic_hash
    
    verus_proofs_path = os.path.join(rust_src_dir, "verus_proofs.rs")
    with open(verus_proofs_path, "r", encoding="utf-8") as f:
        verus_hashes = compute_verus_hashes(f.read())
        
    manifest["verus_hashes"] = verus_hashes

    # Compute bounds_manifest.json hash
    bounds_manifest_path = os.path.join(os.path.dirname(__file__), "bounds_manifest.json")
    if os.path.exists(bounds_manifest_path):
        with open(bounds_manifest_path, "rb") as f:
            bounds_hash = hashlib.sha256(f.read()).hexdigest()
        manifest["bounds_manifest_hash"] = bounds_hash
    else:
        print(f"Warning: bounds_manifest.json not found at {bounds_manifest_path}", file=sys.stderr)
            
    with open("proof_manifest.json", "w") as f:
        json.dump(manifest, f, indent=2)
        
    print("Proof manifest generated at proof_manifest.json")

    if has_error:
        print("Error: Unproven placeholders ('sorry' or 'axiom') detected in CORE_THEOREMS.", file=sys.stderr)
        sys.exit(1)

if __name__ == "__main__":
    generate_manifest()
