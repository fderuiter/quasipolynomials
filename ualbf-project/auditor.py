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
    "UALBF.Engine.Obstruction.qpn_sigma_mod_9",
    "UALBF.FFI.fromU512_toU512",
    "UALBF.FFI.toU512_fromU512",
    "UALBF.FFI.modInverse_spec",
    "UALBF.FFI.U512.w0_mk",
    "UALBF.FFI.U512.w1_mk",
    "UALBF.FFI.U512.w2_mk",
    "UALBF.FFI.U512.w3_mk",
    "UALBF.FFI.U512.w4_mk",
    "UALBF.FFI.U512.w5_mk",
    "UALBF.FFI.U512.w6_mk",
    "UALBF.FFI.U512.w7_mk",
]


def theorem_checksum(name, rel_file, status):
    file_path = os.path.join(
        os.path.dirname(os.path.abspath(__file__)), "lean4-proofs", rel_file
    )
    with open(file_path, "rb") as f:
        return hashlib.sha256(f.read()).hexdigest()


def compute_verus_hashes(verus_content):
    verus_hashes = {}
    current_fn = ""
    current_body = ""
    in_spec = False
    brace_count = 0
    module_stack = []
    global_brace_depth = 0

    for line in verus_content.splitlines():
        trimmed = line.strip()

        if (
            not in_spec
            and "{" in trimmed
            and (trimmed.startswith("mod ") or trimmed.startswith("pub mod "))
        ):
            if trimmed.startswith("pub mod "):
                mod_name = trimmed.removeprefix("pub mod ")
            else:
                mod_name = trimmed.removeprefix("mod ")
            mod_name = mod_name.split("{", 1)[0].strip()
            if mod_name:
                module_stack.append((mod_name, global_brace_depth))

        if not in_spec and any(
            kw in line
            for kw in ["pub spec fn ", "pub open spec fn ", "pub fn ", "pub proof fn "]
        ):
            for kw in ["pub spec fn ", "pub open spec fn ", "pub proof fn ", "pub fn "]:
                if kw in line:
                    parts = line.split(kw, 1)
                    break
            bare_fn_name = parts[1].split("(", 1)[0].strip()
            mod_prefix = "::".join([m[0] for m in module_stack])
            qualified_name = (
                bare_fn_name if not mod_prefix else f"{mod_prefix}::{bare_fn_name}"
            )
            current_fn = qualified_name
            current_body = line
            in_spec = True
            brace_count = line.count("{") - line.count("}")
            if brace_count == 0 and "{" in line:
                verus_hashes[current_fn] = hashlib.sha256(
                    current_body.encode("utf-8")
                ).hexdigest()
                in_spec = False
            continue
        elif in_spec:
            current_body += "\n" + line
            brace_count += line.count("{") - line.count("}")
            if brace_count == 0:
                verus_hashes[current_fn] = hashlib.sha256(
                    current_body.encode("utf-8")
                ).hexdigest()
                in_spec = False
        else:
            global_brace_depth += line.count("{")
            global_brace_depth -= line.count("}")
            while module_stack and global_brace_depth <= module_stack[-1][1]:
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
            print(
                f"Warning: LEAN_SYSROOT is set to {lean_sysroot} but bin/lean was not found or is not executable.",
                file=sys.stderr,
            )

    if not lean_found:
        try:
            result = subprocess.run(
                ["lean", "--print-prefix"], capture_output=True, text=True
            )
            if result.returncode == 0 and result.stdout.strip():
                lean_found = True
        except FileNotFoundError:
            pass

    if not lean_found:
        if os.environ.get("ALLOW_UNVERIFIED_BUILD") == "1":
            print(
                "Warning: Lean 4 toolchain not found, but ALLOW_UNVERIFIED_BUILD=1 is set. Proceeding with unverified build.",
                file=sys.stderr,
            )
            return False

        print("Error: Lean 4 toolchain not found!", file=sys.stderr)
        print(
            "Please install Lean 4: https://leanprover.github.io/lean4/doc/setup.html",
            file=sys.stderr,
        )
        print(
            "e.g., curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh",
            file=sys.stderr,
        )
        print(
            "Or set the LEAN_SYSROOT environment variable if Lean is already installed:",
            file=sys.stderr,
        )
        print("export LEAN_SYSROOT=/path/to/lean", file=sys.stderr)
        print(
            "To build without verified Lean logic (not for production), set ALLOW_UNVERIFIED_BUILD=1",
            file=sys.stderr,
        )
        sys.exit(1)

    return True


def generate_manifest():
    has_lean = check_lean_environment()
    manifest = {"theorems": []}

    # Check Lean axioms using the compiler
    cwd = os.path.join(os.path.dirname(os.path.abspath(__file__)), "lean4-proofs")

    has_error = False
    # Pre-build the isolated target to avoid full environment checks and repeated builds
    if has_lean:
        env = os.environ.copy()
        mock_bin = os.path.abspath(
            os.path.join(
                os.path.dirname(os.path.abspath(__file__)), "build", "mock-bin"
            )
        )
        env["PATH"] = f"{mock_bin}:{env.get('PATH', '')}"
        subprocess.run(
            ["make", "mock-ui"],
            cwd=os.path.dirname(os.path.abspath(__file__)),
            check=True,
        )
        subprocess.run(["lake", "exe", "cache", "get"], cwd=cwd, env=env, check=False)
        subprocess.run(["lake", "build", "UALBF"], cwd=cwd, env=env, check=True)

    for thm in CORE_THEOREMS:
        # map name to file
        # improve heuristic to find actual file
        parts = thm.split(".")
        rel_file = "UALBF.lean"
        for i in range(len(parts) - 1, 0, -1):
            possible_rel = "/".join(parts[:i]) + ".lean"
            possible_path = os.path.join(cwd, possible_rel)
            if os.path.exists(possible_path):
                rel_file = possible_rel
                break

        if not has_lean:
            status = "unverified"
        else:
            lean_file = "find_axioms.lean"
            lean_path = os.path.join(cwd, lean_file)
            with open(lean_path, "w", encoding="utf-8") as f:
                f.write("import UALBF\n")
                f.write(f"#print axioms {thm}\n")

            result = subprocess.run(
                ["lake", "env", "lean", lean_file],
                cwd=cwd,
                env=env,
                capture_output=True,
                text=True,
            )

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
                    ax_str = output.split("depends on axioms:")[1].strip()
                    ax_str = ax_str.replace("[", "").replace("]", "").replace("\n", "")
                    axioms = [a.strip() for a in ax_str.split(",")]
                    # if any axiom is not the whitelisted one, mark as axiom
                    for ax in axioms:
                        if ax == "sorryAx":
                            status = "sorry"
                            has_error = True
                            break
                        elif ax not in [
                            "UALBF.FFI.rust_is_prime_sound",
                            "propext",
                            "Classical.choice",
                            "Quot.sound",
                        ]:
                            status = "axiom"
                            has_error = True
                            break

            # cleanup
            if os.path.exists(lean_path):
                os.remove(lean_path)

        checksum = theorem_checksum(thm, rel_file, status)

        manifest["theorems"].append(
            {"name": thm, "file": rel_file, "status": status, "checksum": checksum}
        )

    # Add Verus-verified Rust component hashes
    rust_engine_dir = os.path.join(
        os.path.dirname(os.path.abspath(__file__)), "rust-engine"
    )
    rust_src_dir = os.path.join(rust_engine_dir, "src")

    # Stabilize the proof_manifest.json for deterministic hashing by setting hashes to empty before saving
    manifest["verified_logic_hash"] = ""
    manifest["verified_extension_hash"] = ""
    with open("proof_manifest.json", "w", encoding="utf-8") as f:
        json.dump(manifest, f, indent=2)

    # Use verification-cli to compute the unified verified_logic_hash
    cli_path = os.path.join(
        os.path.dirname(os.path.abspath(__file__)),
        "verification-lib",
        "target",
        "release",
        "verification_cli",
    )
    repo_root = os.path.dirname(os.path.abspath(__file__))

    # Fallback to cargo if binary is not pre-compiled
    if os.path.exists(cli_path):
        result = subprocess.run(
            [cli_path, "hash-tcb", repo_root], capture_output=True, text=True
        )
    else:
        # Note: the constraints mention not requiring rust toolchain during *verification*,
        # but the auditor is an internal dev tool run by `make audit`, so cargo run is okay here.
        result = subprocess.run(
            [
                "cargo",
                "run",
                "--release",
                "--features",
                "signing",
                "--manifest-path",
                os.path.join(repo_root, "verification-lib", "Cargo.toml"),
                "--bin",
                "verification_cli",
                "--",
                "hash-tcb",
                repo_root,
            ],
            capture_output=True,
            text=True,
        )

    if result.returncode != 0:
        raise RuntimeError(f"Failed to compute verified_logic_hash: {result.stderr}")

    logic_hash = result.stdout.strip()
    manifest["verified_logic_hash"] = logic_hash

    # Compute extension hash
    if os.path.exists(cli_path):
        result_ext = subprocess.run(
            [cli_path, "hash-tcb", repo_root, "--extension"],
            capture_output=True,
            text=True,
        )
    else:
        result_ext = subprocess.run(
            [
                "cargo",
                "run",
                "--release",
                "--features",
                "signing,python,gpu",
                "--manifest-path",
                os.path.join(
                    os.path.dirname(os.path.abspath(__file__)),
                    "verification-lib",
                    "Cargo.toml",
                ),
                "--bin",
                "verification_cli",
                "--",
                "hash-tcb",
                repo_root,
                "--extension",
            ],
            capture_output=True,
            text=True,
        )

    if result_ext.returncode == 0:
        ext_hash = result_ext.stdout.strip()
        manifest["verified_extension_hash"] = ext_hash

    verus_proofs_path = os.path.join(rust_src_dir, "verus_proofs.rs")
    with open(verus_proofs_path, "r", encoding="utf-8") as f:
        verus_hashes = compute_verus_hashes(f.read())

    manifest["verus_hashes"] = verus_hashes

    # Scan and hash all 23 proof files
    proof_files = []
    for root, _, files in os.walk(cwd):
        if ".lake" in root:
            continue
        for file in files:
            if (
                file.endswith(".lean")
                and file != "lakefile.lean"
                and file != "find_axioms.lean"
            ):
                full_path = os.path.join(root, file)
                rel_path = os.path.relpath(full_path, cwd)
                with open(full_path, "rb") as f:
                    content = f.read()
                checksum = hashlib.sha256(content).hexdigest()
                proof_files.append({"file": rel_path, "checksum": checksum})
    manifest["proof_files"] = sorted(proof_files, key=lambda x: x["file"])

    # Compute bounds_manifest.json hash
    bounds_manifest_path = os.path.join(
        os.path.dirname(os.path.abspath(__file__)), "bounds_manifest.json"
    )
    if os.path.exists(bounds_manifest_path):
        with open(bounds_manifest_path, "rb") as f:
            bounds_hash = hashlib.sha256(f.read()).hexdigest()
        manifest["bounds_manifest_hash"] = bounds_hash
    else:
        print(
            f"Warning: bounds_manifest.json not found at {bounds_manifest_path}",
            file=sys.stderr,
        )

    with open("proof_manifest.json", "w", encoding="utf-8") as f:
        json.dump(manifest, f, indent=2)

    print("Proof manifest generated at proof_manifest.json")

    doc_check_passed = check_documentation(manifest)

    if has_error or not doc_check_passed:
        if has_error:
            print(
                "Error: Unproven placeholders ('sorry' or 'axiom') detected in CORE_THEOREMS.",
                file=sys.stderr,
            )
        sys.exit(1)


def check_documentation(manifest):
    import re

    repo_root = os.path.dirname(os.path.abspath(__file__))

    docs_to_check = [
        "semantic_verification_report.md",
        "TCB.md",
        "TUNING.md",
        "TODO.md",
        "rust-engine/README.md",
        "lean4-proofs/README.md",
    ]

    valid_symbols = set()
    for thm in CORE_THEOREMS:
        valid_symbols.add(thm)
        valid_symbols.add(thm.split(".")[-1])

    for fn in manifest.get("verus_hashes", {}).keys():
        valid_symbols.add(fn)
        valid_symbols.add(fn.split("::")[-1])

    lean_regex = re.compile(
        r"^\s*(?:(?:protected|private|noncomputable|partial|unsafe|macro|elab|syntax|@[^\n]+\n)\s*)*(?:def|theorem|lemma|structure|class|inductive|abbrev|constant|axiom|namespace)\s+([a-zA-Z0-9_]+)",
        re.MULTILINE,
    )
    rust_regex = re.compile(
        r"^\s*(?:pub(?:\s*\([^)]+\))?\s+)?(?:unsafe\s+)?(?:fn|struct|enum|const|mod|trait|type|spec\s+fn|proof\s+fn)\s+([a-zA-Z0-9_]+)",
        re.MULTILINE,
    )

    for root, _, files in os.walk(repo_root):
        if ".lake" in root or "target" in root:
            continue
        for file in files:
            if file.endswith(".lean"):
                try:
                    with open(os.path.join(root, file), "r", encoding="utf-8") as f:
                        valid_symbols.update(lean_regex.findall(f.read()))
                except Exception:
                    pass
            elif file.endswith(".rs"):
                try:
                    with open(os.path.join(root, file), "r", encoding="utf-8") as f:
                        valid_symbols.update(rust_regex.findall(f.read()))
                except Exception:
                    pass

    ignore_symbols = {
        "u8",
        "u16",
        "u32",
        "u64",
        "u128",
        "usize",
        "i8",
        "i16",
        "i32",
        "i64",
        "i128",
        "isize",
        "bool",
        "str",
        "String",
        "Option",
        "Result",
        "Vec",
        "Box",
        "make",
        "cargo",
        "lake",
        "python",
        "bash",
        "sh",
        "Prop",
        "def",
        "sorry",
        "axiom",
        "linarith",
        "native_decide",
        "decide",
        "norm_num",
        "rfl",
        "Mathlib",
        "widgetJsAll",
        "rayon",
        "None",
        "Some",
        "Ok",
        "Err",
        "true",
        "false",
        "set_option",
        "exact",
        "unusedVariables",
        "unreachableTactic",
        "import",
        "open",
        "mut",
    }

    errors = []

    for doc in docs_to_check:
        doc_path = os.path.join(repo_root, doc)
        if not os.path.exists(doc_path):
            continue

        try:
            with open(doc_path, "r", encoding="utf-8") as f:
                lines = f.readlines()
        except Exception:
            continue

        doc_rel_to_repo = os.path.basename(repo_root) + "/" + doc

        for i, line in enumerate(lines):
            for link in re.findall(r"\[[^\]]+\]\(([^)]+)\)", line):
                if link.startswith("http"):
                    continue
                if link.startswith("file:///"):
                    errors.append(
                        f"[DOC CHECK ERROR] {doc_rel_to_repo}:{i+1} - Invalid file path: '{link}'"
                    )
                    continue

                target = link.split("#")[0]
                target_repo_rel = os.path.join(repo_root, target)
                target_file_rel = os.path.join(os.path.dirname(doc_path), target)

                if not (
                    os.path.exists(target_repo_rel) or os.path.exists(target_file_rel)
                ):
                    errors.append(
                        f"[DOC CHECK ERROR] {doc_rel_to_repo}:{i+1} - Invalid file path: '{link}'"
                    )

            for bt in re.findall(r"`([^`]+)`", line):
                if "/" in bt or bt.endswith(
                    (".rs", ".md", ".lean", ".json", ".c", ".h", ".toml", ".tex")
                ):
                    target = bt.split("#")[0].split(":")[0]
                    target_repo_rel = os.path.join(repo_root, target)
                    target_file_rel = os.path.join(os.path.dirname(doc_path), target)
                    if not (
                        os.path.exists(target_repo_rel)
                        or os.path.exists(target_file_rel)
                    ):
                        errors.append(
                            f"[DOC CHECK ERROR] {doc_rel_to_repo}:{i+1} - Invalid file path: '{bt}'"
                        )
                elif re.match(r"^[a-zA-Z_][a-zA-Z0-9_:]*$", bt):
                    if bt not in ignore_symbols and bt not in valid_symbols:
                        errors.append(
                            f"[DOC CHECK ERROR] {doc_rel_to_repo}:{i+1} - Invalid code symbol: '{bt}'"
                        )

    for e in errors:
        print(e, file=sys.stderr)

    return len(errors) == 0


if __name__ == "__main__":
    generate_manifest()
