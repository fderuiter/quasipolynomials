import json
import os
import sys

# Add parent directory to sys.path so we can import cert_util
sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import cert_util


bounds_path = os.path.join(os.path.dirname(os.path.dirname(__file__)), "bounds_manifest.json")
if not os.path.exists(bounds_path):
    print(f"Error: bounds_manifest.json not found at {bounds_path}.")
    sys.exit(1)

with open(bounds_path, "r") as bf:
    bounds = json.load(bf)

# Enforce required keys
required_keys = ["omega_bounds", "euler_ceiling", "search_bounds"]
for k in required_keys:
    if k not in bounds:
        print(f"Error: bounds_manifest.json missing required key '{k}'.")
        sys.exit(1)

manifest_min_log = bounds["search_bounds"]["target_min_log10"]["value"]
manifest_max_log = bounds["search_bounds"]["target_max_log10"]["value"]


def format_time_ms(ms):
    s = ms // 1000
    h = s // 3600
    s %= 3600
    m = s // 60
    s %= 60
    return f"{h} hours, {m} minutes, {s} seconds"

cert_path = os.environ.get("UALBF_CERT_PATH")
if not cert_path:
    print("Error: UALBF_CERT_PATH environment variable is required.")
    sys.exit(1)

has_cert = os.path.exists(cert_path)
if not has_cert:
    print(f"Warning: {cert_path} not found. Proceeding with dummy values.")

with open("telemetry.tex", "w") as f:
    if has_cert:
        try:
            cert = cert_util.load_and_validate_cert(cert_path)
        except cert_util.CertificateError as e:
            print(f"Error: {e}")
            sys.exit(1)
            
        tel = cert["telemetry"]
        time_ms = tel["phase2_execution_time_ms"]
        branches = tel["total_branches_searched"]
            
        pruned = tel.get("abundance_pruned", branches)
        raycast = tel.get("raycast_pruned", 0)
        total_pruned = pruned + raycast
        if total_pruned > 0:
            abundance_pct = (pruned / total_pruned) * 100.0
            raycast_pct = (raycast / total_pruned) * 100.0
        else:
            abundance_pct = 100.0
            raycast_pct = 0.0
        
        nodes_per_sec = branches / (time_ms / 1000.0) if time_ms > 0 else 0
        
        p1_time = tel.get("phase1_execution_time_ms", 0)
        total_time = tel.get("total_execution_time_ms", p1_time + time_ms)
        p1_pruned = tel.get("phase1_pruned", 0)
        
        max_log = tel["target_max_log10"]
        min_log = tel["target_min_log10"]
        f.write(f"\\newcommand{{\\TelemetryPhaseTwoTime}}{{{time_ms / 1000:.2f}}}\n")
        f.write(f"\\newcommand{{\\TelemetryPhaseTwoBranches}}{{{branches:,}}}\n")
        f.write(f"\\newcommand{{\\TelemetryPruned}}{{{total_pruned:,}}}\n")
        f.write(f"\\newcommand{{\\TelemetryMaxLog}}{{{max_log}}}\n")
        f.write(f"\\newcommand{{\\TelemetryMinLog}}{{{min_log}}}\n")
        f.write(f"\\newcommand{{\\TelemetryCertHash}}{{{cert['manifest_hash'][:12]}}}\n")
        
        f.write(f"\\newcommand{{\\TelemetryPhaseOnePruned}}{{{p1_pruned:,}}}\n")
        f.write(f"\\newcommand{{\\TelemetryTotalTime}}{{{format_time_ms(total_time)}}}\n")
        f.write(f"\\newcommand{{\\TelemetryPhaseOneTime}}{{{format_time_ms(p1_time)}}}\n")
        f.write(f"\\newcommand{{\\TelemetryNodesPerSec}}{{{int(nodes_per_sec):,}}}\n")
        f.write(f"\\newcommand{{\\TelemetryAbundancePct}}{{{abundance_pct:.1f}}}\n")
        f.write(f"\\newcommand{{\\TelemetryRaycastPct}}{{{raycast_pct:.1f}}}\n")
        
        # New requirements
        f.write(f"\\newcommand{{\\TelemetryEngineVersion}}{{{cert.get('engine_version', 'unknown')}}}\n")
        f.write(f"\\newcommand{{\\TelemetryCommitHash}}{{{cert.get('commit_hash', 'unknown')}}}\n")
        
        bounds_exceeded = tel.get("bounds_exceeded", False)
        if bounds_exceeded:
            print("Error: Search space boundaries were exceeded during telemetry capture.")
            sys.exit(1)
        f.write(f"\\newcommand{{\\TelemetryBoundsEnforced}}{{True}}\n")
    else:
        f.write("\\newcommand{\\TelemetryPhaseTwoTime}{0}\n")
        f.write("\\newcommand{\\TelemetryPhaseTwoBranches}{0}\n")
        f.write("\\newcommand{\\TelemetryPruned}{0}\n")
        f.write(f"\\newcommand{{\\TelemetryMaxLog}}{{{manifest_max_log}}}\n")
        f.write(f"\\newcommand{{\\TelemetryMinLog}}{{{manifest_min_log}}}\n")
        f.write("\\newcommand{\\TelemetryCertHash}{000000000000}\n")
        f.write("\\newcommand{\\TelemetryPhaseOnePruned}{0}\n")
        f.write("\\newcommand{\\TelemetryTotalTime}{0 hours, 0 minutes, 0 seconds}\n")
        f.write("\\newcommand{\\TelemetryPhaseOneTime}{0 hours, 0 minutes, 0 seconds}\n")
        f.write("\\newcommand{\\TelemetryNodesPerSec}{0}\n")
        f.write("\\newcommand{\\TelemetryAbundancePct}{0.0}\n")
        f.write("\\newcommand{\\TelemetryRaycastPct}{0.0}\n")
        f.write("\\newcommand{\\TelemetryEngineVersion}{unknown}\n")
        f.write("\\newcommand{\\TelemetryCommitHash}{unknown}\n")
        f.write("\\newcommand{\\TelemetryBoundsEnforced}{False}\n")
        tel = {}

    if has_cert:
        # Enforce recursive chain of trust
        manifest_path = os.path.join(os.path.dirname(os.path.dirname(__file__)), "proof_manifest.json")
        if not os.path.exists(manifest_path):
            print(f"Error: Proof manifest '{manifest_path}' not found, cannot verify chain of trust.")
            sys.exit(1)
        
        with open(manifest_path, "rb") as mf:
            manifest_content_bytes = mf.read()
        import hashlib
        computed_manifest_hash = hashlib.sha256(manifest_content_bytes).hexdigest()
        if computed_manifest_hash != cert.get("manifest_hash"):
            print("Error: Proof manifest hash mismatch in chain of trust.")
            sys.exit(1)
        
        manifest_data = json.loads(manifest_content_bytes.decode('utf-8'))
        expected_bounds_hash = manifest_data.get("bounds_manifest_hash")
        if not expected_bounds_hash:
            print("Error: Proof manifest missing bounds_manifest_hash.")
            sys.exit(1)
        
        with open(bounds_path, "rb") as bf:
            computed_bounds_hash = hashlib.sha256(bf.read()).hexdigest()
        if computed_bounds_hash != expected_bounds_hash:
            print("Error: Bounds manifest hash mismatch in chain of trust.")
            sys.exit(1)
        
    ps_bound = bounds["omega_bounds"]["prasad_sunitha"]["proof_bound"] + bounds["omega_bounds"]["prasad_sunitha"]["engine_justified_gap"]
    baseline = bounds["omega_bounds"]["baseline"]["proof_bound"] + bounds["omega_bounds"]["baseline"]["engine_justified_gap"]
        
    f.write(f"\\newcommand{{\\TelemetryBaselineMinPrimeFactors}}{{{baseline}}}\n")
    f.write(f"\\newcommand{{\\TelemetryPrasadSunithaBound}}{{{ps_bound}}}\n")

    # Generate verification macros and check hashes
    manifest_path_for_macros = os.path.join(os.path.dirname(os.path.dirname(__file__)), "proof_manifest.json")
    if os.path.exists(manifest_path_for_macros):
        import re
        def make_macro_name(s):
            parts = re.split(r'[._]', s)
            res = "Hash"
            for p in parts:
                if not p: continue
                res += p[0].upper() + p[1:]
            return res
            
        with open(manifest_path_for_macros, "rb") as mf:
            manifest_data_macros = json.loads(mf.read().decode('utf-8'))
            
        # Requirement 4: Verify current hashes against codebase
        import auditor
        rust_file = os.path.join(os.path.dirname(os.path.dirname(__file__)), "rust-engine", "src", "verus_proofs.rs")
        if os.path.exists(rust_file):
            with open(rust_file, "r", encoding="utf-8") as rf:
                local_verus = auditor.compute_verus_hashes(rf.read())
                
            expected_verus = manifest_data_macros.get("verus_hashes", {})
            for fn, expected_hash in expected_verus.items():
                if local_verus.get(fn) != expected_hash:
                    print(f"Error: Local codebase hashes do not match proof_manifest.json! Modification detected in {fn}.")
                    sys.exit(1)
        
        # Write LaTeX macros
        for thm in manifest_data_macros.get("theorems", []):
            name = thm["name"]
            status = thm["status"]
            macro_name = make_macro_name(name)
            f.write(f"\\newcommand{{\\{macro_name}}}{{{thm['checksum']}}}\n")
            f.write(f"\\newcommand{{\\{macro_name}Status}}{{{status}}}\n")
            
        for fn, h in manifest_data_macros.get("verus_hashes", {}).items():
            macro_name = make_macro_name(fn)
            f.write(f"\\newcommand{{\\{macro_name}}}{{{h}}}\n")
            
        # Write Verification Table
        with open("verification_manifest.tex", "w") as vm:
            vm.write("\\begin{table}[h]\n")
            vm.write("\\centering\n")
            vm.write("\\begin{tabular}{|l|l|}\n")
            vm.write("\\hline\n")
            vm.write("\\textbf{Component} & \\textbf{Cryptographic Certificate (SHA-256)} \\\\\n")
            vm.write("\\hline\n")
            vm.write("\\multicolumn{2}{|c|}{\\textbf{Lean Theorems}} \\\\\n")
            vm.write("\\hline\n")
            for thm in manifest_data_macros.get("theorems", []):
                name_escaped = thm["name"].replace("_", "\\_")
                macro_name = make_macro_name(thm["name"])
                vm.write(f"\\texttt{{{name_escaped}}} & \\texttt{{\\{macro_name}}} \\\\\n")
            vm.write("\\hline\n")
            vm.write("\\multicolumn{2}{|c|}{\\textbf{Rust/Verus Implementations}} \\\\\n")
            vm.write("\\hline\n")
            for fn, h in manifest_data_macros.get("verus_hashes", {}).items():
                fn_escaped = fn.replace("_", "\\_")
                macro_name = make_macro_name(fn)
                vm.write(f"\\texttt{{{fn_escaped}}} & \\texttt{{\\{macro_name}}} \\\\\n")
            vm.write("\\hline\n")
            vm.write("\\end{tabular}\n")
            vm.write("\\caption{Cryptographic manifest of formally verified components.}\n")
            vm.write("\\label{tab:verification_manifest}\n")
            vm.write("\\end{table}\n")
