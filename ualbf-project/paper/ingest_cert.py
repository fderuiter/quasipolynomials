import json
import os
import sys

# Add parent directory to sys.path so we can import cert_util
sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import cert_util


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
        f.write("\\newcommand{\\TelemetryMaxLog}{37}\n")
        f.write("\\newcommand{\\TelemetryMinLog}{35}\n")
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

    bounds_path = os.path.join(os.path.dirname(os.path.dirname(__file__)), "bounds_manifest.json")
    if os.path.exists(bounds_path):
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
            
        with open(bounds_path, "r") as bf:
            bounds = json.load(bf)
        ps_bound = bounds["omega_bounds"]["prasad_sunitha"]["proof_bound"] + bounds["omega_bounds"]["prasad_sunitha"]["engine_justified_gap"]
        baseline = bounds["omega_bounds"]["baseline"]["proof_bound"] + bounds["omega_bounds"]["baseline"]["engine_justified_gap"]
    else:
        baseline = tel.get("baseline_min_prime_factors", 7)
        ps_bound = tel.get("prasad_sunitha_bound", 15)
        
    f.write(f"\\newcommand{{\\TelemetryBaselineMinPrimeFactors}}{{{baseline}}}\n")
    f.write(f"\\newcommand{{\\TelemetryPrasadSunithaBound}}{{{ps_bound}}}\n")
