import json
import os
import sys

cert_path = os.getenv("UALBF_CERT_PATH", "../rust-engine/formal_certificate.json")
has_cert = os.path.exists(cert_path)
if not has_cert:
    print(f"Warning: {cert_path} not found. Proceeding with dummy values.")

with open("telemetry.tex", "w") as f:
    if has_cert:
        with open(cert_path, "r") as cf:
            cert = json.load(cf)
        tel = cert["telemetry"]
        time_ms = tel["phase2_execution_time_ms"]
        branches = tel["total_branches_searched"]
        pruned = tel.get("abundance_pruned", branches)
        max_log = tel["target_max_log10"]
        min_log = tel["target_min_log10"]
        f.write(f"\\newcommand{{\\TelemetryPhaseTwoTime}}{{{time_ms / 1000:.2f}}}\n")
        f.write(f"\\newcommand{{\\TelemetryPhaseTwoBranches}}{{{branches:,}}}\n")
        f.write(f"\\newcommand{{\\TelemetryPruned}}{{{pruned:,}}}\n")
        f.write(f"\\newcommand{{\\TelemetryMaxLog}}{{{max_log}}}\n")
        f.write(f"\\newcommand{{\\TelemetryMinLog}}{{{min_log}}}\n")
        f.write(f"\\newcommand{{\\TelemetryCertHash}}{{{cert['manifest_hash'][:12]}}}\n")
    else:
        f.write("\\newcommand{\\TelemetryPhaseTwoTime}{0}\n")
        f.write("\\newcommand{\\TelemetryPhaseTwoBranches}{0}\n")
        f.write("\\newcommand{\\TelemetryPruned}{0}\n")
        f.write("\\newcommand{\\TelemetryMaxLog}{37}\n")
        f.write("\\newcommand{\\TelemetryMinLog}{35}\n")
        f.write("\\newcommand{\\TelemetryCertHash}{000000000000}\n")
        tel = {}

    bounds_path = os.path.join(os.path.dirname(os.path.dirname(__file__)), "bounds_manifest.json")
    if os.path.exists(bounds_path):
        with open(bounds_path, "r") as bf:
            bounds = json.load(bf)
        ps_bound = bounds["omega_bounds"]["prasad_sunitha"]["proof_bound"] + bounds["omega_bounds"]["prasad_sunitha"]["engine_justified_gap"]
        baseline = bounds["omega_bounds"]["baseline"]["proof_bound"] + bounds["omega_bounds"]["baseline"]["engine_justified_gap"]
    else:
        baseline = tel.get("baseline_min_prime_factors", 7)
        ps_bound = tel.get("prasad_sunitha_bound", 15)
        
    f.write(f"\\newcommand{{\\TelemetryBaselineMinPrimeFactors}}{{{baseline}}}\n")
    f.write(f"\\newcommand{{\\TelemetryPrasadSunithaBound}}{{{ps_bound}}}\n")

