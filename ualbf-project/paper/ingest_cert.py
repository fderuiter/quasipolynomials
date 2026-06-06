import json
import os
import sys

cert_path = os.getenv("UALBF_CERT_PATH", "../rust-engine/formal_certificate.json")
if not os.path.exists(cert_path):
    print(f"Warning: {cert_path} not found. Proceeding with dummy values.")
    with open("telemetry.tex", "w") as f:
        f.write("\\newcommand{\\TelemetryPhaseTwoTime}{0}\n")
        f.write("\\newcommand{\\TelemetryPhaseTwoBranches}{0}\n")
        f.write("\\newcommand{\\TelemetryPruned}{0}\n")
        f.write("\\newcommand{\\TelemetryMaxLog}{37}\n")
        f.write("\\newcommand{\\TelemetryCertHash}{000000000000}\n")
    sys.exit(0)

with open(cert_path, "r") as f:
    cert = json.load(f)

tel = cert["telemetry"]
time_ms = tel["phase2_execution_time_ms"]
branches = tel["total_branches_searched"]
pruned = tel.get("abundance_pruned", branches)
max_log = tel["target_max_log10"]

with open("telemetry.tex", "w") as f:
    f.write(f"\\newcommand{{\\TelemetryPhaseTwoTime}}{{{time_ms / 1000:.2f}}}\n")
    f.write(f"\\newcommand{{\\TelemetryPhaseTwoBranches}}{{{branches:,}}}\n")
    f.write(f"\\newcommand{{\\TelemetryPruned}}{{{pruned:,}}}\n")
    f.write(f"\\newcommand{{\\TelemetryMaxLog}}{{{max_log}}}\n")
    f.write(f"\\newcommand{{\\TelemetryCertHash}}{{{cert['manifest_hash'][:12]}}}\n")
    
    baseline = tel.get("baseline_min_prime_factors", 7)
    ps_bound = tel.get("prasad_sunitha_bound", 16)
    f.write(f"\\newcommand{{\\TelemetryBaselineMinPrimeFactors}}{{{baseline}}}\n")
    f.write(f"\\newcommand{{\\TelemetryPrasadSunithaBound}}{{{ps_bound}}}\n")

