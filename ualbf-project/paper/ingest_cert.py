import json
import os
import sys

# Add parent directory to sys.path to import verify_certificate
sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))
try:
    from verify_cert import verify_certificate
except ImportError as e:
    print(f"Error importing verify_certificate: {e}")
    sys.exit(1)

cert_path = os.getenv("UALBF_CERT_PATH", "../rust-engine/formal_certificate.json")
manifest_path = os.getenv("UALBF_MANIFEST_PATH", "../rust-engine/proof_manifest.json")

if not os.path.exists(cert_path):
    print(f"Warning: {cert_path} not found. Proceeding with dummy values.")
    with open("telemetry.tex", "w") as f:
        f.write("\\newcommand{\\TelemetryPhaseTwoTime}{0}\n")
        f.write("\\newcommand{\\TelemetryPhaseTwoBranches}{0}\n")
        f.write("\\newcommand{\\TelemetryPruned}{0}\n")
        f.write("\\newcommand{\\TelemetryMaxLog}{37}\n")
        f.write("\\newcommand{\\TelemetryCertHash}{000000000000}\n")
    sys.exit(0)

try:
    cert = verify_certificate(cert_path, manifest_path)
except Exception as e:
    print(f"Verification Failed: {e}")
    sys.exit(1)

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

