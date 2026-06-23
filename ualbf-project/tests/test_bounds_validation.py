import json
import os
import subprocess
import tempfile

def test_pruning_bound_not_greater_than_justified_bound():
    bounds_path = os.path.join(os.path.dirname(__file__), "..", "bounds_manifest.json")
    with open(bounds_path, "r") as f:
        bounds = json.load(f)
        
    ps = bounds["omega_bounds"]["prasad_sunitha"]
    proof_bound = ps["proof_bound"]
    gap = ps["engine_justified_gap"]
    justified_bound = proof_bound + gap
    
    # The rust engine uses PRASAD_SUNITHA_BOUND_NO_3_5 which is generated in manifest_constants.rs
    constants_path = os.path.join(os.path.dirname(__file__), "..", "rust-engine", "src", "manifest_constants.rs")
    engine_bound = None
    with open(constants_path, "r") as f:
        for line in f:
            if "PRASAD_SUNITHA_BOUND_NO_3_5" in line:
                engine_bound = int(line.split("=")[1].strip().strip(";"))
                break
                
    assert engine_bound is not None
    assert engine_bound <= justified_bound, f"Engine bound {engine_bound} is strictly greater than the justified bound {justified_bound}"

def test_formal_cert_rejection():
    # If PRASAD_SUNITHA_BOUND_NO_3_5 > PRASAD_SUNITHA_PROOF_BOUND, the engine should skip certificate generation
    # We can check the source code of main.rs to ensure the validation logic is present
    main_path = os.path.join(os.path.dirname(__file__), "..", "rust-engine", "src", "main.rs")
    
    found_check = False
    with open(main_path, "r") as f:
        content = f.read()
        if "manifest_constants::PRASAD_SUNITHA_BOUND_NO_3_5 > manifest_constants::PRASAD_SUNITHA_PROOF_BOUND" in content:
            if "skip_cert = true" in content and "reject" in content.lower():
                found_check = True

    assert found_check, "Automated test failed: main.rs does not contain logic to reject 'Formal' certificates when the engine bound exceeds the proven limit."

