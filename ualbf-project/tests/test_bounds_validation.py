import json
import os


def test_pruning_bound_not_greater_than_justified_bound():
    bounds_path = os.path.join(os.path.dirname(__file__), "..", "bounds_manifest.json")
    with open(bounds_path, "r") as f:
        bounds = json.load(f)

    ps = bounds["omega_bounds"]["prasad_sunitha"]
    proof_bound = ps["proof_bound"]
    gap = ps["engine_justified_gap"]
    justified_bound = proof_bound + gap

    # The rust engine uses PRASAD_SUNITHA_BOUND_NO_3_5 which is generated in manifest_constants.rs
    constants_path = os.path.join(
        os.path.dirname(__file__), "..", "rust-engine", "src", "manifest_constants.rs"
    )
    engine_bound = None
    with open(constants_path, "r") as f:
        for line in f:
            if "PRASAD_SUNITHA_BOUND_NO_3_5" in line:
                engine_bound = int(line.split("=")[1].strip().strip(";"))
                break

    assert engine_bound is not None
    assert engine_bound <= justified_bound, (
        f"Engine bound {engine_bound} is strictly greater than the justified bound {justified_bound}"
    )
