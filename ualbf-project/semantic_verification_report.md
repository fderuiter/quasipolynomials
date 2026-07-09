# Semantic Verification Report

This report explicitly links implemented Rust functions to their corresponding Lean theorem proofs.

## 1. Pruning Starvation Logic
- **Lean Theorem:** `abundancy_starvation` in `AbundancyBound.lean`
- **Verus Specification:** `lean_abundancy_starvation_theorem` in `verus_proofs.rs`
- **Rust Implementation:** `check_starvation_kill` in `verus_proofs.rs`

## 2. Fixed-Point Scaling Logic
- **Lean Theorem:** `scaleBoundCeil_conservative` in `Fixed64.lean` (Provides the mathematical bridge proving that fixed-point integer rounding acts as a conservative upper bound for abstract rational multipliers)
- **Verus Specification:** `scale_bound_spec` in `verus_proofs.rs`
- **Rust Implementation:** `scale_bound_ceil` in `lean_ffi.rs`

## 3. Epistemological Memory Boundary
- **Lean FFI:** `ualbf_compute_sigma_ok` and `ualbf_cyclotomic_eval_ok`
- **Verus Specification:** `verified_ualbf_compute_sigma_ok` in `verus_proofs.rs`
- **Data Integrity:** Guarantees no null-pointer dereferences or unsentinel reads across the Lean/Rust FFI.
