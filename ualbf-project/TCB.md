# Trusted Computing Base (TCB) & Verification Boundaries

This document defines the Trusted Computing Base (TCB) for the Unified Algebraic-Lattice Bipartition Framework (UALBF). To maintain transparency and strict mathematical certitude, we explicitly disclose the boundaries of our formally verified claims. The components listed below act as unverified external blocks, FFI boundaries, or trusted mathematical assumptions rather than mechanically checked proofs.

## 1. Lean-to-Rust FFI Boundary
The Foreign Function Interface (FFI) bridging the Lean 4 formalization and the Rust execution engine is unverified.
- **Current State:** The Rust execution engine relies on C-compatible data serialization and exported semantics via Lean's `@[export]` pragmas.
- **Verification Status:** While the individual Lean 4 proofs are mechanically checked and the Rust execution logic is highly robust, the bridging logic across the boundary itself forms a critical part of the TCB and is not formally proven.

## 2. Miller-Rabin Sufficiency Assumption
Deterministic primality testing within the search engine relies on `lemma_mr_bases_sufficient` to assert that a fixed set of 20 prime bases is strictly sufficient to test all numbers within the 256-bit integer domain.
- **Current State:** `lemma_mr_bases_sufficient` is an empty proof placeholder within the codebase (`{}`).
- **Verification Status:** This is reclassified as a trusted, unverified mathematical assumption. It is not a completed formal proof.

## 3. GPU Pollard's Rho Pipeline (Inactive)
The repository contains a highly parallelized batch-factorization GPU Pollard's Rho pipeline, implemented in Apple Metal (`rust-engine/src/gpu.rs`).
- **Current State:** This pipeline is completely bypassed in the active paths. High-performance execution relies entirely on sequential CPU loops.
- **Verification Status:** The GPU pipeline operations are unverified. They are not active during the main verified search processes and form no part of the end-to-end verification claims.

---
By explicitly defining these boundaries, future research contributors can better identify current verification gaps and contribute meaningful proofs to the repository.
