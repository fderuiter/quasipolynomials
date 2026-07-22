# Trusted Computing Base (TCB) & Verification Boundaries

This document defines the Trusted Computing Base (TCB) for the Unified Algebraic-Lattice Bipartition Framework (UALBF). To maintain transparency and strict mathematical certitude, we explicitly disclose the boundaries of our formally verified claims. The components listed below act as unverified external blocks, FFI boundaries, or trusted mathematical assumptions rather than mechanically checked proofs.

## 1. Lean-to-Rust FFI Boundary
The Foreign Function Interface (FFI) bridging the Lean 4 formalization and the Rust execution engine is unverified.
- **Current State:** The Rust execution engine relies on C-compatible data serialization and exported semantics via Lean's `@[export]` pragmas.
- **Verification Status:** While the individual Lean 4 proofs are mechanically checked and the Rust execution logic is highly robust, the bridging logic across the boundary itself forms a critical part of the TCB and is not formally proven.

## 2. GPU Pollard's Rho Pipeline (Inactive)
The repository contains a highly parallelized batch-factorization GPU Pollard's Rho pipeline, implemented in Apple Metal (`rust-engine/src/unverified/gpu.rs`).
- **Current State:** This pipeline is completely bypassed in the active paths. High-performance execution relies entirely on sequential CPU loops.
- **Verification Status:** The GPU pipeline operations are unverified. They are not active during the main verified search processes and form no part of the end-to-end verification claims.

## 3. Bloom Filter Hashing Primitives
The Bloom filter's wrapping double-hashing logic is formally verified in Lean 4 to have zero false negatives. However, the underlying cryptographic (SHA-256) and multiplicative (FNV-1a) hash primitives that generate the initial hash seeds are excluded from formal verification.
- **Current State:** The Lean 4 formalization guarantees that the index generation step maps inputs securely to the bitset, but relies on Rust-side unverified implementations of SHA-256 and FNV-1a.
- **Verification Status:** The hash primitives themselves form part of the TCB and remain unverified.

## 4. 20-Base Miller-Rabin Sufficiency Axiom
The deterministic Miller-Rabin primality test utilized within the engine relies on the assumption that a specific set of 20 prime bases is sufficient to deterministically verify the primality of any integer up to 256 bits.
- **Current State:** The 20 prime bases are: 2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, and 71. The search engine checks candidate primes against these bases.
- **Verification Status:** The mathematical sufficiency of these 20 bases to guarantee deterministic primality up to 256 bits acts as a trusted mathematical assumption (axiom). Proving the underlying number-theoretic correctness of this theorem is explicitly outside the scope of formal verification; it is formally declared as an axiomatic assumption in the verification layer.

---
By explicitly defining these boundaries, future research contributors can better identify current verification gaps and contribute meaningful proofs to the repository.
