# UALBF Paper Updates Checklist

## 1. Missing Theoretical Results
- [ ] Add a new section or subsection detailing the **Prasad-Sunitha Bound** ($\omega(N) \ge 15$ when $\gcd(N, 15) = 1$).
- [ ] Cite the Lean 4 proof `qpn_coprime_15_omega_15` located in `SpecialFactors.lean`.
- [ ] Contrast this with the older Hagis and Cohen bound ($\omega(N) \ge 7$) currently mentioned in the introduction/results.

## 2. Missing Computational Engine Details
- [x] Explain the **Z3 CDCL Pruner**: Document how it detects Zsigmondy traps and target abundance starvation using dependency learning.
- [x] Document **LLL Lattice Diophantine Pruning**: Explain how arbitrary-precision reductions (`rug::Integer`) are used to shape the top of the search tree (depths 3-6) early.
- [x] Describe the **Lock-Free Concurrency & Telemetry**: Detail how Rayon is utilized dynamically and how the lock-free state drives the active-primes output.
- [x] Note the **Dynamic Minimum Factors**: Document that the search floor dynamically shifts (e.g., from 7 to 15) during deep exploration when constraints are met.

## 3. Fill in `[PLACEHOLDER]` Tags
- [ ] **Section 5 (Methodology)**: Replace `[PLACEHOLDER: Detail the Rust-based approach for traversing the search space.]` with concrete DFS details.
- [x] **Section 5.2 (Ray-Casting)**: Replace `[PLACEHOLDER: Explain the ray-cast strategy...]` with the algebraic modular $\mathcal{O}(1)$ targeting via `mod_inverse_128` (Lean FFI) and exact sieving.
- [ ] **Section 6 (Results Overview)**: Replace `[PLACEHOLDER: Present the computational limits reached and the verification strategy.]` with actual bounds metrics.
- [ ] **Section 6.2 (Computational Bounds Achieved)**: Replace `[PLACEHOLDER: State the current lower bounds for $N$ and the number of distinct prime factors.]` with the engine's highest verified bounds and zero panics achievement.

## 4. Formatting & Argument Flow
- [ ] Directly map the formalized Lean lemmas (like `rust_sieve_soundness`) to their exact algorithmic counterparts in Rust (`generate_illegal_z_valuations`).
- [ ] Emphasize that the Rust engine is free of integer overflows (up to 128-bit verified arithmetic via Lean FFI) and lock contention to highlight strict methodological correctness.
- [ ] (Future) Add a note in the conclusion addressing the formalization of the modulo 3 parity gap for $N \equiv 0 \pmod 3$.
