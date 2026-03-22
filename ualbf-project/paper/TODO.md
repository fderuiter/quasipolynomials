# Formal Paper Writeup TODOs

This comprehensive checklist covers all the narrative, mathematical, computational, and formatting tasks required to finalize the `main.tex` writeup for the Unified Algebraic-Lattice Bipartition Framework (UALBF).

## 1. Introduction & Context
- [x] **Historical Context of QPNs**: Summarize previous work and established bounds (e.g., Cattaneo, Hagis, Cohen).
- [x] **Motivation for UALBF**: Explain the necessity of merging formal verification (Lean 4) with high-performance search heuristics (Rust).
- [x] **Paper Contributions**: Clearly list our specific bounds, the formalized parity lemmas, and the exact valuation ray-cast strategy.
- [x] **Update `\section{Introduction}`**: Replace the `[PLACEHOLDER]` block with the synthesized context.

## 2. Mathematical Foundations
- [x] **QPN Definition**: Formally define a Quasiperfect Number using the abundancy index: $\sigma(N) = 2N + 1$.
- [x] **Properties of $\sigma$**: Detail the multiplicativity of the sum-of-divisors function for mutually coprime factors (as constrained and proved in `UALBF/Basic.lean`).
- [x] **Parity of Sigma**: Detail the proof that $\sigma(N)$ is odd if and only if $N$ is a perfect square or twice a perfect square (`odd_sigma_iff_square_or_double_square`).
- [x] **Factorization Lemma**: Explain the relationship between prime exponent parities and square/double-square structures (`factorization_even_iff_square_or_double_square`).
- [x] **Modulo 8 Obstructions**: Explain quadratic reciprocity constraints and how the Legendre symbol restricts prime factors of $N$.
- [x] **Update `\section{Mathematical Foundations}`**: Replace all `[PLACEHOLDER]` tags in subsections 3.1, 3.2, and 3.3.

## 3. The Unified Algebraic-Lattice Bipartition Framework
- [x] **Bipartition Definition**: Formally define the split of the search space $N$ into a prefix $N_L$ and a suffix $N_R$, guaranteeing $\gcd(N_L, N_R) = 1$.
- [x] **Coprimality Guarantee**: Detail the formal proof that $\gcd(N_L, \sigma(N_L)) = 1$ derived structurally from the QPN equation (`prefix_sigma_coprime` in `UALBF/Bipartition.lean`).
- [x] **Contradiction on Double Squares**: Present the finalized proof showing a QPN cannot be a double square ($N \neq 2m^2$) by leveraging modulo 3 arguments (`qpn_not_double_square`).
- [x] **Exact Valuation & Divisibility**: Explain the fundamental valuation condition: $p^{2e} \parallel N \implies \sigma(p^{2e}) \mid \sigma(N)$ (`exact_val_sigma_dvd` in `UALBF/Valuation.lean`).
- [x] **Update `\section{The Unified Algebraic-Lattice Bipartition Framework}`**: Replace `[PLACEHOLDER]` blocks in section 4.

## 4. Computational Methodology (Rust Engine)
- [ ] **Architecture Overview**: Map the Lean 4 mathematical framework to the Rust orchestration pipeline (Sieve $\rightarrow$ DFS Prefix $\rightarrow$ Raycast).
- [ ] **Sieve of Eratosthenes & Primes**: Discuss `sieve.rs` limits, prime indexing bounds, and caching mechanisms.
- [ ] **DFS Prefix Tree**: Explain the prefix lattice in `dfs_tree.rs`, emphasizing how early pruning via exact valuations avoids combinatorial explosions.
- [ ] **Ray-Casting Algorithm**: Describe the constant-time $\mathcal{O}(1)$ ray-cast implementation (`raycast.rs`). Explicitly connect the Lean 4 `prefix_sigma_coprime` theorem to the panic-free guarantee of the modular inverse subroutine.
- [ ] **Algorithmic Optimizations**: Document the internal use of Pollard's Rho, Tonelli-Shanks, Hensel's Lift, and CRT in `math_utils.rs`.
- [ ] **Multithreading & Performance Details**: Detail the parallel execution features added to the engine, analyzing worker-thread utilization and speedups.
- [ ] **Update `\section{Computational Methodology}`**: Erase `[PLACEHOLDER]` markers and flesh out section 5 and its subsections.

## 5. Verification & Results
- [ ] **Lean 4 Integration Strategy**: Explicitly argue how Lean mechanically enforces the assumptions the Rust engine relies on, creating a verified computational pipeline devoid of false positives.
- [ ] **Current Search Limits**: State the final computed lower bounds for $N$ and the minimum number of distinct prime factors achieved by our infrastructure.
- [ ] **Performance Benchmarks**: Document empirical execution logs, phase completion times, metrics (Retained vs. Pruned), and memory use.
- [ ] **Update `\section{Results and Verification}`**: Include metrics from `engine_trace.log` and populate placeholders in section 6.

## 6. Conclusion & Future Work
- [ ] **Summary of Project**: Recap how the UALBF simplifies the search for QPNs via verified algebraic reductions.
- [ ] **Future Directions**: Discuss potential pathways for completely closing the modulo space gaps (such as $N \equiv 0 \pmod 3$) to constrain QPN topologies even further.
- [ ] **Update `\section{Conclusion and Future Work}`**: Polish the concluding remarks.

## 7. Writing Mechanics & Formatting
- [ ] **Proofread LaTeX Syntax**: Verify all math environments, align blocks, congruence signs, and exponent formatting.
- [ ] **Update Lean Snippets**: Ensure `minted` code blocks in LaTeX point to the absolute latest, `sorry`-free Lean implementations.
- [ ] **Compile Citations**: Fill out `references.bib` with actual citations for Lean 4, mathematical predecessors, algorithms (Pollard's Rho), etc.
- [ ] **Cross-references**: Ensure `\cref` and `\ref` tags are wired correctly and not broken.

## 8. Audit-Identified Discrepancies (2026-03-22)

- [ ] **D1: Paper claims O(1) ray-cast; code does O(c_max) iteration**
  - §3.1 / §5.2 claim "an O(1) ray-cast shortcut." In reality, `raycast.rs:72` iterates `c in c_min..=c_max`, which is `O(z_max / σ(N_L))` — potentially millions of iterations per root. Correct the complexity claim or clarify that O(1) refers to the modular-inverse step only.

- [ ] **D4: Lean listing has wrong type signature**
  - `main.tex` line 417 shows `(hn : n ≠ 0)` but `Basic.lean:279` has `(hn : n > 0)`. Update the listing to match the actual Lean code.

- [ ] **D2: Prefix-sigma coprimality caveat**
  - The paper proves `gcd(N_L, σ(N_L)) = 1` assuming a full QPN bipartition exists (Theorem 4). But the Rust engine invokes `mod_inverse` on *partial* prefixes where no valid suffix may exist. The code handles this gracefully via `if let Some(...)`, but the paper should note that the coprimality guarantee only holds conditionally — the code's fallback is the `None` branch, not a panic.

- [ ] **D3: Document the exact mapping between components and exact valuations**
  - The paper formalises $p^{2e} \| N$ (exact valuation), but the Rust engine treats `PrimePower` as a fixed `(p, 2e)` component added to the prefix. The implicit assumption that the QPN has *exactly* this valuation for each prefix prime should be stated explicitly in the Computational Methodology section.
