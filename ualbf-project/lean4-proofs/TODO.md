# Lean 4 Proofs TODO: Resolving `sorry` declarations

This document provides a systematic checklist and technical breakdown for eliminating the remaining `sorry` declarations in the UALBF Lean 4 project.

## Issue 1: `abundancy_le_totient_ratio` (Line 44)

**Current State**:
```lean
theorem abundancy_le_totient_ratio {N : ℕ} (hN : N > 1) :
  abundancy_index N < (N : ℚ) / (N.totient : ℚ) := by sorry
```

**Mathematical Objective**:
Prove that the Abundancy Index $H(N) = \frac{\sigma(N)}{N}$ is strictly bounded by the Euler ratio $\frac{N}{\varphi(N)}$ for any integer $N > 1$.

**Resolution Strategy & Steps**:
- [x] **Step 1: Clear Denominators**  
  Translate the goal from the field of Rationals (`ℚ`) to Natural numbers (`ℕ`). Since $N > 1$, both $N$ and $\varphi(N)$ are strictly positive. Use `div_lt_div_iff₀` to rewrite the goal as:  
  `sigma N * N.totient < N * N`  (equivalently `N^2`)
- [x] **Step 2: Combine Cross Bound with Euler Identity**  
  Reuse `SpecialFactors.abundancy_cross_bound` (σ(N)·∏(p-1) < N·∏p) and multiply by φ(N), then substitute `Nat.totient_mul_prod_primeFactors` (φ(N)·∏p = N·∏(p-1)) to get σ(N)·φ(N)·∏(p-1) < N²·∏(p-1).
- [x] **Step 3: Cancel ∏(p-1)**  
  Since ∏(p-1) > 0 (all prime factors ≥ 2), cancel via `Nat.lt_of_mul_lt_mul_right` to obtain σ(N)·φ(N) < N².
- [x] **Step 4: Lift to ℚ**  
  Cast the ℕ inequality to ℚ via `exact_mod_cast` and close the goal.

---

## Issue 2: `qpn_totient_bound` (Line 89)

**Current State**:
```lean
theorem qpn_totient_bound {N : ℕ} (h_qpn : IsQuasiperfect N) (h_size : N > 10^35) : 
  (N : ℚ) / (N.totient : ℚ) < 2.4675 := by sorry
```

**Mathematical Objective**:
Establish an absolute global ceiling of `2.4675` on the Euler ratio $N/\varphi(N)$ for Quasiperfect Numbers exceeding $10^{35}$.

### Critical Corrections to Previous Analysis

> **⚠ The original Steps 2 & 3 below contained mathematical errors.** Deep analysis reveals:
>
> - **Step 2 was wrong**: `2.4675` is **not** the product $\prod p/(p-1)$ for 15 primes ≥ 7.
>   `abundancy_cube_c_lt_two` already proves the 14-prime product is **< 2**, and adding a
>   15th prime (61) gives ≈ **2.027**. The constant `2.4675` has enormous slack.
>
> - **Step 3 was confused**: The Euler ratio grows with more prime factors, YES — but it is
>   **not** unbounded. The constraint $\sigma(N)/N = 2 + 1/N$ for QPNs tightly couples
>   $N/\varphi(N)$ to the correction factor $\prod p^{v_p+1}/(p^{v_p+1}-1)$, which converges
>   to ≈ 1.005. The actual bound is $N/\varphi(N) < 2.011$, far below 2.4675.

### Correct Mathematical Structure

The Euler ratio decomposes multiplicatively as:
$$\frac{N}{\varphi(N)} = \prod_{p \mid N} \frac{p}{p-1} = \frac{\sigma(N)}{N} \times \prod_{p \mid N} \frac{p^{v_p+1}}{p^{v_p+1}-1}$$

where $v_p = v_p(N)$ is the $p$-adic valuation. This follows from the identity:
$$\frac{p}{p-1} = \frac{\sigma(p^v)}{p^v} \times \frac{p^{v+1}}{p^{v+1}-1}$$

For QPNs:
- $\sigma(N)/N = 2 + 1/N$ (by definition)
- $N$ is an odd square (`qpn_is_odd_square`), so all $v_p$ are **even ≥ 2**
- With `gcd(N,15) = 1`, all primes $p \geq 7$ (`qpn_coprime_15_primes_ge_7`)

Therefore each correction factor satisfies:
$$\frac{p^{v_p+1}}{p^{v_p+1}-1} \leq \frac{p^3}{p^3-1} \leq \frac{343}{342} \approx 1.00292$$

since $v_p + 1 \geq 3$ and $x/(x-1)$ is decreasing for $x > 1$.

The **full correction product** is bounded by:
$$\prod_{p \mid N} \frac{p^3}{p^3-1} \leq \prod_{\substack{p \text{ prime} \\ p \geq 7}} \frac{p^3}{p^3-1} = \frac{\zeta(3)}{\prod_{p \in \{2,3,5\}} \frac{1}{1-p^{-3}}} \approx 1.20206 \times 0.8355 \approx 1.00428$$

So: $N/\varphi(N) < (2 + 10^{-35}) \times 1.005 < 2.011 \ll 2.4675$.

### Resolution Strategy & Steps

- [ ] **Step 1: Add Missing Hypothesis**  
  Add `(h_coprime : N.gcd 15 = 1)` to the theorem signature. This is necessary and honest —
  the 2.4675 bound genuinely requires coprimality with 15. Downstream callers (the Rust DFS
  engine) supply this from their validated search context.  
  ```lean
  theorem qpn_totient_bound {N : ℕ} (h_qpn : IsQuasiperfect N) (h_size : N > 10^35)
      (h_coprime : N.gcd 15 = 1) : 
    (N : ℚ) / (N.totient : ℚ) < 2.4675 := by sorry
  ```

- [ ] **Step 2: Prove the Multiplicative Decomposition Lemma**  
  Formalize the identity linking N/φ(N) to σ(N)/N:  
  ```lean
  lemma totient_ratio_eq_sigma_times_correction {N : ℕ} (hN : N > 1) :
      (N : ℚ) / (N.totient : ℚ) = 
      (sigma N : ℚ) / (N : ℚ) * ∏ p ∈ N.primeFactors, 
        (p ^ (N.factorization p + 1) : ℚ) / (p ^ (N.factorization p + 1) - 1) := by
  ```
  This follows from the identity $p/(p-1) = \sigma(p^v)/p^v \times p^{v+1}/(p^{v+1}-1)$
  applied multiplicatively over all prime factors.

- [ ] **Step 3: Bound the Correction Factor**  
  There are **two viable proof paths** (choose one):

  **Path A — Finite Truncation + Tail Bound** *(rigorous, hard to formalize)*:  
  Compute $\prod_{p=7}^{61} p^3/(p^3-1)$ explicitly via `norm_num` (≈ 1.00472), then bound
  $\prod_{p > 61} p^3/(p^3-1) < 1 + 1/2178$ using:
  - $\sum_{p > 61} 1/p^3 < \int_{60}^{\infty} x^{-3}\,dx = 1/7200$
  - $\prod(1+x_i) \leq e^{\sum x_i}$ and $e^x < 1+2x$ for $x < 0.01$
  
  **Difficulty**: Formalizing $e^x$, integrals, and infinite products in Lean/Mathlib is
  currently very hard. Would require `Mathlib.Analysis.SpecificLimits`.

  **Path B — Crude Algebraic Bound** *(simpler, fully mechanizable)*:  
  Use the fact that each factor $\leq 343/342$ and bound $\omega(N)$ from the σ constraint:
  - From $\sigma(N)/N = 2 + 1/N$ and each $\sigma(p^v)/p^v \geq 1 + 1/p$:
    $\prod(1 + 1/p_i) \leq 2 + 1/N$
  - For the 18 smallest primes ≥ 7: $\prod(1+1/p) \approx 2.014 > 2.001$
  - But with large primes, $\prod(1+1/p)$ stays small, so $\omega(N)$ isn't tightly bounded
  - Instead: use $N/\varphi(N) < \sigma(N)/N \times (343/342)^{\omega(N)}$, then bound
    $\omega(N) \leq \lfloor\log_{49}(N)\rfloor$ from $N \geq \prod p_i^2 \geq 49^{\omega}$
  - For $N < 10^{1000}$: $\omega \leq 592$, giving $(343/342)^{592} \times 2.001 \approx 11.6$
    — too loose! This path only works with a tighter $\omega$ bound via σ constraints.
  
  **Recommended refinement for Path B**: Show directly from $\sigma(N)/N < 3$ (trivially)
  and the explicit factored form that $N/\varphi(N)/(\sigma(N)/N) < 1.005$ by computing
  the first 15 factors of $p^3/(p^3-1)$ via `norm_num` and noting the tail is negligible.

  **Path C — Establish Vacuous Truth** *(elegant if provable)*:  
  Show that no QPNs with `gcd(N,15) = 1` and $N > 10^{35}$ exist at all. Evidence:
  - With $\omega(N) \geq 15$ and all $v_p \geq 2$:
    $\sigma(N)/N \geq \prod_{\text{15 smallest primes} \geq 7} (1+1/p+1/p^2) \approx 2.017$
  - But $\sigma(N)/N = 2 + 1/N < 2 + 10^{-35} \approx 2.000$
  - So $2.017 \leq 2.000$: **contradiction** (if all 15 primes are smallest ≥ 7)
  - **Caveat**: This only works when the primes ARE the smallest. With larger primes
    (some $p > 61$), the product $(1+1/p+1/p^2)$ per factor decreases, potentially
    allowing consistency. So vacuous truth requires a more careful argument about which
    prime configurations are realizable.

- [ ] **Step 4: Assemble the Final Proof**  
  Chain the decomposition and correction bound:
  ```
  N/φ(N) = (σ(N)/N) × C
         = (2 + 1/N) × C
         < 2.001 × 1.005     -- for N > 10^35
         < 2.4675             -- by norm_num
  ```

### Key Numerical Reference Table

| Quantity | Value | Source |
|----------|-------|--------|
| $\prod_{k=1}^{14} p_k/(p_k-1)$ for $p \geq 7$ | < 2 | `abundancy_cube_c_lt_two` |
| $\prod_{k=1}^{15} p_k/(p_k-1)$ for $p \geq 7$ | ≈ 2.027 | Extends cubeCPrimes with 61 |
| $\prod_{k=1}^{22} p_k/(p_k-1)$ for $p \geq 7$ | ≈ 2.228 | First 22 primes ≥ 7 |
| $\prod_{p \geq 7} p^3/(p^3-1)$ (correction ceiling) | ≈ 1.00428 | $= \zeta(3) \prod_{p<7}(1-p^{-3})$ |
| $\prod_{k=1}^{15} (1+1/p+1/p^2)$ (min $\sigma$ bound) | ≈ 2.0172 | Smallest 15 primes ≥ 7, all $v=2$ |
| Actual $N/\varphi(N)$ for large QPNs | < 2.011 | $(2+\epsilon) \times 1.005$ |
| Stated bound | 2.4675 | ~23% headroom over actual |

### Dependencies

- `qpn_is_odd_square` (Basic.lean): All exponents even ≥ 2
- `qpn_coprime_15_primes_ge_7` (SpecialFactors.lean): All primes ≥ 7
- `qpn_coprime_15_omega_15` (SpecialFactors.lean): $\omega(N) \geq 15$
- `sigma_mul_totient_lt_sq` (Abundancy.lean): $\sigma(N) \cdot \varphi(N) < N^2$
- `Nat.totient_eq_prod_primeFactors` (Mathlib): $\varphi(N) = N \cdot \prod_{p|N} (1-1/p)$

---

## Issue 3: `sigma_prime_pow_cyclotomic` (Cyclotomic.lean) — ✅ RESOLVED

**Current State**: Proof completed, compiles successfully.

**Mathematical Objective**:
Prove that the sum of divisors function $\sigma(p^{2e}) = \sum_{k=0}^{2e} p^k = \frac{p^{2e+1}-1}{p-1}$ factors perfectly into the product of cyclotomic polynomials evaluated at $p$, for all divisors $d$ of $2e+1$ except $d=1$. This isolates the distinct algebraic factors bridging to Zsigmondy's theorem.

**Resolution Strategy & Steps**:
- [x] **Step 1: Rewrite $\sigma(p^{2e})$ as a Geometric Sum**  
  Used `sum_divisors_prime_pow` to rewrite $\sigma(p^{2e}) = \sum_{k=0}^{2e} p^k$.
- [x] **Step 2: Connect Geometric Sum to Polynomial Expansion**  
  Used `prod_cyclotomic_eq_geom_sum` which directly gives $\prod_{d | n, d \neq 1} \Phi_d(X) = \sum_{i<n} X^i$.
- [x] **Step 3: Extract the $d=1$ Term**  
  The `prod_cyclotomic_eq_geom_sum` already excludes $d=1$ via `divisors.erase 1`. Connected to `divisors \ {1}` via `sdiff_singleton_eq_erase`.
- [x] **Step 4: Handle ℤ to ℕ Coercions and Evaluation**  
  Evaluated the polynomial identity at `(p : ℤ)` using `eval_prod` and `eval_geom_sum`. Used `Int.natAbsHom` (`map_prod`) to distribute `natAbs` over the product. Used `cyclotomic_pos'` to establish positivity.

