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

## Issue 2: `qpn_totient_bound` (Line 55)

**Current State**:
```lean
theorem qpn_totient_bound {N : ℕ} (h_qpn : IsQuasiperfect N) (h_size : N > 10^35) : 
  (N : ℚ) / (N.totient : ℚ) < 2.4675 := by sorry
```

**Mathematical Objective**:
Establish an absolute global ceiling of `2.4675` on the Euler ratio for Quasiperfect Numbers exceeding $10^{35}$.

**Resolution Strategy & Steps**:
- [ ] **Step 1: Address Missing Hypotheses**  
  The theorem's comment claims the bound follows from $\gcd(N, 15) = 1$ (via `qpn_coprime_15_omega_15`). However, `N.gcd 15 = 1` is **not** stated as a hypothesis.  
  *Action Required*: Either add `(h_coprime : N.gcd 15 = 1)` as a hypothesis, or provide a bridging lemma proving that $N > 10^{35}$ implies $\gcd(N, 15) = 1$ for Quasiperfect Numbers.
- [ ] **Step 2: Formalize the `2.4675` Arithmetic Limit**  
  The number `2.4675` approximates the cumulative product $\prod \frac{p}{p-1}$ for the first 15 primes strictly greater than $5$ (i.e., starting at $7$). 
  *Action Required*: Create a discrete evaluator function or explicit list product computation that verifies:
  ```lean
  lemma max_totient_ratio_15_primes : 
    (cubeCPrimes.take 15).foldl (fun acc p => acc * (p : ℚ) / (p - 1)) 1 < 2.4675
  ```
- [ ] **Step 3: Reconcile $\omega(N)$ upper vs. lower bounds**  
  The Euler ratio $\frac{N}{\varphi(N)}$ grows strictly larger as we multiply in more unique prime factors. 
  If `qpn_coprime_15_omega_15` forces $\omega(N) \ge 15$, the 15-prime product is the *minimum* structural threshold, not the maximum. To force a strict upper bound (`< 2.4675`), we must also logically cap the total number of prime roots $\omega(N)$ allowed, or prove convergence limits for $\sigma(N)/N \approx 2$ blocking extended prime chains.
  *Action Required*: Complete the algebraic squeeze bridging the local DFS assumption to formal Lean bounds using `abundancy_starvation` context.

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

