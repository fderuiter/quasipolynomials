# Lean 4 Proofs TODO: Resolving `sorry` declarations in `UALBF/Abundancy.lean`

This document provides a systematic checklist and technical breakdown for eliminating the remaining `sorry` declarations in `UALBF/Abundancy.lean`.

## Issue 1: `abundancy_le_totient_ratio` (Line 44)

**Current State**:
```lean
theorem abundancy_le_totient_ratio {N : ℕ} (hN : N > 1) :
  abundancy_index N < (N : ℚ) / (N.totient : ℚ) := by sorry
```

**Mathematical Objective**:
Prove that the Abundancy Index $H(N) = \frac{\sigma(N)}{N}$ is strictly bounded by the Euler ratio $\frac{N}{\varphi(N)}$ for any integer $N > 1$.

**Resolution Strategy & Steps**:
- [ ] **Step 1: Clear Denominators**  
  Translate the goal from the field of Rationals (`ℚ`) to Natural numbers (`ℕ`). Since $N > 1$, both $N$ and $\varphi(N)$ are strictly positive. Use `Rat.div_lt_div_iff` or equivalent cast mechanics to rewrite the goal as:  
  `sigma N * N.totient < N^2`
- [ ] **Step 2: Decompose over Prime Factors**  
  Both the divisor sum $\sigma(N)$ and Euler's totient $\varphi(N)$ are multiplicative functions. Rewrite $N$, $\sigma(N)$, and $\varphi(N)$ using `Finset.prod` over `N.primeFactors`.
- [ ] **Step 3: Establish Local Prime Power Bound**  
  Create and prove a helper lemma showing that the strict inequality holds algebraically for any valid prime power:
  ```lean
  lemma sigma_mul_totient_prime_pow {p k : ℕ} (hp : p.Prime) (hk : k > 0) :
    sigma (p^k) * (p^k).totient < p^(2*k)
  ```
  *Proof sketch*: Substitute $\varphi(p^k) = p^k - p^{k-1}$. The algebraic expansion becomes $(p^{2k+1} - p^{k-1}) / (p-1)$, which simplifies or directly bounds to strictly less than $p^{2k}$.
- [ ] **Step 4: Aggregate with `Finset.prod_lt_prod`**  
  Map the local helper lemma across `N.primeFactors`. Because $N > 1$, `N.primeFactors.Nonempty` is true, ensuring there is at least one strictly bounded term. The overall product then preserves the strict `<` inequality mapping back to the target goal.

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
