# Lean 4 Proofs TODO: Resolving `sorry` declarations

One remaining `sorry` in the UALBF Lean 4 project: `qpn_totient_bound` in `Abundancy.lean`.

> Issues 1 (`abundancy_le_totient_ratio`) and 3 (`sigma_prime_pow_cyclotomic`) are resolved
> and compile successfully.

---

## `qpn_totient_bound` (Abundancy.lean, Line 89)

**Current State**:
```lean
theorem qpn_totient_bound {N : ℕ} (h_qpn : IsQuasiperfect N) (h_size : N > 10^35)
    (h_coprime : N.gcd 15 = 1) : 
  (N : ℚ) / (N.totient : ℚ) < 2.4675 := by sorry
```

**Goal**: Prove $N/\varphi(N) < 2.4675$ for quasiperfect $N > 10^{35}$.

### Key Identity

$$\frac{N}{\varphi(N)} = \frac{\sigma(N)}{N} \times \underbrace{\prod_{p \mid N} \frac{p^{v_p+1}}{p^{v_p+1}-1}}_{\text{correction factor } C}$$

For QPNs: $\sigma(N)/N = 2 + 1/N$, $N$ is an odd square (all $v_p$ even $\geq 2$),
and with $\gcd(N,15)=1$ all primes $p \geq 7$. Each correction term $\leq 343/342$.
The full product $C \approx 1.005$, giving $N/\varphi(N) < 2.011 \ll 2.4675$.

### Implementation Checklist

#### Phase 1: Theorem Signature Fix

- [x] Add `(h_coprime : N.gcd 15 = 1)` hypothesis to `qpn_totient_bound`
- [x] Update the docstring comment to reflect the coprimality requirement
- [x] Check no downstream callers break (grep for `qpn_totient_bound` across the project)
  - ✅ No downstream callers found — only referenced in a comment (line 45) and its own definition

#### Phase 2: Core Algebraic Identity

- [x] Prove the local prime-power identity as a standalone lemma:
  ```lean
  lemma euler_factor_decomp (p v : ℕ) (hp : p.Prime) (hv : v ≥ 1) :
      (p : ℚ) / (p - 1) = 
      (∑ k ∈ Finset.range (v + 1), (p : ℚ) ^ k) / (p : ℚ) ^ v *
      (p ^ (v + 1) : ℚ) / (p ^ (v + 1) - 1) := by
  ```
  - [x] Verify that `p/(p-1) = σ(p^v)/p^v × p^{v+1}/(p^{v+1}-1)` holds as a ℚ identity
  - [x] Handle the `p ≥ 2` positivity and `p^{v+1} - 1 ≠ 0` side goals

- [x] Lift to the global multiplicative identity:
  ```lean
  lemma totient_ratio_decomp {N : ℕ} (hN : N > 1) :
      (N : ℚ) / (N.totient : ℚ) = 
      abundancy_index N * ∏ p ∈ N.primeFactors, 
        (p ^ (N.factorization p + 1) : ℚ) / (p ^ (N.factorization p + 1) - 1) := by
  ```
  - [x] Show RHS = ∏ p/(p-1) via `euler_factor_decomp` at each prime factor
  - [x] Show LHS = ∏ p/(p-1) via `Nat.totient_mul_prod_primeFactors` + ℚ casting
  - [x] Handle ℕ→ℚ subtraction casting via `Nat.cast_sub` + `Nat.cast_one`

#### Phase 3: Correction Factor Bound

Choose **one** of these paths:

##### Path A: Finite computation + tail bound (hardest, most rigorous)

- [ ] Compute $\prod_{p=7}^{61} p^3/(p^3-1)$ as explicit ℚ via `norm_num`
  - [ ] Define the list: `[343/342, 1331/1330, 2197/2196, ..., 226981/226980]`
  - [ ] Verify product < 100472/100000 (i.e., < 1.00472) by `norm_num`/`decide`
- [ ] Bound the tail $\prod_{p > 61, \text{prime}} p^3/(p^3-1)$
  - [ ] Prove $\sum_{p>61} 1/p^3 < 1/7200$ (integral bound or explicit enumeration)
  - [ ] Prove $\prod(1+x_i) \leq 1/(1-\sum x_i)$ for $\sum x_i < 1$
  - [ ] Conclude tail < $1/(1 - 2/7200) < 1.0003$
- [ ] Combine: $C < 1.00472 \times 1.0003 < 1.006$
- [ ] **Difficulty**: Requires `Mathlib.Analysis.SpecificLimits` or custom infinite product bounding

##### Path B: ω(N) bound + per-factor bound — ❌ BROKEN (see [PATH_B_ANALYSIS.md](PATH_B_ANALYSIS.md))

**Per-factor bound is valid** ($343/342$ ceiling per prime), but **ω(N) is unbounded** without an a priori upper bound on $N$. The product $(343/342)^{\omega(N)}$ diverges for QPNs with many large prime factors, each contributing $(1+1/p) \approx 1$ to the σ constraint. See full analysis in PATH_B_ANALYSIS.md §3.

##### Path B Fixed: Telescoping sum approach — ✅ RECOMMENDED

Combines Path B's valid monotonicity with a convergent-sum argument in pure ℚ arithmetic.
No real analysis imports. See [PATH_B_ANALYSIS.md](PATH_B_ANALYSIS.md) §4–6 for full proof.

- [ ] Lemma 1: `cube_reciprocal_mono` — $p^{v+1}/(p^{v+1}-1) \leq p^3/(p^3-1)$ for $p \geq 7, v \geq 2$
- [ ] Lemma 2: `reciprocal_cube_comparison` — $1/(p^3-1) < 2/p^3$ for $p \geq 2$
- [ ] Lemma 3: `finset_sum_cube_reciprocal_bound` — For any Finset $S \subseteq [7,\infty)$:
  $\sum_{n \in S} 1/n^3 \leq 1/72$ (via telescoping: $1/n^3 \leq \frac{1}{2}(1/(n-1)^2 - 1/n^2)$)
- [ ] Lemma 4: `prod_one_plus_le_inv` — $\prod(1+x_i) \leq 1/(1-\sum x_i)$ for $x_i \geq 0, \sum x_i < 1$
  (Finset induction, pure ℚ, no Mathlib.Analysis)
- [ ] Lemma 5: Assembly — $C < 36/35$, then $(2+1/N) \times 36/35 < 2.059 < 2.4675$

##### Path C: Vacuous truth — ❌ ABANDONED (investigated, provably insufficient)

**Strategy**: Show no QPNs with $\gcd(N,15)=1$ exist for $N > 10^{35}$, making
`qpn_totient_bound` vacuously true via `False.elim`.

**Available tools**:
  - From `qpn_coprime_15_omega_15`: $\omega(N) \geq 15$
  - From `qpn_is_odd_square`: all $v_p$ even $\geq 2$
  - From `qpn_coprime_15_primes_ge_7`: all primes $p \geq 7$
  - QPN definition: $\sigma(N)/N = 2 + 1/N$

**The argument**: Since $\sigma$ is multiplicative and $v_p \geq 2$:
$$\sigma(N)/N = \prod_{p \mid N} \sigma(p^{v_p})/p^{v_p} \geq \prod_{p \mid N}(1 + 1/p + 1/p^2)$$
If this lower bound exceeds $2 + 1/N$ for every valid prime configuration,
we get a contradiction → no such QPN exists.

**Numerical investigation** (computed exactly in ℚ):

| Configuration | $\prod(1+1/p+1/p^2)$ | Exceeds 2? |
|---------------|----------------------|------------|
| 15 smallest primes $\geq 7$ | 2.0170 | ✅ |
| 14 smallest + $p = 10007$ | 1.9842 | ❌ |
| 13 smallest + 2 large | 1.9504 | ❌ |
| 12 smallest + 3 huge | 1.9136 | ❌ |
| 15 primes near $10^{17}$ | ≈ 1.0000 | ❌ |

**Critical threshold**: With the 14 smallest primes $\{7,...,59\}$,
$\prod_{k=1}^{14}(1+1/p_k+1/p_k^2) \approx 1.9840$. A 15th prime $q$ pushes
the product above 2 only when $1+1/q+1/q^2 > 2/1.984 \approx 1.0081$,
requiring $q \leq 10$. But $q$ must be prime, $\geq 7$, coprime to 15,
and distinct from the existing 14 — impossible.

**Why it fails**: $\omega(N) \geq 15$ constrains the *count* of prime factors
but not *which* primes appear. A hypothetical QPN could have factorization
$N = 7^2 \cdot 11^2 \cdots 53^2 \cdot q_{14}^{2} \cdot q_{15}^{2}$ with
$q_{14}, q_{15}$ arbitrarily large. Nothing in the omega bound prevents this.

**Rescue attempt — starvation argument**: Could we prove that any QPN with
$\gcd(N,15)=1$ must use all 15 smallest primes $\geq 7$? This would require
showing "if $p \nmid N$ for some small $p$, then $\omega(N) \geq 16$" (or similar),
which amounts to partial results on the **full QPN non-existence conjecture** —
a major open problem far beyond the scope of `qpn_totient_bound`.

> **Verdict**: Path C is equivalent in difficulty to proving that no QPN exists
> with $\gcd(N,15) = 1$. This is the non-existence conjecture itself.
> **Do not pursue.** Use Path A instead.

#### Phase 4: Final Assembly

- [ ] Instantiate $\sigma(N)/N = 2 + 1/N$ from `h_qpn`
- [ ] Bound $2 + 1/N < 2 + 1/10^{35} < 2.001$ from `h_size` (via `norm_num`/`linarith`)
- [ ] Apply the correction factor bound: $C < 1.006$ (or whichever path succeeded)
- [ ] Chain: $N/\varphi(N) = (2 + 1/N) \times C < 2.001 \times 1.006 < 2.4675$
- [ ] Close with `norm_num` or `linarith`

#### Phase 5: Verification

- [ ] Run `lake build` — no errors, no remaining `sorry` in Abundancy.lean
- [ ] Verify no regressions in dependent files (SpecialFactors, Obstruction, FFI)
- [ ] Update this TODO to mark Issue 2 as ✅ RESOLVED

### Numerical Reference

| Quantity | Value | Source |
|----------|-------|--------|
| $\prod_{k=1}^{14} p_k/(p_k-1)$ for $p \geq 7$ | < 2 | `abundancy_cube_c_lt_two` |
| $\prod_{k=1}^{15} p_k/(p_k-1)$ for $p \geq 7$ | ≈ 2.027 | cubeCPrimes + 61 |
| $\prod_{p \geq 7} p^3/(p^3-1)$ (correction ceiling) | ≈ 1.00428 | $\zeta(3) \prod_{p<7}(1-p^{-3})$ |
| $\prod_{k=1}^{15} (1+1/p+1/p^2)$, smallest primes | ≈ 2.0172 | all $v=2$ |
| Actual $N/\varphi(N)$ for large QPNs | < 2.011 | $(2+\epsilon) \times 1.005$ |
| Stated bound | 2.4675 | ~23% headroom |

### Dependencies

| Lemma | File | Provides |
|-------|------|----------|
| `qpn_is_odd_square` | Basic.lean | All $v_p$ even ≥ 2 |
| `qpn_coprime_15_primes_ge_7` | SpecialFactors.lean | All primes ≥ 7 |
| `qpn_coprime_15_omega_15` | SpecialFactors.lean | $\omega(N) \geq 15$ |
| `sigma_mul_totient_lt_sq` | Abundancy.lean | $\sigma(N) \cdot \varphi(N) < N^2$ |
| `abundancy_cube_c_lt_two` | SpecialFactors.lean | 14-prime Euler product < 2 |
| `Nat.totient_eq_prod_primeFactors` | Mathlib | $\varphi(N) = N \cdot \prod(1-1/p)$ |
