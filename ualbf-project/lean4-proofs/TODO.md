# Lean 4 Proofs TODO: Resolving `sorry` declarations

One remaining `sorry` in the UALBF Lean 4 project: `zsigmondy_prime_divisor` in `Cyclotomic.lean`.

> `qpn_totient_bound` in `Abundancy.lean` is ✅ RESOLVED — fully proven, no `sorry`.

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

#### Phase 3: Correction Factor Bound — ✅ ANALYZED (see [PATH_A_ANALYSIS.md](PATH_A_ANALYSIS.md))

##### Path A (Strategy 3a): All-at-once telescoping — ✅ RECOMMENDED

Bounds ALL primes $\geq 7$ via telescoping without finite/tail split. Achieves
$C < 36/35 \approx 1.029$, giving $N/\varphi(N) < 2.059$ (20% headroom below 2.4675).
**Zero** `Mathlib.Analysis` imports. **Zero** finite computation. Five lemmas over ℚ.

Mathematically identical to "Path B Fixed" — see [PATH_A_ANALYSIS.md](PATH_A_ANALYSIS.md) §5 for
the complete self-contained proof and [PATH_B_ANALYSIS.md](PATH_B_ANALYSIS.md) §4–6 for
the same argument derived independently.

New file: `CorrectionFactor.lean` (standalone, no UALBF imports):

- [x] Lemma 1: `reciprocal_comparison` — $1/(p^3-1) < 2/p^3$ for $p \geq 2$
- [x] Lemma 2: `cube_recip_telescope` — $1/n^3 \leq \frac{1}{2}(1/(n-1)^2 - 1/n^2)$ for $n \geq 1$
- [x] Lemma 3: `finset_sum_cube_bound` — $\sum_{n \in S} 1/n^3 < 1/72$ for distinct $n \geq 7$
- [x] Lemma 4: `prod_one_plus_le_inv` — $\prod(1+x_i) \leq 1/(1-\sum x_i)$, Finset induction over ℚ
- [x] Lemma 5: `correction_factor_lt` — Assembly: $C < 36/35$

##### Path A (Strategy 3b): Finite computation + tail split (optional tightening)

Tighter bound ($C < 1.005$) via explicit 15-prime `norm_num` computation + tail telescoping
from $p > 61$. **Not needed** for `qpn_totient_bound` due to 20% headroom. May cause
`norm_num` timeouts with ~60-digit rationals. See [PATH_A_ANALYSIS.md](PATH_A_ANALYSIS.md) §3.

##### Path B: ω(N) bound + per-factor bound — ❌ BROKEN (see [PATH_B_ANALYSIS.md](PATH_B_ANALYSIS.md))

**Per-factor bound is valid** ($343/342$ ceiling per prime), but **ω(N) is unbounded** without an a priori upper bound on $N$. The product $(343/342)^{\omega(N)}$ diverges for QPNs with many large prime factors, each contributing $(1+1/p) \approx 1$ to the σ constraint. See full analysis in PATH_B_ANALYSIS.md §3.

##### Path B Fixed: Telescoping sum approach — ✅ RECOMMENDED

Combines Path B's valid monotonicity with a convergent-sum argument in pure ℚ arithmetic.
No real analysis imports. See [PATH_B_ANALYSIS.md](PATH_B_ANALYSIS.md) §4–6 for full proof.

- [x] Lemma 1: `cube_reciprocal_mono` — $p^{v+1}/(p^{v+1}-1) \leq p^3/(p^3-1)$ for $p \geq 7, v \geq 2$
- [x] Lemma 2: `reciprocal_cube_comparison` — $1/(p^3-1) < 2/p^3$ for $p \geq 2$
- [x] Lemma 3: `finset_sum_cube_reciprocal_bound` — For any Finset $S \subseteq [7,\infty)$:
  $\sum_{n \in S} 1/n^3 \leq 1/72$ (via telescoping: $1/n^3 \leq \frac{1}{2}(1/(n-1)^2 - 1/n^2)$)
- [x] Lemma 4: `prod_one_plus_le_inv` — $\prod(1+x_i) \leq 1/(1-\sum x_i)$ for $x_i \geq 0, \sum x_i < 1$
  (Finset induction, pure ℚ, no Mathlib.Analysis)
- [x] Lemma 5: Assembly — $C < 36/35$, then $(2+1/N) \times 36/35 < 2.059 < 2.4675$

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

#### Phase 4: Final Assembly — ✅ COMPLETE

- [x] Instantiate $\sigma(N)/N = 2 + 1/N$ from `h_qpn` via `qpn_abundancy_target`
- [x] Bound $2 + 1/N < 20001/10000$ from `h_size > 10^{35}` (via `div_lt_div_iff₀` + `linarith`)
- [x] Apply the correction factor bound: $C < 1022/1000$ from `correction_factor_bound`
- [x] Chain: $N/\varphi(N) = H(N) \times C < (20001/10000) \times (1022/1000)$ via `mul_lt_mul`
- [x] Close with `norm_num`: $20001/10000 \times 1022/1000 < 2.4675$ ✓

#### Phase 5: Verification — ✅ COMPLETE

- [x] Run `lake build` — no errors, no remaining `sorry` in Abundancy.lean
- [x] Verify no regressions in dependent files (SpecialFactors, Obstruction, FFI)
- [x] Update this TODO to mark Issue 2 as ✅ RESOLVED

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
