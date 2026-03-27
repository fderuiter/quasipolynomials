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

- [ ] Prove the local prime-power identity as a standalone lemma:
  ```lean
  lemma euler_factor_decomp (p v : ℕ) (hp : p.Prime) (hv : v ≥ 1) :
      (p : ℚ) / (p - 1) = 
      (∑ k ∈ Finset.range (v + 1), (p : ℚ) ^ k) / (p : ℚ) ^ v *
      (p ^ (v + 1) : ℚ) / (p ^ (v + 1) - 1) := by
  ```
  - [ ] Verify that `p/(p-1) = σ(p^v)/p^v × p^{v+1}/(p^{v+1}-1)` holds as a ℚ identity
  - [ ] Handle the `p ≥ 2` positivity and `p^{v+1} - 1 ≠ 0` side goals

- [ ] Lift to the global multiplicative identity:
  ```lean
  lemma totient_ratio_decomp {N : ℕ} (hN : N > 1) :
      (N : ℚ) / (N.totient : ℚ) = 
      abundancy_index N * ∏ p ∈ N.primeFactors, 
        (p ^ (N.factorization p + 1) : ℚ) / (p ^ (N.factorization p + 1) - 1) := by
  ```
  - [ ] Use `Nat.totient_eq_prod_primeFactors` to rewrite φ(N) as product
  - [ ] Use `Nat.sum_divisors` to rewrite σ(N) as product over prime powers
  - [ ] Apply `euler_factor_decomp` at each prime factor via `Finset.prod` manipulation

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

##### Path B: ω(N) bound + per-factor bound (moderate, partially mechanizable)

- [ ] Prove monotonicity: $x/(x-1)$ is decreasing for $x > 1$
  - [ ] Conclude $p^{v+1}/(p^{v+1}-1) \leq p^3/(p^3-1) \leq 343/342$ for $p \geq 7, v \geq 2$
- [ ] Bound ω(N) from the σ constraint:
  - [ ] Prove each $\sigma(p^v)/p^v \geq 1 + 1/p$ (partial geometric sum ≥ first two terms)
  - [ ] So $\prod(1+1/p_i) \leq \sigma(N)/N = 2 + 1/N$
  - [ ] Compute: for the 18 smallest primes ≥ 7, $\prod(1+1/p) > 2.014$
  - [ ] Therefore at most 17 of N's primes can be among {7,...,71}
  - [ ] Also $N \geq \prod p_i^2 \geq 49^{\omega(N)}$, giving $\omega(N) \leq \log_{49}(N)$
  - [ ] **Issue**: Without an upper bound on N, ω(N) is unbounded → $(343/342)^{\omega}$ blows up
  - [ ] **Fix needed**: Tighter argument using $\sum 1/(p^3-1) < \sum 2/p^3$ convergence

##### Path C: Vacuous truth (elegant, requires careful argument)

- [ ] Show no QPNs with $\gcd(N,15)=1$ exist for $N > 10^{35}$:
  - [ ] From `qpn_coprime_15_omega_15`: $\omega(N) \geq 15$
  - [ ] From `qpn_is_odd_square`: all $v_p \geq 2$
  - [ ] So $\sigma(N)/N = \prod \sigma(p^{v_p})/p^{v_p} \geq \prod(1 + 1/p + 1/p^2)$
  - [ ] Compute: for ANY 15 distinct primes $\geq 7$, is $\prod(1+1/p+1/p^2) > 2 + 10^{-35}$?
    - [ ] ✅ for 15 smallest (≈ 2.017)
    - [ ] ❌ for 15 very large primes (product → 1): **vacuous truth fails in general**
  - [ ] **Caveat**: Need to prove no valid prime configuration exists. This requires showing
        that ω(N) ≥ 15 forces enough small primes that the σ product exceeds 2 + 1/N.
        Essentially, one must prove a "starvation" result: QPNs can't avoid small primes
        while maintaining 15+ factors.
  - [ ] If provable, the theorem becomes `False.elim` — any conclusion follows.

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
