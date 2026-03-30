# Path B Analysis: ω(N) Bound + Per-Factor Bound

## 1. What Path B Claims

**Goal**: Bound the correction factor $C = \prod_{p \mid N} p^{v_p+1}/(p^{v_p+1}-1)$ by combining:
1. A **per-factor ceiling**: each term $\leq 343/342$ (monotonicity)  
2. An **ω(N) cap** from the σ-constraint: limit how many factors appear

If both hold, then $C \leq (343/342)^{\omega(N)}$, which is a finite constant.

**Available facts** (already proved in the codebase):

| Fact | Source | Statement |
|------|--------|-----------|
| $\sigma(N) = 2N + 1$ | `IsQuasiperfect` | QPN definition |
| $N$ is an odd perfect square | `qpn_is_odd_square` | All $v_p$ even $\geq 2$ |
| All prime factors $p \geq 7$ | `qpn_coprime_15_primes_ge_7` | From $\gcd(N,15)=1$ |
| $\omega(N) \geq 15$ | `qpn_coprime_15_omega_15` | Prasad–Sunitha bound |
| $\prod_{k=1}^{14} p_k/(p_k-1) < 2$ | `abundancy_cube_c_lt_two` | 14-prime Euler product |

---

## 2. The Argument Step-by-Step

### Step 1: Per-factor monotonicity ✅ (valid)

$x/(x-1)$ is decreasing for $x > 1$. Since $p^{v+1} \geq p^3 \geq 7^3 = 343$ for $p \geq 7, v \geq 2$:

$$\frac{p^{v+1}}{p^{v+1}-1} \leq \frac{p^3}{p^3-1} \leq \frac{343}{342}$$

This is elementary and correct. Cross-multiply to verify: $343 \cdot (p^3-1) \geq p^3 \cdot 342$ iff $p^3 \geq 343$ iff $p \geq 7$.

### Step 2: Bound ω(N) from the σ constraint ✅ (valid for finite N)

Each $\sigma(p^v)/p^v \geq 1 + 1/p$ (first two terms of the geometric sum). So:

$$\prod_{p \mid N} \left(1 + \frac{1}{p}\right) \leq \prod_{p \mid N} \frac{\sigma(p^v)}{p^v} = 2 + \frac{1}{N} < 2.001$$

For the 18 smallest primes $\geq 7$ (up to $p = 73$):

$$\prod_{k=1}^{18} \left(1 + \frac{1}{p_k}\right) = \frac{8}{7} \cdot \frac{12}{11} \cdot \frac{14}{13} \cdots \frac{74}{73} \approx 2.014 > 2.001$$

Therefore **at most 17** of N's prime factors can lie in $\{7, 11, \ldots, 73\}$.

### Step 3: Conclude C is bounded ❌ (FAILS)

Path B attempts: $C \leq (343/342)^{\omega(N)}$.

For this to yield $C < 1.234$ (needed for $N/\varphi(N) < 2.4675$), we need:

$$(343/342)^{\omega(N)} < 1.234 \implies \omega(N) < \frac{\ln 1.234}{\ln(343/342)} \approx 72$$

**But ω(N) cannot be bounded as a constant.** The σ constraint only shows that the product $\prod(1+1/p_i)$ is bounded, not the count. A QPN could have:

$$N = 7^2 \cdot 11^2 \cdot 13^2 \cdots 53^2 \cdot q_{14}^2 \cdot q_{15}^2 \cdot q_{16}^2 \cdots q_{k}^2$$

with $q_{14}, \ldots, q_k$ being arbitrarily many large primes. Each $(1 + 1/q_i) \approx 1$ for huge $q_i$, so the product stays below 2.001 even with thousands of factors.

The size bound $N \geq \prod p_i^2 \geq 49^{\omega(N)}$ gives $\omega(N) \leq \log_{49}(N)$, but without an upper bound on $N$ itself, $\omega(N)$ is unbounded.

---

## 3. Numerical Demonstration of Failure

| Configuration | ω(N) | $(343/342)^{\omega}$ | Usable? |
|---------------|-------|----------------------|---------|
| 15 primes, all small | 15 | 1.0447 | ✅ |
| 30 primes, half large | 30 | 1.0912 | ✅ |
| 72 primes | 72 | 1.234 | ⚠️ borderline |
| 100 primes | 100 | 1.339 | ❌ exceeds bound |
| 500 primes (huge $q_i$) | 500 | 4.30 | ❌ blows up |

Since a QPN with $\gcd(N,15) = 1$ could hypothetically have $\omega(N) = 500$ (with 486 primes each $> 10^{100}$, contributing factors infinitesimally above 1 to the σ product), the bound $(343/342)^{500} \approx 4.3$ is useless.

> [!CAUTION]
> **Path B's fatal flaw**: The per-factor bound $343/342$ is **too loose to absorb unbounded ω(N)**. The product $(343/342)^k$ grows exponentially in $k$, while the actual correction factor converges to $\approx 1.00428$ because larger primes contribute exponentially smaller terms. Path B discards this decay by replacing every $1/(p^3-1)$ with the worst-case $1/342$.

---

## 4. The Fix: Telescoping Sum Approach

The "fix needed" noted in the TODO correctly identifies the escape: use the **convergence** of $\sum 1/(p^3-1)$ rather than bounding $\omega(N)$.

### Core Insight

Instead of bounding the product as $(343/342)^k$, bound it via logarithmic compression:

$$C = \prod_{p \mid N} \left(1 + \frac{1}{p^3-1}\right) \leq \frac{1}{1 - \sum_{p \mid N} \frac{1}{p^3-1}}$$

using the rational inequality $\prod(1+x_i) \leq 1/(1-\sum x_i)$ for $x_i \geq 0, \sum x_i < 1$.

### ℚ-Arithmetic Proof (no real analysis needed)

**Step 1**: Each $\frac{1}{p^3-1} < \frac{2}{p^3}$ for $p \geq 2$ (since $p^3 - 1 > p^3/2$).

**Step 2**: Bound $\sum_{p \mid N} 1/p^3$ over distinct primes $\geq 7$ using the telescoping inequality:

$$\frac{1}{n^3} \leq \frac{1}{2}\left(\frac{1}{(n-1)^2} - \frac{1}{n^2}\right) \quad \text{for } n \geq 1$$

*Proof*: Cross-multiply gives $2n^2(n-1)^2 \leq n^3(2n-1)$, i.e. $2(n-1)^2 \leq n(2n-1)$, i.e. $-3n + 2 \leq 0$, true for $n \geq 1$.

**Step 3**: For any finite set $S$ of distinct naturals, all $\geq K \geq 2$, the telescoping sum collapses:

$$\sum_{n \in S} \frac{1}{n^3} \leq \sum_{n=K}^{\max(S)} \frac{1}{n^3} \leq \frac{1}{2} \cdot \frac{1}{(K-1)^2}$$

The second inequality follows by telescoping: $\sum_{n=K}^{M} \frac{1}{2}\left(\frac{1}{(n-1)^2} - \frac{1}{n^2}\right) = \frac{1}{2}\left(\frac{1}{(K-1)^2} - \frac{1}{M^2}\right) \leq \frac{1}{2(K-1)^2}$.

**Step 4**: With $K = 7$:

$$\sum_{p \mid N} \frac{1}{p^3-1} < 2 \sum_{p \mid N} \frac{1}{p^3} \leq \frac{2}{2 \cdot 6^2} = \frac{1}{36}$$

**Step 5**: Apply the product-sum inequality:

$$C < \frac{1}{1 - 1/36} = \frac{36}{35} \approx 1.02857$$

**Step 6**: Final assembly:

$$\frac{N}{\varphi(N)} = \left(2 + \frac{1}{N}\right) \cdot C < 2.001 \times \frac{36}{35} < 2.059 < 2.4675 \quad \blacksquare$$

> [!TIP]
> This bound ($C < 36/35$) is intentionally crude. The actual value is $C \approx 1.00428$. We trade tightness for simplicity — the 23% headroom absorbs everything easily. A tighter bound could be obtained by computing the first 14 primes explicitly and applying the tail bound only to primes $> 61$, yielding $C < 1.005$.

---

## 5. Product-Sum Inequality: Self-Contained Proof

**Lemma.** For $x_1, \ldots, x_k \geq 0$ with $S = \sum x_i < 1$:

$$\prod_{i=1}^{k}(1 + x_i) \leq \frac{1}{1 - S}$$

*Proof by induction*. Base: $k = 0$, $1 \leq 1/(1-0) = 1$. ✓

Inductive step: Assume $\prod_{i=1}^{k}(1+x_i) \leq 1/(1-S_k)$ where $S_k = \sum_{i=1}^{k} x_i$.

$$\prod_{i=1}^{k+1}(1+x_i) = \prod_{i=1}^{k}(1+x_i) \cdot (1+x_{k+1}) \leq \frac{1+x_{k+1}}{1 - S_k}$$

Need: $\frac{1+x_{k+1}}{1 - S_k} \leq \frac{1}{1 - S_{k+1}}$ where $S_{k+1} = S_k + x_{k+1}$.

Cross-multiply (denominators positive since $S_{k+1} < 1$):

$$(1+x_{k+1})(1-S_k-x_{k+1}) \leq 1-S_k$$

Expand left side: $1 - S_k - x_{k+1} + x_{k+1} - S_k x_{k+1} - x_{k+1}^2 = 1 - S_k - S_k x_{k+1} - x_{k+1}^2$

This is $\leq 1 - S_k$ iff $S_k x_{k+1} + x_{k+1}^2 \geq 0$, which holds since $S_k, x_{k+1} \geq 0$. $\square$

> [!NOTE]
> This is provable in Lean 4 by `Finset.induction` over ℚ with standard `field_simp` / `linarith` / `positivity` tactics. No real analysis imports required.

---

## 6. Lean 4 Implementation Outline

Five modular lemmas, all independent of the SpecialFactors pigeonhole machinery:

```
Lemma 1: cube_reciprocal_mono
  (p : ℕ) (hp : p ≥ 7) (v : ℕ) (hv : v ≥ 2) :
  (p^(v+1) : ℚ) / (p^(v+1) - 1) ≤ (p^3 : ℚ) / (p^3 - 1)

Lemma 2: reciprocal_cube_comparison
  (p : ℕ) (hp : p ≥ 2) :
  (1 : ℚ) / (p^3 - 1) < 2 / p^3

Lemma 3: finset_sum_cube_reciprocal_bound
  (S : Finset ℕ) (hS : ∀ n ∈ S, n ≥ 7) :
  ∑ n in S, (1 : ℚ) / n^3 ≤ 1 / 72

Lemma 4: prod_one_plus_le_inv
  (S : Finset ι) (x : ι → ℚ) (hx : ∀ i ∈ S, 0 ≤ x i)
  (hsum : ∑ i in S, x i < 1) :
  ∏ i in S, (1 + x i) ≤ 1 / (1 - ∑ i in S, x i)

Lemma 5: qpn_totient_bound  (assembly — closes the sorry)
```

### Dependencies

| Lemma | Uses from codebase | New math |
|-------|-------------------|----------|
| 1 | — | Monotonicity of $x/(x-1)$ |
| 2 | — | Cross-multiply $p^3 > p^3/2$ |
| 3 | — | Telescoping sum (induction on Finset.Ico) |
| 4 | — | Induction on Finset |
| 5 | `totient_ratio_decomp`, `qpn_abundancy_target`, `qpn_is_odd_square`, `qpn_coprime_15_primes_ge_7` | Assembly |

---

## 7. Summary Comparison with Paths A and C

| | Path A (Finite + Tail) | Path B (ω + Per-Factor) | Path B Fixed (Telescoping) | Path C (Vacuous) |
|---|---|---|---|---|
| **Per-factor bound** | ✅ explicit per prime | ✅ $343/342$ | ✅ $1/(p^3-1) < 2/p^3$ | N/A |
| **Handles unbounded ω** | ✅ via tail integral | ❌ fatal flaw | ✅ via telescoping sum | N/A |
| **Bound achieved** | $C < 1.005$ | unbounded | $C < 36/35 \approx 1.029$ | N/A |
| **Real analysis needed** | Yes ($\int x^{-3}dx$) | No | **No** | N/A |
| **Lean 4 feasibility** | Hard (Mathlib.Analysis) | N/A | **Moderate** (ℚ induction) | Impossible |
| **Verdict** | ✅ tightest | ❌ broken | ✅ **recommended** | ❌ abandoned |

> [!IMPORTANT]
> **Recommendation**: Implement the "Path B Fixed" (telescoping sum) approach. It combines Path B's valid per-factor monotonicity with a convergent-sum argument that works entirely in ℚ, avoiding both the unbounded-ω trap and the need for real analysis imports. The bound $C < 36/35$ is crude but sufficient, giving $N/\varphi(N) < 2.059$ with 20% headroom below the 2.4675 threshold.
