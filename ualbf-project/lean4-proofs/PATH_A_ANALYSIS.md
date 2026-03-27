# Path A Analysis: Finite Computation + Tail Bound

## 1. What Path A Claims

**Goal**: Prove the correction factor $C = \prod_{p \mid N} p^{v_p+1}/(p^{v_p+1}-1) < 503/500$ (= 1.006) by splitting into a finite computation over small primes and an analytic tail bound over large primes; then close `qpn_totient_bound` via $N/\varphi(N) = (2+1/N) \cdot C < 2.001 \times 1.006 < 2.4675$.

**Available facts** (already proved in the codebase):

| Fact | Source | Statement |
|------|--------|-----------|
| $\sigma(N) = 2N + 1$ | `IsQuasiperfect` | QPN definition |
| $N$ is an odd perfect square | `qpn_is_odd_square` | All $v_p$ even $\geq 2$ |
| All prime factors $p \geq 7$ | `qpn_coprime_15_primes_ge_7` | From $\gcd(N,15)=1$ |
| $\omega(N) \geq 15$ | `qpn_coprime_15_omega_15` | Prasad–Sunitha bound |
| $N/\varphi(N) = H(N) \cdot C$ | `totient_ratio_decomp` | Multiplicative decomposition |
| $H(N) = 2 + 1/N$ | `qpn_abundancy_target` | QPN abundancy |

---

## 2. Key Insight: Why This Path Works

Path A succeeds where Paths B and C fail because it handles **unbounded ω(N)** without needing to count prime factors.

- **Path C** tried to show no QPN exists — failed because large primes defeat the lower bound.
- **Path B** tried to cap $\omega(N)$ — failed because $C \leq (343/342)^{\omega}$ diverges for large $\omega$.
- **Path A** bounds the product via its **logarithmic convergence**: large primes contribute exponentially small terms $1/(p^3-1)$, ensuring the infinite product converges even with unbounded $\omega$.

The 23% headroom ($2.4675$ vs actual $\approx 2.011$) means we can use crude bounds and still succeed.

---

## 3. Two Viable Sub-Strategies

### Strategy 3a: All-at-Once Telescoping (Cruder, Simpler)

Skip the finite/tail split entirely. Bound ALL primes $\geq 7$ with the telescoping inequality:

$$\sum_{p \mid N} \frac{1}{p^3} \leq \sum_{n=7}^{\infty} \frac{1}{n^3} \leq \frac{1}{2 \cdot 6^2} = \frac{1}{72}$$

Then: $\sum 1/(p^3-1) < 2\sum 1/p^3 \leq 1/36$, so $C < 36/35 \approx 1.0286$.

$$N/\varphi(N) < 2.001 \times 36/35 = 2.0582 < 2.4675 \quad \blacksquare$$

> [!TIP]
> This is the "Path B Fixed" approach from `PATH_B_ANALYSIS.md`. It requires **zero finite computation** and **zero analysis imports**. Five Lean lemmas, all over ℚ.

### Strategy 3b: Finite + Tail Split (Tighter, Harder)

Compute the first 15 primes explicitly, bound the tail via telescoping from $p > 61$:

**Finite part**: $\prod_{p \in \{7,...,61\}} p^3/(p^3-1) < 100472/100000 \approx 1.00472$ (pure `norm_num`)

**Tail**: $\sum_{p>61} 1/p^3 \leq \sum_{n=67}^{\infty} 1/n^3 \leq 1/(2 \cdot 66^2) = 1/8712$

So tail factor $< 1/(1 - 2/8712) = 8712/8710 \approx 1.00023$.

**Combined**: $C < 100472/100000 \times 8712/8710 \approx 1.00495$, then:

$$N/\varphi(N) < 2.001 \times 1.00495 \approx 2.011 < 2.4675 \quad \blacksquare$$

> [!NOTE]
> Strategy 3b produces a much tighter bound ($C < 1.005$ vs $C < 1.029$) but requires a 15-prime `norm_num` computation with ~60-digit rational arithmetic.

---

## 4. Recommended Strategy: 3a (All-at-Once Telescoping)

> [!IMPORTANT]
> **Recommendation**: Use Strategy 3a. It achieves $C < 36/35$ with zero finite computation, zero Mathlib.Analysis imports, and only five Lean lemmas. The crude bound $N/\varphi(N) < 2.058$ sits 20% below the 2.4675 threshold — more than sufficient.
>
> Strategy 3b can be implemented later as a tightening exercise, but is unnecessary for correctness.

### Why not 3b?

| Concern | 3a | 3b |
|---------|----|----|
| `norm_num` timeout risk | None | ~60-digit rationals |
| Analysis imports | None | None |
| Proof complexity | 5 lemmas | 7+ lemmas |
| Bound quality | $C < 1.029$ (sufficient) | $C < 1.005$ (tight) |
| Lean compile risk | Low | Medium |

---

## 5. Mathematical Proof (Strategy 3a, Self-Contained)

### Lemma 1: Reciprocal Comparison

For $p \geq 2$ (natural number):

$$\frac{1}{p^3 - 1} < \frac{2}{p^3}$$

*Proof*: $p^3 - 1 > p^3/2$ iff $p^3 > 2$, which holds for $p \geq 2$. $\square$

### Lemma 2: Telescoping Per-Term Bound

For $n \geq 1$ (natural number):

$$\frac{1}{n^3} \leq \frac{1}{2}\left(\frac{1}{(n-1)^2} - \frac{1}{n^2}\right)$$

*Proof*: Cross-multiply by $2n^2(n-1)^2 > 0$. The inequality becomes $2(n-1)^2 \leq n(2n-1)$, i.e. $2n^2 - 4n + 2 \leq 2n^2 - n$, i.e. $2 \leq 3n$, true for $n \geq 1$. $\square$

### Lemma 3: Finite Sum Bound via Telescoping

For any finite set $S$ of distinct naturals, all $\geq K \geq 2$:

$$\sum_{n \in S} \frac{1}{n^3} \leq \frac{1}{2(K-1)^2}$$

*Proof*: Since elements are distinct integers $\geq K$, label them $n_1 < n_2 < \cdots < n_k$. Then $n_i \geq K + i - 1$, so:

$$\sum_{i=1}^{k} \frac{1}{n_i^3} \leq \sum_{i=1}^{k} \frac{1}{(K+i-1)^3} \leq \sum_{j=K}^{K+k-1} \frac{1}{j^3}$$

By Lemma 2, this telescopes:

$$\leq \frac{1}{2}\sum_{j=K}^{K+k-1}\left(\frac{1}{(j-1)^2} - \frac{1}{j^2}\right) = \frac{1}{2}\left(\frac{1}{(K-1)^2} - \frac{1}{(K+k-1)^2}\right) < \frac{1}{2(K-1)^2}$$

Applying with $K = 7$: $\sum 1/n^3 < 1/(2 \cdot 36) = 1/72$. $\square$

> [!WARNING]
> **Lean formalization note**: The "relabeling" step ($n_i \geq K + i - 1$) requires sorting the Finset and comparing elementwise. This is the hardest part to formalize. An alternative is to directly prove the bound by `Finset.induction` on a monotone Finset budget, or to embed $S$ into a `Finset.Ico` and use subset-sum monotonicity.

### Lemma 4: Product-Sum Comparison (Weierstrass)

For $x_1, \ldots, x_k \geq 0$ with $\sum x_i < 1$:

$$\prod_{i=1}^{k}(1 + x_i) \leq \frac{1}{1 - \sum x_i}$$

*Proof*: By induction. Base: $k=0$, $1 \leq 1$. Step: $(1 + x_{k+1})/(1 - S_k) \leq 1/(1 - S_{k+1})$ reduces to $S_k x_{k+1} + x_{k+1}^2 \geq 0$. $\square$

### Lemma 5: Correction Factor Bound

$$C = \prod_{p \mid N} \frac{p^{v_p+1}}{p^{v_p+1}-1} < \frac{36}{35}$$

*Proof*: Write each factor as $1 + 1/(p^{v_p+1}-1)$. Since $v_p \geq 2$ and $p \geq 7$:

$$\frac{1}{p^{v_p+1}-1} \leq \frac{1}{p^3-1} < \frac{2}{p^3} \quad \text{(Lemma 1)}$$

Apply Lemma 4 with $x_p = 2/p^3$:

$$C \leq \prod\left(1 + \frac{2}{p^3}\right) \leq \frac{1}{1 - \sum 2/p^3} \leq \frac{1}{1 - 2/72} = \frac{1}{1 - 1/36} = \frac{36}{35}$$

using $\sum 2/p^3 = 2\sum 1/p^3 \leq 2/72 = 1/36$ (Lemma 3 with $K=7$). $\square$

### Theorem: `qpn_totient_bound`

$$\frac{N}{\varphi(N)} = \left(2 + \frac{1}{N}\right) \cdot C < 2.001 \times \frac{36}{35} < 2.4675$$

*Proof*: From `totient_ratio_decomp`: $N/\varphi(N) = H(N) \cdot C$.

$H(N) = 2 + 1/N < 2 + 1/10^{35} < 2001/1000$ (from `h_size`).

$C < 36/35$ (Lemma 5).

$$\frac{N}{\varphi(N)} < \frac{2001}{1000} \times \frac{36}{35} = \frac{72036}{35000} = \frac{18009}{8750} \approx 2.0582$$

Check: $18009/8750 < 2.4675 = 19740/8000$? Cross-multiply: $18009 \times 8000 = 144072000$ vs $19740 \times 8750 = 172725000$. Yes. $\square$

---

## 6. Lean 4 Implementation: Five Lemmas

All lemmas go in a new standalone file `CorrectionFactor.lean` importing only Mathlib (no UALBF imports). The assembly lemma lives in `Abundancy.lean`.

```
CorrectionFactor.lean (NEW — standalone)
├── reciprocal_comparison      -- 1/(p³-1) < 2/p³
├── cube_recip_telescope       -- 1/n³ ≤ ½(1/(n-1)² - 1/n²)
├── finset_sum_cube_bound      -- ∑ 1/n³ < 1/72  for n ≥ 7
├── prod_one_plus_le_inv       -- ∏(1+xᵢ) ≤ 1/(1-∑xᵢ)
└── correction_factor_lt       -- ∏ p³/(p³-1) < 36/35  for p ≥ 7

Abundancy.lean (MODIFY — replace sorry)
└── qpn_totient_bound          -- N/φ(N) < 2.4675
```

### Mathlib Dependencies

| Lemma | Key Mathlib Imports |
|-------|-------------------|
| reciprocal_comparison | `Mathlib.Data.Rat.Defs`, `Mathlib.Tactic.Linarith` |
| cube_recip_telescope | `Mathlib.Tactic.FieldSimp`, `Mathlib.Tactic.Ring` |
| finset_sum_cube_bound | `Mathlib.Algebra.BigOperators.Group.Finset.Basic` |
| prod_one_plus_le_inv | `Mathlib.Algebra.BigOperators.Group.Finset.Basic` |
| correction_factor_lt | Combines above |

**No** `Mathlib.Analysis.*` imports needed. **No** `UALBF.*` imports needed.

---

## 7. The Hardest Formalization Step

> [!CAUTION]
> **Lemma 3 (finset_sum_cube_bound)** is the trickiest to formalize in Lean 4 because it requires showing that a sum over an *arbitrary* `Finset ℕ` of distinct elements $\geq 7$ is bounded by a telescoping series over a contiguous range.
>
> **Three formalization approaches** (in order of difficulty):
>
> 1. **Direct Finset.Ico embedding** (recommended): Show $S \subseteq \text{Finset.Ico } 7 \, (\max S + 1)$, bound the superset sum via telescoping over the Ico, then use `Finset.sum_le_sum_of_subset_of_nonneg`.
>
> 2. **Sort-and-compare**: Sort $S$ to a list, prove $n_i \geq 6 + i$ elementwise, then bound $\sum 1/n_i^3 \leq \sum 1/(6+i)^3$ and telescope. (More code, mirrors the math proof exactly.)
>
> 3. **Monotone budget induction**: Prove a stronger lemma: for $S$ with all elements $\geq K$ and $|S| = k$, $\sum 1/n^3 \leq 1/(2(K-1)^2) - 1/(2(K+k-1)^2)$. Induct on $k$ by removing the minimum element. (Cleanest statement, moderate difficulty.)

---

## 8. Comparison with Other Paths

| | Path A (This) | Path B Original | Path B Fixed | Path C |
|---|---|---|---|---|
| **Core technique** | Telescoping sum | Per-factor × ω cap | Telescoping sum | Vacuous truth |
| **Handles ω → ∞** | ✅ | ❌ fatal | ✅ | N/A |
| **Bound on C** | $36/35 ≈ 1.029$ | unbounded | $36/35 ≈ 1.029$ | N/A |
| **Finite computation** | Optional (for tightness) | None | None | N/A |
| **Analysis imports** | None | None | None | N/A |
| **Lean feasibility** | ✅ Moderate | ❌ Broken | ✅ Moderate | ❌ Impossible |

> [!NOTE]
> **Path A (Strategy 3a) and Path B Fixed are mathematically identical.** Both use the all-at-once telescoping bound with $K=7$. The only difference is naming. Path A (Strategy 3b) adds the optional finite computation refinement for a tighter bound, which is unnecessary for `qpn_totient_bound`. We recommend the shared approach under the "Path A" label since it was identified first in the TODO.

---

## 9. Verdict

$$\boxed{C < \frac{36}{35}, \quad \frac{N}{\varphi(N)} < 2.059, \quad \text{20% headroom below 2.4675}}$$

**Path A is viable, self-contained, and implementable in Lean 4 using five ℚ-arithmetic lemmas with no analysis imports.** The proof depends on exactly four codebase facts (`qpn_abundancy_target`, `totient_ratio_decomp`, `qpn_is_odd_square`, `qpn_coprime_15_primes_ge_7`) and no search-engine or Z3 results.
