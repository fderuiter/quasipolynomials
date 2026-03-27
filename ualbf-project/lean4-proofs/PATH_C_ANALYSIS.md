# Path C Analysis: Vacuous Truth for QPN Nonexistence

## 1. What Path C Claims

**Goal**: Show no quasiperfect number $N$ with $\gcd(N, 15) = 1$ exists for $N > 10^{35}$, thereby making `qpn_totient_bound` vacuously true (any conclusion follows from `False`).

**Available facts** (already proved in the codebase):

| Fact | Source | Statement |
|------|--------|-----------|
| $\sigma(N) = 2N + 1$ | `IsQuasiperfect` | QPN definition |
| $N$ is an odd perfect square | `qpn_is_odd_square` | All $v_p$ even $\geq 2$ |
| All prime factors $p \geq 7$ | `qpn_coprime_15_primes_ge_7` | From $\gcd(N,15)=1$ |
| $\omega(N) \geq 15$ | `qpn_coprime_15_omega_15` | Prasad–Sunitha bound |

---

## 2. The Argument Attempt

Since $\sigma$ is multiplicative and $N = \prod p_i^{v_i}$:

$$\frac{\sigma(N)}{N} = \prod_{p \mid N} \frac{\sigma(p^{v_p})}{p^{v_p}} = 2 + \frac{1}{N}$$

Each factor satisfies (for $v_p \geq 2$):

$$\frac{\sigma(p^{v_p})}{p^{v_p}} = \frac{p^{v_p+1} - 1}{(p-1) \cdot p^{v_p}} \geq 1 + \frac{1}{p} + \frac{1}{p^2}$$

with equality at $v_p = 2$. So:

$$\prod_{p \mid N} \left(1 + \frac{1}{p} + \frac{1}{p^2}\right) \leq 2 + \frac{1}{N}$$

**Path C asks**: Is the left side always $> 2 + 10^{-35}$ for any set of $\geq 15$ distinct primes $\geq 7$?

---

## 3. Numerical Verdict

### ✅ Works for the 15 smallest primes

$$\prod_{k=1}^{15} \left(1 + \frac{1}{p_k} + \frac{1}{p_k^2}\right) \approx 2.0170 > 2$$

where $p_1, \ldots, p_{15} = 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61$.

### ❌ Fails when primes are large

| Configuration | Product | $> 2$? |
|---------------|---------|--------|
| 15 smallest $\geq 7$ | 2.0170 | ✅ |
| 14 smallest + $10007$ | 1.9842 | ❌ |
| 13 smallest + $10^5, 10^6$ | 1.9504 | ❌ |
| 12 smallest + 3 huge primes | 1.9136 | ❌ |
| 15 primes near $10^{17}$ | $\approx 1.0000$ | ❌ |

### The critical threshold

With the 14 smallest primes $\{7, \ldots, 59\}$:

$$\prod_{k=1}^{14} \left(1 + \frac{1}{p_k} + \frac{1}{p_k^2}\right) \approx 1.9840$$

For a 15th prime $q$ to push the product above 2, we need:

$$1 + \frac{1}{q} + \frac{1}{q^2} > \frac{2}{1.9840} \approx 1.00808$$

which requires $q \leq 10$. But the only odd prime $\leq 10$ coprime to 15 and $\geq 7$ is $7$ itself — which is already in the list. So any 15th prime $q > 59$ gives a product below 2.

> [!CAUTION]
> **Path C fails as a standalone argument.** The lower bound $\prod(1 + 1/p + 1/p^2)$ exceeds 2 only when *all 15 primes are among the smallest*. Replacing even one small prime with a large prime drops the product below 2. Since $\omega(N) \geq 15$ does not constrain which primes appear, there exist valid prime configurations where the product is well below 2.

---

## 4. Can Path C Be Rescued?

To rescue Path C, one would need a **starvation argument**: prove that any QPN with $\gcd(N,15)=1$ must have all 15 smallest primes $\geq 7$ (i.e., $\{7, 11, 13, \ldots, 59, 61\}$) dividing it.

**Why this is essentially impossible from the available tools**:

The bound $\omega(N) \geq 15$ says "at least 15 distinct prime factors," but places no constraint on *which* primes. A hypothetical QPN could have factorization:

$$N = 7^2 \cdot 11^2 \cdot 13^2 \cdots 53^2 \cdot q_{14}^{2} \cdot q_{15}^{2} \cdots$$

with $q_{14}, q_{15}, \ldots$ being arbitrarily large primes. Nothing in the omega bound or the parity/coprimality constraints prevents this.

To force all small primes to appear would require proving something like:
- "If $7 \nmid N$ then $\omega(N) \geq 16$" (i.e., missing a small prime forces *more* total factors), or
- A direct Diophantine impossibility result.

Both of these amount to partial results toward the full QPN non-existence conjecture — far beyond what's needed for `qpn_totient_bound`.

> [!IMPORTANT]
> **Path C is equivalent in difficulty to proving the full QPN non-existence conjecture for $\gcd(N,15)=1$.** This is a major open problem in number theory. Do not pursue this path.

---

## 5. The Correct Independent Proof (Path A)

The theorem `qpn_totient_bound` does **not** require vacuous truth. The direct correction-factor bound gives a clean proof entirely independent of the codebase's search-tree logic.

### Self-Contained Statement

> **Theorem.** Let $N > 10^{35}$ be a quasiperfect number with $\gcd(N, 15) = 1$. Then $N / \varphi(N) < 2.4675$.

### Proof (independent of codebase)

**Step 1: Key Identity.**

$$\frac{N}{\varphi(N)} = \prod_{p \mid N} \frac{p}{p-1} = \prod_{p \mid N} \frac{\sigma(p^{v_p})}{p^{v_p}} \cdot \prod_{p \mid N} \frac{p^{v_p+1}}{p^{v_p+1} - 1}$$

This follows from the local identity at each prime $p$ with exponent $v \geq 1$:

$$\frac{p}{p-1} = \frac{\sigma(p^v)}{p^v} \cdot \frac{p^{v+1}}{p^{v+1} - 1}$$

which can be verified algebraically:

$$\frac{p^{v+1}-1}{(p-1) \cdot p^v} \cdot \frac{p^{v+1}}{p^{v+1}-1} = \frac{p^{v+1}}{(p-1) \cdot p^v} = \frac{p}{p-1} \quad \checkmark$$

**Step 2: Bound the abundancy factor.**

For a QPN: $\sigma(N)/N = 2 + 1/N$. Since $N > 10^{35}$:

$$\frac{\sigma(N)}{N} = 2 + \frac{1}{N} < 2 + 10^{-35} < 2.001$$

**Step 3: Bound the correction factor $C$.**

$$C = \prod_{p \mid N} \frac{p^{v_p+1}}{p^{v_p+1}-1} = \prod_{p \mid N} \frac{1}{1 - p^{-(v_p+1)}}$$

Since all $p \geq 7$ (from $\gcd(N,15) = 1$) and all $v_p \geq 2$ (from $N$ being an odd square):

$$\frac{p^{v_p+1}}{p^{v_p+1}-1} \leq \frac{p^3}{p^3-1}$$

because $x/(x-1)$ is decreasing for $x > 1$ and $p^{v_p+1} \geq p^3$. Therefore:

$$C \leq \prod_{p \mid N} \frac{p^3}{p^3-1} \leq \prod_{\substack{p \geq 7 \\ p \text{ prime}}} \frac{p^3}{p^3-1}$$

The second inequality is valid because each factor $p^3/(p^3-1) > 1$, so adding more primes only increases the product.

**Step 4: Evaluate the infinite product.**

$$\prod_{\substack{p \geq 7 \\ p \text{ prime}}} \frac{1}{1-p^{-3}} = \frac{\zeta(3)}{\prod_{p < 7} (1-p^{-3})^{-1}} = \frac{\zeta(3)}{\frac{8}{7} \cdot \frac{27}{26} \cdot \frac{125}{124}}$$

where $\zeta(3) \approx 1.2020569$. Numerically:

$$\prod_{p < 7} \frac{p^3}{p^3-1} = \frac{8}{7} \cdot \frac{27}{26} \cdot \frac{125}{124} \approx 1.19638$$

$$C \leq \frac{1.2020569}{1.19638} \approx 1.00474$$

> [!TIP]
> **For formalization**, avoid $\zeta(3)$. Instead, directly compute $\prod_{p=7}^{9973} p^3/(p^3-1)$ as an explicit rational ($\approx 1.004741$) and bound the tail $\prod_{p > 9973} p^3/(p^3-1) < 1 + 10^{-8}$ using $\sum_{p>9973} 1/p^3 < \int_{9973}^{\infty} x^{-3}\,dx = 5 \times 10^{-9}$ and $\prod(1+x_i) \leq e^{\sum x_i}$.

**Step 5: Combine.**

$$\frac{N}{\varphi(N)} = \frac{\sigma(N)}{N} \cdot C < 2.001 \times 1.005 < 2.011 \ll 2.4675 \quad \blacksquare$$

---

## 6. Framing as an Independent Self-Contained Proof

The proof above requires exactly **four mathematical ingredients**, none of which depend on the UALBF codebase:

### Ingredient 1: QPN structural facts (classical number theory)
- **Odd square**: If $\sigma(N) = 2N+1$ then $N$ is an odd perfect square.
  - *Proof*: $\sigma(N)$ is odd $\Rightarrow$ $N$ is a square or $2 \times$ square. The latter leads to a mod-3 contradiction (proved in [Basic.lean](file:///Volumes/SanDisk%20External%20SSD/Code/quasipolynomials/ualbf-project/lean4-proofs/UALBF/Basic.lean)).
  - Even square case fails by Legendre symbol obstruction ($-1$ is not a QR mod primes $\equiv 3 \pmod{4}$).

### Ingredient 2: Multiplicativity of $\sigma$ 
- Standard from Mathlib: `Nat.Coprime.sum_divisors_mul`, `Nat.sum_divisors`.

### Ingredient 3: The local Euler factor identity
- Pure algebra over $\mathbb{Q}$:
$$\frac{p}{p-1} = \frac{\sigma(p^v)}{p^v} \cdot \frac{p^{v+1}}{p^{v+1}-1}$$

### Ingredient 4: Convergent infinite product bound
- $\prod_{p \geq 7} p^3/(p^3-1) < 1.005$.
- Can be verified by finite computation + integral tail bound.

> [!NOTE]
> **Key insight**: The proof does NOT use $\omega(N) \geq 15$ at all! It only uses:
> - $\sigma(N)/N = 2 + 1/N$ (QPN definition)
> - All $p \geq 7$ (from coprimality)  
> - All $v_p \geq 2$ (from odd square)
> - $N > 10^{35}$ (size bound)
>
> The $\omega \geq 15$ bound is a *consequence* of these, but is never needed in the proof chain.

---

## 7. Summary Comparison

| | Path C (Vacuous Truth) | Path A (Direct Bound) |
|---|---|---|
| **Goal** | Prove $\nexists$ QPN with $\gcd(N,15)=1$, $N > 10^{35}$ | Prove $N/\varphi(N) < 2.4675$ directly |
| **Difficulty** | Equivalent to QPN non-existence conjecture | Elementary bound |
| **Uses $\omega \geq 15$?** | Yes (and still insufficient) | No |
| **Key obstacle** | Large primes defeat the lower bound | None — clean argument |
| **Result** | ❌ **Cannot be completed** | ✅ **Clean proof with massive headroom** |
| **Bound achieved** | N/A | $N/\varphi(N) < 2.011$ (23% below 2.4675) |

> [!IMPORTANT]
> **Recommendation**: Abandon Path C entirely. Implement Path A as an independent, self-contained proof. The four ingredients above can each be proved (or are already proved) without any dependency on the UALBF search engine, Z3 pruner, or computational results.
