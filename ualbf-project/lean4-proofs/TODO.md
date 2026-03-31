# TODO: Lean 4 Formalization Tasks

The following theorems and lemmas are currently stubbed with `sorry` and need to be comprehensively built out and formalized.

## UALBF/Cyclotomic.lean

### `cyclotomic_only_top_dvd` (Line 1067)
**Signature:**
```lean
lemma cyclotomic_only_top_dvd (p m q : ℕ) (d : ℕ) (hq_prime : q.Prime) (hqm : ¬(q ∣ m)) (hq_dvd_phi_m : q ∣ (eval (p : ℤ) (cyclotomic m ℤ)).natAbs) (hd_dvd_m : d ∣ m) (hd_ne_m : d ≠ m) (hm_pos : 0 < m) ¬(q ∣ (eval (p : ℤ) (cyclotomic (d * q) ℤ)).natAbs) intro hq_dvd_phi_dq
```
**Description:** Sub-sub-lemma 5i: Isolation — only Φ_{mq} contributes q-valuation.** Among all `Φ_{dq}(p)` for `d | m` (with `q ∤ m`), only `d = m` gives `q | Φ_{dq}(p)`. This is because: `q | Φ_{dq}(p)` iff `q | Φ_d(p)` (since in `ZMod q`, `Φ_{dq} = Φ_d^{q-1}`). `q | Φ_d(p)` iff `orderOf p = d` in `ZMod q` (by `isRoot_cyclotomic_iff`). We know `orderOf p = m` (from the hypothesis `q | Φ_m(p)` and `q ∤ m`). So `d = m` is the only possibility. /
**Implementation Notes / Hints:**
- Step 1: Prove q | Φ_d(p)
- Φ_d(p) * Φ_{dq}(p) = Φ_d(p^q)
- q | Φ_d(p^q) - Φ_d(p)
- q | Φ_{dq}(p)
- q | Φ_d(p) * Φ_{dq}(p)
- q | Φ_d(p)
- Φ_d(p^q) = Φ_d(p) * Φ_{dq}(p)
- So q | Φ_d(p^q)
- q | Φ_d(p) = Φ_d(p^q) - (Φ_d(p^q) - Φ_d(p))
- Cast back to natAbs
- Step 2: Use ZMod properties
- (p : ZMod q) is a root of cyclotomic m (ZMod q)
- (p : ZMod q) is a root of cyclotomic d (ZMod q)
- m : ZMod q is not zero
- d : ZMod q is not zero
- Primitive roots
- Orders
- Therefore m = d
- Step 1: q | p^m - 1  (since q | Φ_m(p) | p^m - 1)
- Step 2: Apply 5g to x = p^m: q | S = Σ (p^m)^i  but  q² ∤ S
- Step 3: Product identity (5h): ∏_{d|m} Φ_{dq}(p) = Σ p^{im}
- Step 4: The product = S, and q | S, q² ∤ S
- Factor out the m = divisor contribution:
- ∏_{d|m} Φ_{dq}(p) = Φ_{mq}(p) * ∏_{d|m, d≠m} Φ_{dq}(p)
- By 5i: for d | m, d ≠ m, q ∤ Φ_{dq}(p)
- Now assume q² | Φ_{mq}(p) and derive contradiction
- q² | Φ_{mq}(p) means (q : ℤ)² | Φ_{mq}(p) as integers
- q | Φ_{dq}(p) for all d in erase-list? No; q ∤ those.
- The product ∏_{d|m} Φ_{dq} = Φ_{mq} * ∏_{d|m, d≠m} Φ_{dq}
- The co-product is not divisible by q
- q is prime, so q | some factor
- q² | product = (q² | Φ_{mq}) * (coprod)
- So q² | S, contradicting q² ∤ S
- Expand: Φ_{m·q^{k+1}}(p) = Φ_{m·q^k}(p^q)  [since q | m·q^k]
- h_eval: Φ_{m·q^k}(p^q) = Φ_{m·q^{k+1}}(p)
- Fermat: Φ_{m·q^k}(p^q) ≡ Φ_{m·q^k}(p)  (mod q)
- So Φ_{m·q^{k+1}}(p) - Φ_{m·q^k}(p) ≡ 0  (mod q)
- Part 1: q | Φ_{m·q^{k+1}}(p)
- Part 2: q² ∤ Φ_{m·q^{k+1}}(p)
- q² | Φ_{m·q^{k+1}}(p) as integers
- Φ_{m·q^{k+1}}(p) = Φ_{m·q^k}(p) + diff,  q | diff  (from h_diff_dvd)
- q² | Φ_{m·q^{k+1}}(p)  and  q | diff  =>  q² | Φ_{m·q^k}(p)? NO!
- We need: q | Φ_{m·q^k}(p) and q | diff and q² | sum doesn't give q² | Φ_{m·q^k}
- Instead use: q² | Φ_{m·q^{k+1}} and the expand identity
- Φ_{m·q^{k+1}}(p) = Φ_{m·q^k}(p^q)
- Φ_{m·q^k}(p^q) = Φ_{m·q^k}(p) + (Fermat gap)  ←  gap divisible by q
- Write Φ_{m·q^k}(p) = q·u, gap = q·t, so Φ_{m·q^{k+1}} = q·u + q·t = q·(u+t)
- q² | q·(u+t) means q | (u+t), i.e., q | u + t ≡ u (mod q) — wait: t may not be 0 mod q
- Actually the gap = Φ_{m·q^k}(p^q) - Φ_{m·q^k}(p), which is q · (something).
- u+t ≡ u  iff  q | t. But we only know q∤u. So this doesn't propagate!
- Need a sharper argument; the Fermat gap is divisible by q but we can't say more.
- We use a different approach: raise the divisibility by looking at the factoring identity.
- Φ_{m·q^k}(p^q) = Φ_{m·q^k}(p) · [correction], but there's no such factoring for q|m·q^k.
- ALTERNATIVE: Use that q · u = Φ_{m·q^k}(p), gap = q·t, Φ_{m·q^{k+1}} = q(u+t).
- q² | q(u+t)  iff  q | u+t  iff  q | u + (t mod q).
- We know: u = Φ_{m·q^k}(p)/q, write the Fermat gap = Φ_{m·q^k}(p^q) - Φ_{m·q^k}(p).
- The gap/q equals (evaluation of derivative-like thing) which is hard to track.
- OBSERVATION: h_not_sq says ¬q² | Φ_{m·q^k}(p). Similarly for level k+1 we use
- the fact that in the product formula for p^{n}-1 / (p^{m}-1), the valuation is fixed.
- For now, use the iterated argument that q | Φ_{m·q^j}(p) for ALL j ≥ 1, so
- q² | Φ_{m·q^{k+1}} → q | (quotient) → contradiction by showing the quotient is ≡ the
- previous quotient mod q. We rely on the fact gap/q is NOT divisible by q in general.
- FALLBACK: use 5g applied to Φ_{m·q^k} at one higher level.
- Actually the correct proof uses LTE for p^{mq^k}-1 which is not yet available here.
- For now, treat this direction as needing an additional sub-lemma.

- [ ] Formalize proof

### `cyclotomic_eval_val_of_dvd_index` (Line 1109)
**Signature:**
```lean
lemma cyclotomic_eval_val_of_dvd_index (p n q : ℕ) (hp : p.Prime) (hn : 3 ≤ n) (hq_prime : q.Prime) (hq_dvd_phi : q ∣ (eval (p : ℤ) (cyclotomic n ℤ)).natAbs) (hq_dvd_n : q ∣ n) ¬(q ^ 2 ∣ (eval (p : ℤ) (cyclotomic n ℤ)).natAbs)
```
**Description:** Sub-lemma 5: Bounded contribution of non-primitive primes.** If a prime `q` divides both `Φ_n(p)` and `n`, then `q` appears in `Φ_n(p)` with multiplicity exactly 1 (i.e., `q ∥ Φ_n(p)`). More precisely, `¬(q² | Φ_n(p))` when `q | n` and `q | Φ_n(p)`. Proof:* Write `n = q^a · m` with `q ∤ m`, `a ≥ 1`. 1. Show `q | Φ_m(p)` (contrapositive of 5f: q ∤ Φ_m ⇒ q ∤ Φ_{m·q^k}). 2. By 5h: `∏_{d | m} Φ_{dq}(p) = 1 + p^m + ⋯ + p^{(q-1)m}` (geometric sum). 3. By 5g (LTE core): `v_q(Σ p^{im}) = 1` since `q | p^m - 1`. 4. By 5i (isolation): only `Φ_{mq}(p)` among the product is divisible by `q`. 5. Therefore `v_q(Φ_{mq}(p)) = 1`, i.e., `q ∥ Φ_{mq}(p)`. 6. For `a ≥ 2`: `v_q` stays 1 under q-power iteration (helper 5-step). 7. Since `n = m·q^a`, we conclude `v_q(Φ_n(p)) = 1`. /
**Implementation Notes / Hints:**
- Step 0: q ≠ 2 (since q | n and n is odd... wait n need not be odd here)
- Actually we need q odd for 5g. Check: q prime, q | n, n ≥ 3.
- q = 2 is possible, but then: Φ_n(p) for even n...
- For q = 2: q | n means n is even. Φ_n(p) at even n is typically odd for odd p.
- Actually for q=2, q | Φ_n(p) is rare. But the proof structure changes.
- We handle q = 2 separately.
- For q = 2: cyclotomic evaluations at even index are harder to reason about.
- We use a different argument for even q.
- Actually, for q=2: Φ_n(p) with p odd and n≥4 even: Φ_n(p) ≡ 1 (mod 2) typically.
- If 2 | Φ_n(p) and 2 | n, then 4 ∤ Φ_n(p)?
- This requires knowing Φ_n(p) is odd when p is odd and n even, or...
- For now, rely on the fact that if q=2 and q | Φ_n(p), then Φ_n(p) is even.
- But 4 | Φ_n(p) is blocked by the LTE/product argument.
- This case analysis is complex. Use sorry for q=2.

- [ ] Formalize proof

### `cyclotomic_eval_two_ge_one` (Line 1478)
**Signature:**
```lean
lemma cyclotomic_eval_two_ge_one (d : ℕ) : 1 ≤ (eval (2 : ℤ) (cyclotomic d ℤ)).natAbs
```
**Description:** Sub-sub-lemma 6a_3b1: Cyclotomic evaluated at 2 is at least 1.** /

- [ ] Formalize proof

### `properDivisors_eq_biUnion_divisors_of_primeFactors` (Line 1485)
**Signature:**
```lean
lemma properDivisors_eq_biUnion_divisors_of_primeFactors (n : ℕ) (hn : 0 < n) : n.properDivisors = n.primeFactors.biUnion (fun p => (n / p).divisors)
```
**Description:** Sub-sub-lemma 6a_3b2: Proper divisors as union of maximal proper divisors.** /

- [x] Formalize proof

### `prod_biUnion_le_prod_prod` (Line 1493)
**Signature:**
```lean
lemma prod_biUnion_le_prod_prod {α : Type*} {s : Finset α} {t : α → Finset ℕ} {f : ℕ → ℕ} (h_pos : ∀ x, 1 ≤ f x) : ∏ x ∈ s.biUnion t, f x ≤ ∏ a ∈ s, ∏ x ∈ t a, f x
```
**Description:** Sub-sub-lemma 6a_3b3: Bounding union product.** The product of values ≥ 1 over a union of sets is bounded by the product of products over the sets. /

- [ ] Formalize proof

### `prod_properDivisors_cyclotomic_two_le_primeFactors` (Line 1501)
**Signature:**
```lean
lemma prod_properDivisors_cyclotomic_two_le_primeFactors (n : ℕ) (hn_pos : 0 < n) : (∏ d ∈ n.properDivisors, (eval (2 : ℤ) (cyclotomic d ℤ)).natAbs) ≤ ∏ p ∈ n.primeFactors, (2 ^ (n / p) - 1)
```
**Description:** Sub-sub-lemma 6a_3b4: Bounding the product over proper divisors by products over maximal divisors.** /

- [ ] Formalize proof

### `primeFactors_bound_cyclotomic_two_lt` (Line 1509)
**Signature:**
```lean
lemma primeFactors_bound_cyclotomic_two_lt (n : ℕ) (hn_odd : Odd n) (hn : 3 ≤ n) : n * ∏ p ∈ n.primeFactors, (2 ^ (n / p) - 1) < 2 ^ n - 1
```
**Description:** Sub-sub-lemma 6a_3b5: Final algebraic bound.** For odd `n ≥ 3`, `n * ∏_{p|n} (2^{n/p}-1) < 2^n - 1`. /

- [ ] Formalize proof

### `cyclotomic_eval_two_gt_index` (Line 1550)
**Signature:**
```lean
lemma cyclotomic_eval_two_gt_index (n : ℕ) (hn_odd : Odd n) (hn : 3 ≤ n) : n < (eval (2 : ℤ) (cyclotomic n ℤ)).natAbs have hm_pos : 0 < n := by omega have h_prod := prod_proper_divisors_cyclotomic_two n hm_pos have h_bound := prod_proper_divisors_cyclotomic_two_bound n hn_odd hn
```
**Description:** Sub-sub-lemma 6a_3: Index bound for p = 2.** /
**Implementation Notes / Hints:**
- Let A be the product over proper divisors, and B be Φ_n(2)
- To conclude n < B from n * A < A * B, A must be positive.
- The product is positive because each evaluation of cyclotomic is positive.

- [ ] Formalize proof

### `squarefree_dvd_of_prime_factors_dvd` (Line 1590)
**Signature:**
```lean
lemma squarefree_dvd_of_prime_factors_dvd (m n : ℕ) (hm_pos : 0 < m) (h_primes : ∀ q : ℕ, q.Prime → q ∣ m → q ∣ n) (h_sq : ∀ q : ℕ, q.Prime → q ∣ m → ¬(q ^ 2 ∣ m)) m ∣ n
```
**Description:** Sub-sub-lemma 6b: Squarefree numbers with all prime factors dividing n must divide n.** If a positive integer `m` satisfies: (1) every prime factor of `m` divides `n`, and (2) no prime appears in `m` with multiplicity ≥ 2, then `m ∣ n`. Proof:* m is squarefree (by condition 2), so m = ∏ (primes of m). Each such prime divides n (by condition 1), so m | rad(n) | n. /

- [ ] Formalize proof
