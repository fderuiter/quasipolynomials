# TODO: Lean 4 Formalization Tasks

The following theorems and lemmas are currently stubbed with `sorry` and need to be comprehensively built out and formalized.

## UALBF/Cyclotomic.lean

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

- [x] Formalize proof

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
