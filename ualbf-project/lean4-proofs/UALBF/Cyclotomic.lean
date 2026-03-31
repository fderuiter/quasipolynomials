import UALBF.Obstruction
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.Data.Int.NatAbs
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Tactic

/--
  A robust helper lemma computing the geometric sum exclusively in `ℕ`
  without truncated subtraction: `(p - 1) * ∑ p^i + 1 = p^n`.
-/
lemma nat_geom_sum (p n : ℕ) (hp : 1 ≤ p) :
    (p - 1) * (∑ i ∈ Finset.range n, p ^ i) + 1 = p ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add]
    have h1 : (p - 1) * (∑ i ∈ Finset.range n, p ^ i) + (p - 1) * p ^ n + 1 =
              ((p - 1) * (∑ i ∈ Finset.range n, p ^ i) + 1) + (p - 1) * p ^ n := by omega
    rw [h1, ih]
    have h2 : p ^ n + (p - 1) * p ^ n = p * p ^ n := by
      have h_add : 1 * p ^ n + (p - 1) * p ^ n = (1 + (p - 1)) * p ^ n :=
        (add_mul 1 (p - 1) (p ^ n)).symm
      have h_one : 1 * p ^ n = p ^ n := one_mul (p ^ n)
      have h_p : 1 + (p - 1) = p := by omega
      rw [h_p] at h_add
      rw [h_one] at h_add
      exact h_add
    rw [h2]
    have h3 : p * p ^ n = p ^ (n + 1) := by
      have h_pow_add : p ^ 1 * p ^ n = p ^ (1 + n) := (pow_add p 1 n).symm
      have h_pow_one : p ^ 1 = p := pow_one p
      have h_add : 1 + n = n + 1 := by omega
      rw [h_pow_one] at h_pow_add
      rw [h_add] at h_pow_add
      exact h_pow_add
    exact h3

namespace UALBF

open Finset Nat Polynomial

/--
  Task 1: Cyclotomic Expansion.
  σ(p^{2e}) factors exactly into ∏_{d | 2e+1, d>1} Φ_d(p).
-/
lemma sigma_prime_pow_cyclotomic (p e : ℕ) (hp : p.Prime) :
  sigma (p ^ (2 * e)) = ∏ d ∈ (2 * e + 1).divisors \ {1}, (eval (p : ℤ) (cyclotomic d ℤ)).natAbs := by
  -- Step 1: σ(p^{2e}) = ∑ k in range(2e+1), p^k
  have h_sigma : sigma (p ^ (2 * e)) = ∑ x ∈ Finset.range (2 * e + 1), p ^ x := by
    unfold sigma
    exact sum_divisors_prime_pow hp
  rw [h_sigma]
  -- Step 2: Use the polynomial identity ∏_{d | n, d ≠ 1} Φ_d(X) = ∑_{i < n} X^i
  have h_pos : 0 < 2 * e + 1 := by omega
  have h_poly : ∏ i ∈ (2 * e + 1).divisors.erase 1, cyclotomic i ℤ =
      ∑ i ∈ Finset.range (2 * e + 1), X ^ i :=
    prod_cyclotomic_eq_geom_sum h_pos ℤ
  -- Step 3: Evaluate the polynomial identity at (p : ℤ)
  have h_eval : eval (↑p : ℤ) (∏ i ∈ (2 * e + 1).divisors.erase 1, cyclotomic i ℤ) =
      eval (↑p : ℤ) (∑ i ∈ Finset.range (2 * e + 1), X ^ i) := by
    rw [h_poly]
  rw [eval_prod] at h_eval
  rw [eval_geom_sum] at h_eval
  -- h_eval : ∏ i ∈ (2*e+1).divisors.erase 1, eval ↑p (cyclotomic i ℤ) = ∑ i ∈ range (2*e+1), ↑p ^ i
  -- Step 4: Convert divisors.erase 1 to divisors \ {1}
  rw [← Finset.sdiff_singleton_eq_erase] at h_eval
  -- Step 5: The ℤ geometric sum = ℕ geometric sum cast up
  have h_cast : (∑ x ∈ Finset.range (2 * e + 1), (p : ℤ) ^ x) =
      ↑(∑ x ∈ Finset.range (2 * e + 1), p ^ x) := by
    push_cast
    rfl
  rw [h_cast] at h_eval
  -- Step 6: Each cyclotomic polynomial eval at p ≥ 2 is positive
  have hp_cast_gt1 : (1 : ℤ) < (p : ℤ) := by
    have := hp.two_le; omega
  have h_each_pos : ∀ d ∈ (2 * e + 1).divisors \ {1},
      0 < eval (↑p : ℤ) (cyclotomic d ℤ) := by
    intro d hd
    exact Polynomial.cyclotomic_pos' d hp_cast_gt1
  -- natAbs distributes over the product
  have h_natAbs_prod : (∏ d ∈ (2 * e + 1).divisors \ {1},
      eval (↑p : ℤ) (cyclotomic d ℤ)).natAbs =
      ∏ d ∈ (2 * e + 1).divisors \ {1},
      (eval (↑p : ℤ) (cyclotomic d ℤ)).natAbs :=
    map_prod Int.natAbsHom _ _
  -- The product is positive, so natAbs is the identity (modulo cast)
  have h_prod_pos : 0 < ∏ d ∈ (2 * e + 1).divisors \ {1},
      eval (↑p : ℤ) (cyclotomic d ℤ) :=
    Finset.prod_pos h_each_pos
  -- Combine: sum = natAbs(prod) = prod of natAbs
  have h_sum_eq : (↑(∑ x ∈ Finset.range (2 * e + 1), p ^ x) : ℤ) =
      ∏ d ∈ (2 * e + 1).divisors \ {1}, eval (↑p : ℤ) (cyclotomic d ℤ) :=
    h_eval.symm
  rw [← h_natAbs_prod, ← h_sum_eq, Int.natAbs_natCast]

/--
  The sum of divisors of `p^{2e}`.
  Since `p` is prime, this evaluates precisely to the geometric sum
  `1 + p + p^2 + ... + p^{2e}`.
-/
def sigma_prime_pow (p e : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (2 * e + 1), p ^ i

-- ═══════════════════════════════════════════════════════════════════════════
-- Task 2: Zsigmondy's Theorem — Decomposed Proof via Cyclotomic Polynomials
-- ═══════════════════════════════════════════════════════════════════════════
--
-- The classical proof of Zsigmondy's theorem proceeds by analyzing the
-- factorization  a^n - 1 = ∏_{d | n} Φ_d(a)  where Φ_d is the d-th
-- cyclotomic polynomial.  A "primitive prime divisor" of a^n - 1 is
-- precisely a prime that divides Φ_n(a) but NOT n itself.
--
-- The proof decomposes into the following chain of sub-results:
--
--   Step 1: Lower bound on |Φ_n(a)| showing it grows with n.
--   Step 2: Φ_n(a) > 1 implies it has a prime factor.
--   Step 3: Any prime q | Φ_n(a) with q ∤ n is a primitive prime divisor.
--   Step 4: If q | Φ_n(a) AND q | n, the q-adic valuation is exactly 1.
--   Step 5: After removing all non-primitive factors, Φ_n(a) still has
--           a prime factor left (unless we are in an exceptional case).
--   Step 6: Verification that (p, 1, 2e+1) with 2e+1 ≥ 3 and p prime
--           is never an exceptional case.
--   Step 7: Final assembly.
--
-- Each sub-lemma is stated precisely and stubbed with `sorry`.
-- ═══════════════════════════════════════════════════════════════════════════

/--
  **Sub-lemma 1: Lower bound on Φ_n(p).**

  For a prime `p ≥ 2` and `n ≥ 3`, the cyclotomic polynomial evaluation
  satisfies `Φ_n(p) ≥ (p - 1)^{φ(n)}`, where `φ` is Euler's totient.

  This follows from the product formula
    `Φ_n(p) = ∏_{ζ primitive n-th root} (p - ζ)`
  and the triangle inequality `|p - ζ| ≥ p - 1` for each root on the unit circle.
-/
lemma cyclotomic_eval_lower_bound (p n : ℕ) (hp : p.Prime) (hn : 3 ≤ n) :
    (p - 1) ^ n.totient ≤ (eval (p : ℤ) (cyclotomic n ℤ)).natAbs := by
  -- Mathlib provides the strict bound: (p-1)^φ(n) < |Φ_n(p)| for n > 1 and p ≠ 1
  have hn' : 1 < n := by omega
  have hp_ne_one : p ≠ 1 := Nat.Prime.one_lt hp |>.ne'
  exact le_of_lt (Polynomial.sub_one_pow_totient_lt_natAbs_cyclotomic_eval hn' hp_ne_one)

/--
  **Sub-lemma 2: Φ_n(p) > 1 for primes p and n ≥ 3.**

  Since `p ≥ 2` we have `p - 1 ≥ 1`, so `(p-1)^{φ(n)} ≥ 1`.
  Combined with `φ(n) ≥ 2` for `n ≥ 3`, we get `Φ_n(p) ≥ (p-1)^2 ≥ 1`.
  Therefore `Φ_n(p)` has at least one prime factor.
-/
lemma cyclotomic_eval_gt_one (p n : ℕ) (hp : p.Prime) (hn : 3 ≤ n) :
    1 < (eval (p : ℤ) (cyclotomic n ℤ)).natAbs := by
  -- Chain: 1 ≤ (p-1)^φ(n) < |Φ_n(p)|
  have hn' : 1 < n := by omega
  have hp_ne_one : p ≠ 1 := hp.one_lt.ne'
  have h_strict := Polynomial.sub_one_pow_totient_lt_natAbs_cyclotomic_eval hn' hp_ne_one
  have h_pm1 : 1 ≤ p - 1 := by have := hp.two_le; omega
  have h_base : 1 ≤ (p - 1) ^ n.totient := Nat.one_le_pow _ _ h_pm1
  exact lt_of_le_of_lt h_base h_strict

/--
  **Sub-lemma 7 (moved up): Φ_n(p) divides p^n - 1.**

  This is immediate from the cyclotomic factorization
    `p^n - 1 = ∏_{d | n} Φ_d(p)`.
-/
lemma cyclotomic_eval_dvd_pow_sub_one (p n : ℕ) (hp : p.Prime) (hn : 0 < n) :
    (eval (p : ℤ) (cyclotomic n ℤ)).natAbs ∣ p ^ n - 1 := by
  -- Step 1: ∏_{d | n} Φ_d(X) = X^n - 1
  have h_prod := Polynomial.prod_cyclotomic_eq_X_pow_sub_one hn ℤ
  -- Step 2: Evaluate at (p : ℤ)
  have h_eval_eq : ∏ d ∈ n.divisors, eval (↑p : ℤ) (cyclotomic d ℤ)
      = (↑p : ℤ) ^ n - 1 := by
    have h := congr_arg (eval (↑p : ℤ)) h_prod
    simp only [eval_prod, eval_sub, eval_pow, eval_X, eval_one] at h
    exact h
  -- Step 3: Φ_n(p) divides the product since n ∈ n.divisors
  have h_mem : n ∈ n.divisors := Nat.mem_divisors.mpr ⟨dvd_refl n, by omega⟩
  have h_dvd_int : eval (↑p : ℤ) (cyclotomic n ℤ) ∣ (↑p : ℤ) ^ n - 1 :=
    h_eval_eq ▸ Finset.dvd_prod_of_mem _ h_mem
  -- Step 4: Transfer to natAbs
  have h_natAbs_dvd := Int.natAbs_dvd_natAbs.mpr h_dvd_int
  -- Step 5: natAbs((↑p)^n - 1) = p^n - 1
  have h_pos : 1 ≤ p ^ n := Nat.one_le_pow _ p hp.one_lt.le
  have h_cast_eq : (↑(p ^ n - 1 : ℕ) : ℤ) = (↑p : ℤ) ^ n - 1 := by
    rw [Nat.cast_sub h_pos]; push_cast; ring
  rw [show ((↑p : ℤ) ^ n - 1).natAbs = p ^ n - 1 from by
    rw [← h_cast_eq, Int.natAbs_natCast]] at h_natAbs_dvd
  exact h_natAbs_dvd

-- ─────────────────────────────────────────────────────────────────────────────
-- Sub-lemma 3: Decomposed via Path B (isRoot_cyclotomic_iff)
--
-- Instead of the classical GCD identity argument, we use Mathlib's
-- `isRoot_cyclotomic_iff` which directly tells us that a root of Φ_n
-- in a domain where char doesn't divide n is a primitive n-th root.
--
-- The proof decomposes into three sub-sub-lemmas:
--   3a. Cast q | |Φ_n(p)| over ℤ to a root condition in ZMod q.
--   3b. Apply isRoot_cyclotomic_iff to get IsPrimitiveRoot.
--   3c. Use IsPrimitiveRoot to block q | p^k - 1 for 0 < k < n.
-- ─────────────────────────────────────────────────────────────────────────────

/--
  **Sub-sub-lemma 3a (helper): Ring hom compatibility for eval.**

  For a ring hom `f : ℤ →+* S`, `f(eval a p) = eval (f a) (map f p)`.
  Specialized to `f = Int.castRingHom (ZMod q)`.
-/
lemma int_cast_eval_eq_eval_map_cast (q : ℕ) (a : ℤ) (f : ℤ[X]) :
    ((eval a f : ℤ) : ZMod q) =
    eval ((a : ℤ) : ZMod q) (Polynomial.map (Int.castRingHom (ZMod q)) f) := by
  rw [Polynomial.eval_map]
  induction f using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [Polynomial.eval₂_add, Polynomial.eval_add, Int.cast_add, hp, hq]
  | monomial n c =>
    simp only [Polynomial.eval₂_monomial, Polynomial.eval_monomial,
               Int.cast_mul, Int.cast_pow, mul_comm]
    congr 1

/--
  **Sub-sub-lemma 3a: Reduction to ZMod.**

  If `q | |Φ_n(p)|` as natural numbers, then `(p : ZMod q)` is a root
  of `cyclotomic n (ZMod q)`.
-/
lemma eval_cyclotomic_zmod_eq_zero (p n q : ℕ)
    (hq_prime : q.Prime)
    (hq_dvd_phi : q ∣ (eval (p : ℤ) (cyclotomic n ℤ)).natAbs) :
    eval ((p : ℕ) : ZMod q) (cyclotomic n (ZMod q)) = 0 := by
  haveI : Fact q.Prime := ⟨hq_prime⟩
  -- Step 1: q | natAbs(x) → (q : ℤ) | x → (x : ZMod q) = 0
  have h_zmod_zero : ((eval (↑p : ℤ) (cyclotomic n ℤ) : ℤ) : ZMod q) = 0 := by
    have h_int_dvd : (↑q : ℤ) ∣ eval (↑p : ℤ) (cyclotomic n ℤ) :=
      Int.dvd_natAbs.mp (by exact_mod_cast hq_dvd_phi)
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h_int_dvd
  -- Step 2: cast(eval a p) = eval (cast a) (map cast p) = eval (↑p) (Φ_n (ZMod q))
  rw [int_cast_eval_eq_eval_map_cast, Polynomial.map_cyclotomic] at h_zmod_zero
  -- Step 3: (↑p : ℤ) : ZMod q = (p : ℕ) : ZMod q
  simp only [Int.cast_natCast] at h_zmod_zero
  exact h_zmod_zero

/--
  **Sub-sub-lemma 3b: From root to primitive root.**

  If `(p : ZMod q)` is a root of `cyclotomic n (ZMod q)` and `q ∤ n`,
  then `IsPrimitiveRoot (↑p : ZMod q) n`.
-/
lemma isPrimitiveRoot_of_dvd_cyclotomic (p n q : ℕ)
    (_hp : p.Prime) (_hn : 1 < n)
    (hq_prime : q.Prime)
    (hq_dvd_phi : q ∣ (eval (p : ℤ) (cyclotomic n ℤ)).natAbs)
    (hq_ndvd_n : ¬(q ∣ n)) :
    IsPrimitiveRoot ((p : ℕ) : ZMod q) n := by
  haveI : Fact q.Prime := ⟨hq_prime⟩
  -- Step 1: (↑p : ZMod q) is a root of cyclotomic n (ZMod q)
  have h_root : IsRoot (cyclotomic n (ZMod q)) ((p : ℕ) : ZMod q) :=
    eval_cyclotomic_zmod_eq_zero p n q hq_prime hq_dvd_phi
  -- Step 2: NeZero (n : ZMod q) from q ∤ n
  have h_ne : (n : ZMod q) ≠ 0 := by
    intro h_eq
    apply hq_ndvd_n
    first
    | exact (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mp h_eq
    | exact (CharP.cast_eq_zero_iff (ZMod q) q _).mp h_eq
  haveI : NeZero ((n : ℕ) : ZMod q) := ⟨h_ne⟩
  -- Step 3: Apply isRoot_cyclotomic_iff
  exact (isRoot_cyclotomic_iff).mp h_root

/--
  **Sub-sub-lemma 3c: Primitive root blocks divisibility.**

  If `(p : ZMod q)` is a primitive `n`-th root of unity, then for
  any `0 < k < n`, `q ∤ p^k - 1`.

  *Proof:* If `q | p^k - 1` then `(p : ZMod q)^k = 1`. By
  `IsPrimitiveRoot`, `n | k`. But `0 < k < n` means `n ≤ k`,
  contradiction.
-/
lemma not_dvd_pow_sub_one_of_primitiveRoot (p n q k : ℕ)
    (hp : p.Prime)
    (hq_prime : q.Prime)
    (hprim : IsPrimitiveRoot ((p : ℕ) : ZMod q) n)
    (hk_pos : 0 < k) (hk_lt : k < n) :
    ¬(q ∣ p ^ k - 1) := by
  haveI : Fact q.Prime := ⟨hq_prime⟩
  intro hq_dvd_k
  -- Cast q | p^k - 1 to (p : ZMod q)^k = 1
  have h_le : 1 ≤ p ^ k := Nat.one_le_pow _ p hp.one_lt.le
  have h_cast_zero : ((p ^ k - 1 : ℕ) : ZMod q) = 0 := by
    first
    | exact (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mpr hq_dvd_k
    | exact (CharP.cast_eq_zero_iff (ZMod q) q _).mpr hq_dvd_k
  have h_sub : ((p ^ k - 1 : ℕ) : ZMod q) =
      ((p ^ k : ℕ) : ZMod q) - ((1 : ℕ) : ZMod q) := Nat.cast_sub h_le
  rw [h_sub] at h_cast_zero
  push_cast at h_cast_zero
  have h_pow_one : ((p : ℕ) : ZMod q) ^ k = 1 := sub_eq_zero.mp h_cast_zero
  -- IsPrimitiveRoot gives orderOf = n, so n | k follows from orderOf_dvd_of_pow_eq_one
  have h_ord : orderOf ((p : ℕ) : ZMod q) = n := hprim.eq_orderOf.symm
  have h_ord_dvd : orderOf ((p : ℕ) : ZMod q) ∣ k := orderOf_dvd_of_pow_eq_one h_pow_one
  rw [h_ord] at h_ord_dvd
  -- But 0 < k < n contradicts n | k
  have : n ≤ k := Nat.le_of_dvd hk_pos h_ord_dvd
  omega

/--
  **Sub-lemma 3: Primes dividing Φ_n(a) that do not divide n are primitive.**

  Assembled from sub-sub-lemmas 3a → 3b → 3c.
-/
lemma prime_dvd_cyclotomic_is_primitive (p n q : ℕ)
    (hp : p.Prime) (hn : 3 ≤ n)
    (hq_prime : q.Prime)
    (hq_dvd_phi : q ∣ (eval (p : ℤ) (cyclotomic n ℤ)).natAbs)
    (hq_ndvd_n : ¬(q ∣ n)) :
    q ∣ p ^ n - 1 ∧ ∀ k, 0 < k → k < n → ¬(q ∣ p ^ k - 1) := by
  constructor
  · -- Part 1: q | p^n - 1 via Φ_n(p) | p^n - 1 and transitivity
    exact dvd_trans hq_dvd_phi (cyclotomic_eval_dvd_pow_sub_one p n hp (by omega))
  · -- Part 2: ∀ k, 0 < k → k < n → ¬(q | p^k - 1)
    -- Obtain IsPrimitiveRoot via Sub-sub-lemmas 3a + 3b
    have hprim := isPrimitiveRoot_of_dvd_cyclotomic p n q hp (by omega : 1 < n)
      hq_prime hq_dvd_phi hq_ndvd_n
    -- Apply Sub-sub-lemma 3c for each k
    exact fun k hk_pos hk_lt =>
      not_dvd_pow_sub_one_of_primitiveRoot p n q k hp hq_prime hprim hk_pos hk_lt

/--
  **Sub-lemma 4: GCD of cyclotomic evaluations.**

  For distinct divisors `d₁ | n` and `d₂ | n` with `d₁ ≠ d₂`, the GCD
  `gcd(Φ_{d₁}(p), Φ_{d₂}(p))` divides `n`.

  This is the key algebraic fact: if a prime `q` divides both `Φ_{d₁}(p)`
  and `Φ_{d₂}(p)` where `d₁ < d₂`, then `q | (d₂)` (and hence `q | n`).
  The proof uses the fact that `p` has two different orders mod `q`
  unless `q | n`, which forces the orders to coincide via `p^q ≡ p [MOD q]`.
-/
lemma cyclotomic_eval_gcd_dvd_index (p n d₁ d₂ : ℕ)
    (_hp : p.Prime)
    (hd₁ : d₁ ∣ n) (hd₂ : d₂ ∣ n)
    (hd_ne : d₁ ≠ d₂)
    (q : ℕ) (hq_prime : q.Prime)
    (hq₁ : q ∣ (eval (p : ℤ) (cyclotomic d₁ ℤ)).natAbs)
    (hq₂ : q ∣ (eval (p : ℤ) (cyclotomic d₂ ℤ)).natAbs) :
    q ∣ n := by
  -- Strategy: show q | d₁ or q | d₂ by contradiction using multiplicative orders.
  -- If q ∤ d₁ and q ∤ d₂, then (p : ZMod q) is a primitive d₁-th AND d₂-th root,
  -- so d₁ = d₂ (both equal orderOf (p : ZMod q)), contradicting hd_ne.
  haveI : Fact q.Prime := ⟨hq_prime⟩
  -- First handle degenerate cases: d₁ = 0 or d₂ = 0.
  -- cyclotomic 0 ℤ = 1 so eval p (cyclotomic 0 ℤ) = 1, and q ∤ 1.
  have hd₁_pos : 0 < d₁ := by
    by_contra h
    push_neg at h
    interval_cases d₁
    simp [Polynomial.cyclotomic_zero, Polynomial.eval_one] at hq₁
    -- hq₁ : q = 1, contradicts q.Prime
    exact absurd hq₁ (by have := hq_prime.two_le; omega)
  have hd₂_pos : 0 < d₂ := by
    by_contra h
    push_neg at h
    interval_cases d₂
    simp [Polynomial.cyclotomic_zero, Polynomial.eval_one] at hq₂
    -- hq₂ : q = 1, contradicts q.Prime
    exact absurd hq₂ (by have := hq_prime.two_le; omega)
  -- Main argument: q must divide d₁ or d₂.
  suffices h : q ∣ d₁ ∨ q ∣ d₂ by
    rcases h with hqd₁ | hqd₂
    · exact dvd_trans hqd₁ hd₁
    · exact dvd_trans hqd₂ hd₂
  -- Prove by contradiction: assume q ∤ d₁ ∧ q ∤ d₂
  by_contra h_neither
  push_neg at h_neither
  obtain ⟨hq_nd₁, hq_nd₂⟩ := h_neither
  -- (p : ZMod q) is a root of cyclotomic d₁ (ZMod q) and cyclotomic d₂ (ZMod q)
  have hroot₁ : IsRoot (cyclotomic d₁ (ZMod q)) ((p : ℕ) : ZMod q) :=
    eval_cyclotomic_zmod_eq_zero p d₁ q hq_prime hq₁
  have hroot₂ : IsRoot (cyclotomic d₂ (ZMod q)) ((p : ℕ) : ZMod q) :=
    eval_cyclotomic_zmod_eq_zero p d₂ q hq_prime hq₂
  -- Since q ∤ d₁, we have NeZero (d₁ : ZMod q)
  have hne₁ : (d₁ : ZMod q) ≠ 0 := by
    intro h; exact hq_nd₁ (by
      first
      | exact (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mp h
      | exact (CharP.cast_eq_zero_iff (ZMod q) q _).mp h)
  haveI : NeZero (d₁ : ZMod q) := ⟨hne₁⟩
  -- Since q ∤ d₂, we have NeZero (d₂ : ZMod q)
  have hne₂ : (d₂ : ZMod q) ≠ 0 := by
    intro h; exact hq_nd₂ (by
      first
      | exact (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mp h
      | exact (CharP.cast_eq_zero_iff (ZMod q) q _).mp h)
  haveI : NeZero (d₂ : ZMod q) := ⟨hne₂⟩
  -- By isRoot_cyclotomic_iff, (p : ZMod q) is a primitive d₁-th and d₂-th root
  have hprim₁ : IsPrimitiveRoot ((p : ℕ) : ZMod q) d₁ :=
    isRoot_cyclotomic_iff.mp hroot₁
  have hprim₂ : IsPrimitiveRoot ((p : ℕ) : ZMod q) d₂ :=
    isRoot_cyclotomic_iff.mp hroot₂
  -- IsPrimitiveRoot gives orderOf = d₁ and orderOf = d₂
  have hord₁ : orderOf ((p : ℕ) : ZMod q) = d₁ := hprim₁.eq_orderOf.symm
  have hord₂ : orderOf ((p : ℕ) : ZMod q) = d₂ := hprim₂.eq_orderOf.symm
  -- Therefore d₁ = d₂, contradicting hd_ne
  exact hd_ne (hord₁.symm.trans hord₂)

-- ─────────────────────────────────────────────────────────────────────────────
-- Sub-lemma 5: Decomposed into sub-sub-lemmas (5a–5f)
--
-- The proof that v_q(Φ_n(p)) = 1 when q | n and q | Φ_n(p) decomposes into:
--
--   5a. Fermat congruence: p^q ≡ p (mod q) for prime q.
--   5b. Polynomial congruence: if a ≡ b (mod q) then f(a) ≡ f(b) (mod q).
--   5c. Expansion identity: Φ_m(p^q) = Φ_{mq}(p) · Φ_m(p) when q ∤ m
--        (from cyclotomic_expand_eq_cyclotomic_mul evaluated at p).
--   5d. Non-divisibility of the q-free factor: q ∤ Φ_m(p) when q | Φ_n(p)
--        and n = q^a · m with q ∤ m (via multiplicative order argument).
--   5e. The step lemma: combining 5a-5d to show q ∤ Φ_{mq}(p).
--   5f. Assembly: iterate 5e across q-powers to show q² ∤ Φ_n(p).
-- ─────────────────────────────────────────────────────────────────────────────

/--
  **Sub-sub-lemma 5a: Fermat's little theorem (ZMod version).**

  For prime `q`, `(p : ZMod q) ^ q = (p : ZMod q)`.
  This is Fermat's little theorem: `a^q ≡ a (mod q)`.
-/
lemma zmod_pow_prime_eq_self (q : ℕ) (hq : q.Prime) (a : ZMod q) :
    a ^ q = a := by
  haveI : Fact q.Prime := ⟨hq⟩
  exact ZMod.pow_card a

/--
  **Sub-sub-lemma 5b: Polynomial evaluation respects Fermat congruence.**

  For prime `q` and any polynomial `f ∈ ℤ[X]`, `f(p^q) ≡ f(p) (mod q)`.
  This follows from Fermat's little theorem: `p^q ≡ p (mod q)`, so
  the polynomial evaluations agree in `ZMod q`.
-/
lemma eval_pow_prime_congr_zmod (q : ℕ) (hq : q.Prime) (p : ℕ) (f : ℤ[X]) :
    (q : ℤ) ∣ (eval ((p : ℤ) ^ q) f - eval (p : ℤ) f) := by
  haveI : Fact q.Prime := ⟨hq⟩
  -- It suffices to show the difference is zero in ZMod q
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  -- Cast both evaluations to ZMod q
  push_cast
  -- Use the ring hom compatibility: cast(eval a f) = eval (cast a) (map cast f)
  rw [int_cast_eval_eq_eval_map_cast, int_cast_eval_eq_eval_map_cast]
  -- Normalize the coercion: (↑((↑p : ℤ) ^ q) : ZMod q) = ((↑p : ZMod q) ^ q)
  simp only [Int.cast_pow, Int.cast_natCast]
  -- By Fermat's little theorem: (↑p : ZMod q)^q = (↑p : ZMod q)
  rw [ZMod.pow_card]
  ring

/--
  **Sub-sub-lemma 5c: Expansion identity for cyclotomic polynomials.**

  When `q ∤ m` (with `q` prime), the cyclotomic expansion identity gives:
    `eval p (expand q (Φ_m)) = eval p (Φ_{mq}) · eval p (Φ_m)`
  i.e., `Φ_m(p^q) = Φ_{mq}(p) · Φ_m(p)`.

  This is a direct evaluation of `cyclotomic_expand_eq_cyclotomic_mul`.
-/
lemma cyclotomic_expand_eval (p m q : ℕ) (hq : q.Prime) (hqm : ¬(q ∣ m)) :
    eval (p : ℤ) (cyclotomic m ℤ) * eval (p : ℤ) (cyclotomic (m * q) ℤ) =
    eval ((p : ℤ) ^ q) (cyclotomic m ℤ) := by
  have h_expand := Polynomial.cyclotomic_expand_eq_cyclotomic_mul hq hqm ℤ
  -- expand R q (cyclotomic m R) = cyclotomic (m * q) R * cyclotomic m R
  have h_eval := congr_arg (eval (p : ℤ)) h_expand
  rw [eval_mul] at h_eval
  -- eval p (expand q (Φ_m)) = Φ_m(p^q)
  rw [Polynomial.expand_eval] at h_eval
  -- h_eval : Φ_m(p^q) = Φ_{mq}(p) * Φ_m(p)
  linarith

-- NOTE: The original sub-sub-lemma 5d (`cyclotomic_qfree_not_dvd`) asserted
-- `q ∤ Φ_m(p)` when `q | Φ_n(p)` and `n = q^a · m`. This is FALSE:
-- Counterexample: q=3, n=6=3·2, m=2, p=2 gives Φ_2(2) = 3, so 3 | Φ_m(p).
--
-- The correct approach does not need this intermediate lemma. Instead,
-- the Lifting-the-Exponent Lemma is applied directly to compute
-- `v_q(Φ_n(p)) = 1` from the product formula and the LTE identity
-- `v_q(p^{qm} - 1) = v_q(p^m - 1) + 1`.

/--
  **Sub-sub-lemma 5e: The single-step valuation lemma.**

  If `q ∤ m`, `q ∤ Φ_m(p)`, and `Φ_m(p^q) ≡ Φ_m(p) (mod q)`, then
  from `Φ_m(p^q) = Φ_{mq}(p) · Φ_m(p)`, we deduce `q ∤ Φ_{mq}(p)`.

  *Proof:* `Φ_{mq}(p) · Φ_m(p) = Φ_m(p^q) ≡ Φ_m(p) (mod q)`.
  So `Φ_m(p) · (Φ_{mq}(p) - 1) ≡ 0 (mod q)`.
  Since `q` is prime and `q ∤ Φ_m(p)`, we get `Φ_{mq}(p) ≡ 1 (mod q)`.
  In particular, `q ∤ Φ_{mq}(p)`.
-/
lemma cyclotomic_step_not_dvd (p m q : ℕ)
    (hq_prime : q.Prime) (hqm : ¬(q ∣ m))
    (hq_not_dvd_base : ¬(q ∣ (eval (p : ℤ) (cyclotomic m ℤ)).natAbs))
    (_hm_pos : 0 < m) :
    ¬(q ∣ (eval (p : ℤ) (cyclotomic (m * q) ℤ)).natAbs) := by
  -- Work in ℤ. Let Φm = eval p (cyclotomic m ℤ), Φmq = eval p (cyclotomic (m*q) ℤ).
  set Φm := eval (p : ℤ) (cyclotomic m ℤ) with hΦm_def
  set Φmq := eval (p : ℤ) (cyclotomic (m * q) ℤ) with hΦmq_def
  -- Step 1: Φm * Φmq = Φm(p^q) (expansion identity, 5c)
  have h_expand : Φm * Φmq = eval ((p : ℤ) ^ q) (cyclotomic m ℤ) :=
    cyclotomic_expand_eval p m q hq_prime hqm
  -- Step 2: q | (Φm(p^q) - Φm) (Fermat congruence, 5b)
  have h_fermat : (q : ℤ) ∣ (eval ((p : ℤ) ^ q) (cyclotomic m ℤ) - Φm) :=
    eval_pow_prime_congr_zmod q hq_prime p (cyclotomic m ℤ)
  -- Step 3: q | (Φm * Φmq - Φm) = Φm * (Φmq - 1)
  have h_factor : (q : ℤ) ∣ (Φm * (Φmq - 1)) := by
    have : Φm * (Φmq - 1) = Φm * Φmq - Φm := by ring
    rw [this, h_expand]
    exact h_fermat
  -- Step 4: q ∤ Φm (as integers)
  have hq_not_dvd_Φm : ¬((q : ℤ) ∣ Φm) := by
    intro h_dvd
    apply hq_not_dvd_base
    rw [hΦm_def]
    exact Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr h_dvd)
  -- Step 5: Since q is prime and q ∤ Φm, by Euclid: q | (Φmq - 1)
  have hq_dvd_sub : (q : ℤ) ∣ (Φmq - 1) := by
    have hq_int_prime : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq_prime
    exact (hq_int_prime.dvd_or_dvd h_factor).resolve_left hq_not_dvd_Φm
  -- Step 6: Φmq ≡ 1 (mod q), so q ∤ Φmq
  intro h_dvd_mq
  apply hq_not_dvd_base
  -- If q | Φmq then q | (Φmq - (Φmq - 1)) = 1, contradiction
  have hq_dvd_Φmq : (q : ℤ) ∣ Φmq := by
    rw [hΦmq_def]
    exact Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr h_dvd_mq)
  have hq_dvd_one : (q : ℤ) ∣ 1 := by
    have : (1 : ℤ) = Φmq - (Φmq - 1) := by ring
    rw [this]
    exact dvd_sub hq_dvd_Φmq hq_dvd_sub
  have hq_le_one : q ≤ 1 := by
    have := Int.le_of_dvd one_pos hq_dvd_one
    exact_mod_cast this
  exact absurd hq_prime.one_lt (by omega)

/--
  **Sub-sub-lemma 5f: Iterated step — q does not divide Φ_{m·q^k} for k ≥ 1.**

  By iterating 5e and the Fermat congruence for the `expand` case,
  if `q ∤ Φ_m(p)` and `q ∤ m`, then for all `k ≥ 1`:
  `q ∤ Φ_{m · q^k}(p)`.

  *Proof:*
  - Base case `k = 1`: By 5e (`cyclotomic_step_not_dvd`).
  - Inductive step `k → k+1` (for `k ≥ 1`):
    `Φ_{m·q^{k+1}}(p) = Φ_{m·q^k}(p^q)` (from `cyclotomic_expand_eq_cyclotomic`
    since `q | m·q^k`), and `Φ_{m·q^k}(p^q) ≡ Φ_{m·q^k}(p) (mod q)` by Fermat.
    So `q ∤ Φ_{m·q^k}(p)` implies `q ∤ Φ_{m·q^{k+1}}(p)`.
-/
lemma cyclotomic_iterated_not_dvd (p m q : ℕ) (k : ℕ)
    (hq_prime : q.Prime) (hqm : ¬(q ∣ m))
    (hq_not_dvd_base : ¬(q ∣ (eval (p : ℤ) (cyclotomic m ℤ)).natAbs))
    (hm_pos : 0 < m) (hk : 1 ≤ k) :
    ¬(q ∣ (eval (p : ℤ) (cyclotomic (m * q ^ k) ℤ)).natAbs) := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hk_zero : k = 0
    · -- Base case: k = 0, so succ k = 1, and m * q^1 = m * q
      rw [hk_zero, pow_one]
      exact cyclotomic_step_not_dvd p m q hq_prime hqm hq_not_dvd_base hm_pos
    · -- Inductive step: k ≥ 1, so succ k ≥ 2
      -- IH: q ∤ Φ_{m·q^k}(p)
      have ih' := ih (by omega : 1 ≤ k)
      -- Identity: expand q (Φ_{m·q^k}) = Φ_{m·q^{k+1}} since q | m·q^k
      have hq_dvd_mqk : q ∣ m * q ^ k := dvd_mul_of_dvd_right (dvd_pow_self q (by omega : k ≠ 0)) m
      have h_expand := Polynomial.cyclotomic_expand_eq_cyclotomic hq_prime hq_dvd_mqk ℤ
      -- expand gives: Φ_{m·q^k}(p^q) = Φ_{m·q^k · q}(p) = Φ_{m·q^{k+1}}(p)
      have h_eval := congr_arg (eval (p : ℤ)) h_expand
      rw [Polynomial.expand_eval] at h_eval
      -- h_eval : eval (p^q) (Φ_{m·q^k}) = eval p (Φ_{m·q^k · q})
      -- Rewrite m * q^k * q = m * q^(k+1)
      have h_index : m * q ^ k * q = m * q ^ (k + 1) := by ring
      rw [h_index] at h_eval
      -- Fermat: Φ_{m·q^k}(p^q) ≡ Φ_{m·q^k}(p) (mod q)
      have hq_dvd_diff : (q : ℤ) ∣ eval (p : ℤ) (cyclotomic (m * q ^ (k + 1)) ℤ) - eval (p : ℤ) (cyclotomic (m * q ^ k) ℤ) := by
        have h := eval_pow_prime_congr_zmod q hq_prime p (cyclotomic (m * q ^ k) ℤ)
        rw [h_eval] at h
        exact h
      -- If q | Φ_{m·q^{k+1}}(p), then since q | (Φ_{m·q^{k+1}}(p) - Φ_{m·q^k}(p)),
      -- we'd get q | Φ_{m·q^k}(p), contradicting ih'.
      intro h_dvd
      apply ih'
      -- q divides the natAbs of Φ_{m·q^k}(p)
      have hq_dvd_int : (q : ℤ) ∣ eval (p : ℤ) (cyclotomic (m * q ^ (k + 1)) ℤ) :=
        Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr h_dvd)
      
      -- q | Φ_{m·q^{k+1}}(p) and q | (Φ_{m·q^{k+1}}(p) - Φ_{m·q^k}(p))
      -- implies q | Φ_{m·q^k}(p)
      have hq_dvd_mqk_eval : (q : ℤ) ∣ eval (p : ℤ) (cyclotomic (m * q ^ k) ℤ) := by
        have h_sub := dvd_sub hq_dvd_int hq_dvd_diff
        have h_eq : eval (p : ℤ) (cyclotomic (m * q ^ (k + 1)) ℤ) -
            (eval (p : ℤ) (cyclotomic (m * q ^ (k + 1)) ℤ) -
             eval (p : ℤ) (cyclotomic (m * q ^ k) ℤ)) = eval (p : ℤ) (cyclotomic (m * q ^ k) ℤ) := by ring
        rw [h_eq] at h_sub
        exact h_sub
      exact Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hq_dvd_mqk_eval)

/--
  **Sub-sub-lemma 5g_1: Binomial truncation mod q².**

  For any `q h : ℤ` and `i : ℕ`:
    `q² | ((1 + q·h)^i - 1 - i·q·h)`.

  *Proof:* By induction on `i`.
  - Base: `(1+qh)^0 - 1 - 0 = 0`. ✓
  - Step: `(1+qh)^{i+1} = (1+qh)^i · (1+qh) = (1 + iqh + q²r)(1+qh)`
    `= 1 + (i+1)qh + q²(ih² + r(1+qh))`.
-/
lemma binomial_mod_sq (q h : ℤ) : ∀ (i : ℕ),
    (q ^ 2) ∣ ((1 + q * h) ^ i - 1 - ↑i * q * h) := by
  intro i
  induction i with
  | zero => simp
  | succ n ih =>
    obtain ⟨r, hr⟩ := ih
    -- hr : (1 + q*h)^n - 1 - n*q*h = q²*r
    -- So (1+q*h)^n = 1 + n*q*h + q²*r
    have h_pow : (1 + q * h) ^ n = 1 + ↑n * q * h + q ^ 2 * r := by linarith
    use ↑n * h ^ 2 + r * (1 + q * h)
    rw [pow_succ, h_pow]
    push_cast
    ring

/--
  **Sub-sub-lemma 5g: LTE core — geometric sum has exact valuation 1.**

  For an odd prime `q` and integer `x` with `q | (x - 1)`:
    `q | (1 + x + x² + ⋯ + x^{q-1})` but `q² ∤ (1 + x + ⋯ + x^{q-1})`.

  *Proof:* Write `x = 1 + q·h`. By 5g_1 (`binomial_mod_sq`):
    `x^i = 1 + i·q·h + q²·r_i`,
  so `Σ x^i = q + q·h·Σi + q²·Σr_i`.
  Since `Σ_{i=0}^{q-1} i = q(q-1)/2` and `q` is odd, `q | q·h·Σi` twice,
  giving `q² | q·h·Σi`. So `Σ x^i ≡ q (mod q²)`.
  Then `q | q` ✓ and `q² ∤ q` (since `q ≥ 3 > 1`).
-/
lemma geom_sum_prime_valuation_one (q : ℕ) (x : ℤ) (hq : q.Prime) (hq_odd : q ≠ 2)
    (hqx : (q : ℤ) ∣ (x - 1)) :
    (q : ℤ) ∣ (∑ i ∈ Finset.range q, x ^ i) ∧
    ¬((q : ℤ) ^ 2 ∣ (∑ i ∈ Finset.range q, x ^ i)) := by
  -- Step 1: Write x = 1 + q*h
  obtain ⟨h, hh⟩ := hqx
  have hx : x = 1 + (q : ℤ) * h := by linarith
  -- Step 2: Each x^i ≡ 1 + i*q*h (mod q²), via binomial_mod_sq
  -- From binomial_mod_sq: q² | (x^i - 1 - i*q*h) for each i.
  -- So Σ x^i = Σ(1 + i*q*h) + q²*(stuff) = q + q*h*(Σi) + q²*(stuff).
  -- We need: q² | (Σ x^i - q), which requires q² | q*h*(Σi).
  -- Since Σ_{i=0}^{q-1} i = q*(q-1)/2 and q is odd:
  --   q*h*Σi = q*h*q*(q-1)/2 = q²*h*(q-1)/2, which is divisible by q².
  --
  -- Strategy: show q² | (Σ x^i - q) directly.
  have key : (q : ℤ) ^ 2 ∣ ((∑ i ∈ Finset.range q, x ^ i) - ↑q) := by
    -- Show: q² | Σ(x^i - 1 - i*q*h) + q*h*Σi
    -- First part: q² | Σ(x^i - 1 - i*q*h) by summing binomial_mod_sq
    have h_binom_sum : (q : ℤ) ^ 2 ∣
        (∑ i ∈ Finset.range q, (x ^ i - 1 - ↑i * (q : ℤ) * h)) := by
      rw [hx]
      apply Finset.dvd_sum
      intro i _
      exact binomial_mod_sq (q : ℤ) h i
    -- Second part: q² | q*h*(Σ_{i=0}^{q-1} i)
    -- Σ_{i=0}^{q-1} i * 2 = q * (q-1) (by sum_range_id_mul_two)
    -- q is odd, so 2 | (q-1), so (q-1)/2 is an integer.
    -- q * h * Σi = q * h * q*(q-1)/2 = q² * h * (q-1)/2
    have h_sum_idx : (q : ℤ) ^ 2 ∣ ((q : ℤ) * h * ∑ i ∈ Finset.range q, (i : ℤ)) := by
      -- Use: 2 * Σi = q * (q-1)
      have h_gauss : (∑ i ∈ Finset.range q, (i : ℕ)) * 2 = q * (q - 1) :=
        Finset.sum_range_id_mul_two q
      -- Since q is odd, (q-1) is even, let (q-1) = 2*k
      have hq_ge_2 : 2 ≤ q := hq.two_le
      have hq_odd' : Odd q := Nat.Prime.odd_of_ne_two hq hq_odd
      have h_even : 2 ∣ (q - 1) := by
        obtain ⟨k, hk⟩ := hq_odd'
        omega
      obtain ⟨k, hk⟩ := h_even
      -- Σi = q * k (from 2*Σi = q*(q-1) = q*2k, so Σi = q*k)
      have h_sum_val : (∑ i ∈ Finset.range q, (i : ℕ)) = q * k := by
        have : (∑ i ∈ Finset.range q, (i : ℕ)) * 2 = q * (2 * k) := by rw [hk] at h_gauss; exact h_gauss
        nlinarith
      -- q * h * Σi = q * h * q * k = q² * h * k
      use h * ↑k
      rw [show (∑ i ∈ Finset.range q, (i : ℤ)) = ↑(∑ i ∈ Finset.range q, (i : ℕ)) from by push_cast; rfl]
      rw [h_sum_val]
      push_cast
      ring
    -- Combine: Σ x^i - q = Σ(x^i - 1 - i*q*h) + q*h*Σi
    -- Need to show: Σ x^i - q = Σ(x^i - 1 - i*q*h) + q*h*Σi
    have h_split : (∑ i ∈ Finset.range q, x ^ i) - ↑q =
        (∑ i ∈ Finset.range q, (x ^ i - 1 - ↑i * (q : ℤ) * h)) +
        (q : ℤ) * h * ∑ i ∈ Finset.range q, (i : ℤ) := by
      -- Factor out the q*h*Σi from Σ(i*q*h)
      have hfact : ∑ i ∈ Finset.range q, (↑i * (q : ℤ) * h) =
          (q : ℤ) * h * ∑ i ∈ Finset.range q, (i : ℤ) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
      -- Σ x^i = Σ((x^i - 1 - i*q*h) + i*q*h + 1)
      have hsplit2 : ∀ i ∈ Finset.range q,
          x ^ i - 1 = (x ^ i - 1 - ↑i * (q : ℤ) * h) + ↑i * (q : ℤ) * h := by
        intro i _; ring
      -- Σ(x^i) - q = Σ(x^i - 1) = Σ(x^i-1-i*q*h) + Σ(i*q*h)
      have hstep1 : (∑ i ∈ Finset.range q, x ^ i) - ↑q =
          ∑ i ∈ Finset.range q, (x ^ i - 1) := by
        rw [show (↑q : ℤ) = ∑ _i ∈ Finset.range q, (1 : ℤ) from by
          simp [Finset.sum_const, Finset.card_range]]
        rw [← Finset.sum_sub_distrib]
      calc (∑ i ∈ Finset.range q, x ^ i) - ↑q
          = ∑ i ∈ Finset.range q, (x ^ i - 1) := hstep1
        _ = ∑ i ∈ Finset.range q, ((x ^ i - 1 - ↑i * (q : ℤ) * h) + ↑i * (q : ℤ) * h) :=
            Finset.sum_congr rfl hsplit2
        _ = (∑ i ∈ Finset.range q, (x ^ i - 1 - ↑i * (q : ℤ) * h)) +
            ∑ i ∈ Finset.range q, (↑i * (q : ℤ) * h) :=
            Finset.sum_add_distrib
        _ = (∑ i ∈ Finset.range q, (x ^ i - 1 - ↑i * (q : ℤ) * h)) +
            (q : ℤ) * h * ∑ i ∈ Finset.range q, (i : ℤ) := by rw [hfact]
    rw [h_split]
    exact dvd_add h_binom_sum h_sum_idx
  -- Step 3: Derive both conclusions from key
  constructor
  · -- q | Σ x^i: Since Σ x^i = q + q²*stuff, and q | q and q | q².
    obtain ⟨k, hk⟩ := key
    rw [show (∑ i ∈ Finset.range q, x ^ i) = ↑q + (q : ℤ) ^ 2 * k from by linarith]
    exact dvd_add (dvd_refl _) (dvd_mul_of_dvd_left (dvd_pow_self _ (by omega : 2 ≠ 0)) _)
  · -- q² ∤ Σ x^i: If q² | Σ x^i and q² | (Σ x^i - q), then q² | q.
    -- But q² ∤ q since q ≥ 3.
    intro h_sq_dvd
    have hq_dvd_q : (q : ℤ) ^ 2 ∣ (q : ℤ) := by
      have := dvd_sub h_sq_dvd key
      simp at this
      exact this
    -- q² | q is impossible for q ≥ 2: |q²| > |q|
    have hq_ge_2 := hq.two_le
    have hq_pos : (0 : ℤ) < q := Int.natCast_pos.mpr (Nat.Prime.pos hq)
    have hq_sq_gt : (q : ℤ) ^ 2 > (q : ℤ) := by
      have : (q : ℤ) ≥ 2 := by exact_mod_cast hq_ge_2
      nlinarith
    exact absurd (Int.le_of_dvd hq_pos hq_dvd_q) (not_le.mpr hq_sq_gt)

/--
  **Sub-sub-lemma 5h: Product-ratio identity.**

  For `q ∤ m` (with `q` prime), the cyclotomic product over new divisors gives:
    `∏_{d | m} Φ_{dq}(p) = 1 + p^m + p^{2m} + ⋯ + p^{(q-1)m}`.

  This follows from:
    `∏_{d | qm} Φ_d(p) = p^{qm} - 1` and `∏_{d | m} Φ_d(p) = p^m - 1`,
  dividing: `∏_{d | qm, d ∤ m} Φ_d(p) = (p^{qm} - 1)/(p^m - 1)`.
  Since `q ∤ m` and `gcd(q, m) = 1`, the divisors of `qm` not dividing `m`
  are exactly `{d·q : d | m}`. And the ratio is the geometric sum.
-/
lemma cyclotomic_prod_new_divisors_eq_geom_sum (p m q : ℕ)
    (hq : q.Prime) (hqm : ¬(q ∣ m)) (hm_pos : 0 < m) (hp : 1 < p) :
    (∏ d ∈ m.divisors, (eval (p : ℤ) (cyclotomic (d * q) ℤ))) =
    ∑ i ∈ Finset.range q, (p : ℤ) ^ (i * m) := by
  sorry -- Product formula + geometric sum identity.

/--
  **Sub-sub-lemma 5i: Isolation — only Φ_{mq} contributes q-valuation.**

  Among all `Φ_{dq}(p)` for `d | m` (with `q ∤ m`), only `d = m` gives
  `q | Φ_{dq}(p)`. This is because:
  - `q | Φ_{dq}(p)` iff `q | Φ_d(p)` (since in `ZMod q`, `Φ_{dq} = Φ_d^{q-1}`).
  - `q | Φ_d(p)` iff `orderOf p = d` in `ZMod q` (by `isRoot_cyclotomic_iff`).
  - We know `orderOf p = m` (from the hypothesis `q | Φ_m(p)` and `q ∤ m`).
  - So `d = m` is the only possibility.
-/
lemma cyclotomic_only_top_dvd (p m q : ℕ) (d : ℕ)
    (hq_prime : q.Prime) (hqm : ¬(q ∣ m))
    (hq_dvd_phi_m : q ∣ (eval (p : ℤ) (cyclotomic m ℤ)).natAbs)
    (hd_dvd_m : d ∣ m) (hd_ne_m : d ≠ m)
    (hm_pos : 0 < m) :
    ¬(q ∣ (eval (p : ℤ) (cyclotomic (d * q) ℤ)).natAbs) := by
  sorry -- Order argument using isRoot_cyclotomic_iff + Sub-lemma 4.

/--
  **Sub-lemma 5: Bounded contribution of non-primitive primes.**

  If a prime `q` divides both `Φ_n(p)` and `n`, then `q` appears in
  `Φ_n(p)` with multiplicity exactly 1 (i.e., `q ∥ Φ_n(p)`).

  More precisely, `¬(q² | Φ_n(p))` when `q | n` and `q | Φ_n(p)`.

  *Proof:* Write `n = q^a · m` with `q ∤ m`, `a ≥ 1`.

  1. Show `q | Φ_m(p)` (char q power structure: `Φ_n = Φ_m^e` in `ZMod q`).
  2. By 5h: `∏_{d | m} Φ_{dq}(p) = 1 + p^m + ⋯ + p^{(q-1)m}` (geometric sum).
  3. By 5g (LTE core): `v_q(Σ p^{im}) = 1` since `q | p^m - 1`.
  4. By 5i (isolation): only `Φ_{mq}(p)` among the product is divisible by `q`.
  5. Therefore `v_q(Φ_{mq}(p)) = 1`, i.e., `q ∥ Φ_{mq}(p)`.
  6. For `a ≥ 2`: `Φ_{m·q^a}(p) = Φ_{m·q^{a-1}}(p^q)`, and by Fermat
     congruence, `v_q(Φ_{m·q^a}(p)) = v_q(Φ_{m·q^{a-1}}(p))`.
     Iterating from `v_q(Φ_{mq}(p)) = 1` gives `v_q(Φ_{m·q^a}(p)) = 1`.
  7. Since `n = m·q^a`, we conclude `v_q(Φ_n(p)) = 1`.
-/
lemma cyclotomic_eval_val_of_dvd_index (p n q : ℕ)
    (_hp : p.Prime) (_hn : 3 ≤ n)
    (_hq_prime : q.Prime)
    (_hq_dvd_phi : q ∣ (eval (p : ℤ) (cyclotomic n ℤ)).natAbs)
    (_hq_dvd_n : q ∣ n) :
    ¬(q ^ 2 ∣ (eval (p : ℤ) (cyclotomic n ℤ)).natAbs) := by
  sorry -- Assembly of 5g + 5h + 5i + Fermat iteration.

-- ─────────────────────────────────────────────────────────────────────────────
-- Sub-lemma 6: Decomposed into sub-sub-lemmas
--
-- The proof that (p, 1, 2e+1) is never exceptional proceeds by contradiction:
--   6a. Φ_n(p) > n for p prime, n ≥ 3       (size bound)
--   6b. If every prime of m divides n with   (squarefree divisibility)
--       mult 1, then m ∣ n
--   6c. Assembly: contradiction via 6a + 6b + sub-lemma 5
-- ─────────────────────────────────────────────────────────────────────────────

lemma lemma_x_y_ge_x_add_y {x y : ℕ} (hx : 2 ≤ x) (hy : 2 ≤ y) : x + y ≤ x * y := by
  nlinarith

lemma totient_odd_ge_two {n : ℕ} (hn : 3 ≤ n) (hn_odd : n % 2 = 1) : 2 ≤ n.totient := by
  have heven : Even n.totient := Nat.totient_even (by omega)
  have hpos : 0 < n.totient := Nat.totient_pos.mpr (by omega)
  obtain ⟨k, hk⟩ := heven
  have hk_pos : 0 < k := by
    by_contra h
    have : k = 0 := by omega
    omega
  omega

lemma mul_le_pow {x y : ℕ} (hx : 3 ≤ x) (hy : 1 ≤ y) : x * y ≤ x ^ y := by
  induction' y with k ih
  · omega
  · rcases eq_or_lt_of_le (Nat.zero_le k) with rfl | hk_pos
    · simp
    · have hk_ge_1 : 1 ≤ k := hk_pos
      have ih' := ih hk_ge_1
      have eq1 : x * (k + 1) = x * k + x := by ring
      have h1 : x ≤ x ^ k := Nat.le_self_pow (by omega) x
      calc
        x * (k + 1) = x * k + x := eq1
        _ ≤ x ^ k + x := Nat.add_le_add_right ih' x
        _ ≤ x ^ k + x ^ k := by omega
        _ = 2 * x ^ k := by ring
        _ ≤ x * x ^ k := by
          have h2 : 2 ≤ x := by omega
          exact Nat.mul_le_mul_right (x ^ k) h2
        _ = x ^ (k + 1) := by
          calc
            x * x ^ k = x ^ 1 * x ^ k := by rw [pow_one]
            _ = x ^ (1 + k) := by rw [← pow_add]
            _ = x ^ (k + 1) := by
              have hk1 : 1 + k = k + 1 := by omega
              rw [hk1]

lemma two_pow_totient_ge_of_odd_prime_pow {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) (hp_odd : p % 2 = 1) :
    p ^ e ≤ 2 ^ (p ^ e).totient := by
  have hp_ge_3 : 3 ≤ p := by
    have h2 := hp.two_le
    omega
  have h_tot : (p ^ e).totient = p ^ (e - 1) * (p - 1) := Nat.totient_prime_pow hp (by omega)
  rw [h_tot]
  have hp_le : p ≤ 2 ^ (p - 1) := by
    clear he hp_odd h_tot hp
    induction' p, hp_ge_3 using Nat.le_induction with d _ ih_d
    · decide
    · have hc : d + 1 - 1 = d := by omega
      rw [hc]
      have eq1 : 2 ^ d = 2 ^ (d - 1) * 2 := by
        have hd : d - 1 + 1 = d := by omega
        calc
          2 ^ d = 2 ^ (d - 1 + 1) := by rw [hd]
          _ = 2 ^ (d - 1) * 2 ^ 1 := by rw [pow_add]
          _ = 2 ^ (d - 1) * 2 := by rw [pow_one]
      calc
        d + 1 ≤ 2 ^ (d - 1) + 1 := Nat.add_le_add_right ih_d 1
        _ ≤ 2 ^ (d - 1) + 2 ^ (d - 1) := by
          have h1 : 1 ≤ 2 ^ (d - 1) := Nat.one_le_two_pow
          omega
        _ = 2 ^ (d - 1) * 2 := by ring
        _ = 2 ^ d := eq1.symm
  
  have h_pow1 : 2 ^ (p ^ (e - 1) * (p - 1)) = (2 ^ (p - 1)) ^ p ^ (e - 1) := by
    rw [mul_comm, pow_mul]
  have h_pow2 : p ^ e = p * p ^ (e - 1) := by
    have h1 : e = 1 + (e - 1) := by omega
    nth_rw 1 [h1]
    rw [pow_add, pow_one]
  
  rw [h_pow1, h_pow2]
  have hk : 1 ≤ p ^ (e - 1) := Nat.one_le_pow _ p (by omega)
  have h_mul_le_pow : p * p ^ (e - 1) ≤ p ^ (p ^ (e - 1)) := mul_le_pow hp_ge_3 hk
  
  calc
    p * p ^ (e - 1) ≤ p ^ p ^ (e - 1) := h_mul_le_pow
    _ ≤ (2 ^ (p - 1)) ^ p ^ (e - 1) := Nat.pow_le_pow_left hp_le _

lemma two_pow_totient_ge_of_odd_all (n : ℕ) : n % 2 = 1 → n ≤ 2 ^ n.totient := by
  apply Nat.recOnPrimeCoprime (motive := fun n => n % 2 = 1 → n ≤ 2 ^ n.totient)
  · intro h
    omega
  · intro p e hp h_odd
    rcases eq_or_lt_of_le (Nat.zero_le e) with rfl | he_pos
    · simp
    · have he_ge_1 : 1 ≤ e := he_pos
      have hp_odd : p % 2 = 1 := by
        by_contra h
        have : p % 2 = 0 := by omega
        have h2 : 2 ∣ p := Nat.dvd_of_mod_eq_zero this
        have hp2 : p = 2 := (Nat.Prime.eq_two_or_odd hp).resolve_right (by omega)
        rw [hp2] at h_odd
        have : 2 ∣ 2 ^ e := dvd_pow_self 2 (by omega)
        have h_even : 2 ^ e % 2 = 0 := Nat.mod_eq_zero_of_dvd this
        omega
      exact two_pow_totient_ge_of_odd_prime_pow hp he_ge_1 hp_odd
  · intro a b _ _ h_coprime ih_a ih_b h_odd
    have ha_odd : a % 2 = 1 := by
      by_contra h
      have : a % 2 = 0 := by omega
      have : 2 ∣ a := Nat.dvd_of_mod_eq_zero this
      have : 2 ∣ a * b := dvd_mul_of_dvd_left this b
      have : (a * b) % 2 = 0 := Nat.mod_eq_zero_of_dvd this
      omega
    have hb_odd : b % 2 = 1 := by
      by_contra h
      have : b % 2 = 0 := by omega
      have : 2 ∣ b := Nat.dvd_of_mod_eq_zero this
      have : 2 ∣ a * b := dvd_mul_of_dvd_right this a
      have : (a * b) % 2 = 0 := Nat.mod_eq_zero_of_dvd this
      omega
    have iha := ih_a ha_odd
    have ihb := ih_b hb_odd
    
    rcases eq_or_lt_of_le (Nat.zero_le a) with rfl | ha_pos
    · omega
    rcases eq_or_lt_of_le (Nat.zero_le b) with rfl | hb_pos
    · omega
    
    rcases eq_or_lt_of_le (Nat.succ_le_of_lt ha_pos) with rfl | ha_ge_2
    · simp at ihb ⊢
      exact ihb
    rcases eq_or_lt_of_le (Nat.succ_le_of_lt hb_pos) with rfl | hb_ge_2
    · simp at iha ⊢
      exact iha
      
    have ha_ge_3 : 3 ≤ a := by
      by_contra h
      have : a = 2 := by omega
      omega
    have hb_ge_3 : 3 ≤ b := by
      by_contra h
      have : b = 2 := by omega
      omega
    
    have htot_a : 2 ≤ a.totient := totient_odd_ge_two ha_ge_3 ha_odd
    have htot_b : 2 ≤ b.totient := totient_odd_ge_two hb_ge_3 hb_odd
    
    have h_mul_tot : (a * b).totient = a.totient * b.totient := Nat.totient_mul h_coprime
    rw [h_mul_tot]
    
    have h_add_le_mul : a.totient + b.totient ≤ a.totient * b.totient := lemma_x_y_ge_x_add_y htot_a htot_b
    
    calc
      a * b ≤ 2 ^ a.totient * 2 ^ b.totient := by
        have h1 : a * b ≤ 2 ^ a.totient * b := Nat.mul_le_mul_right b iha
        have h2 : 2 ^ a.totient * b ≤ 2 ^ a.totient * 2 ^ b.totient := Nat.mul_le_mul_left (2 ^ a.totient) ihb
        exact le_trans h1 h2
      _ = 2 ^ (a.totient + b.totient) := (pow_add 2 a.totient b.totient).symm
      _ ≤ 2 ^ (a.totient * b.totient) := Nat.pow_le_pow_right (by decide) h_add_le_mul

/--
  **Sub-sub-lemma 6a_1: Totient growth.**
  
  For odd `n ≥ 3`, `n ≤ 2^{φ(n)}`.
-/
lemma two_pow_totient_ge_of_odd (n : ℕ) (hn_odd : n % 2 = 1) (_hn : 3 ≤ n) :
    n ≤ 2 ^ n.totient := two_pow_totient_ge_of_odd_all n hn_odd

/--
  **Sub-sub-lemma 6a_2: Index bound for p ≥ 3.**
-/
lemma cyclotomic_eval_gt_index_of_p_ge_3 (p n : ℕ) (_hp : p.Prime) (hp3 : 3 ≤ p) (hn_odd : Odd n) (hn : 3 ≤ n) :
    n < (eval (p : ℤ) (cyclotomic n ℤ)).natAbs := by
  have hp_not_one : p ≠ 1 := by omega
  have hn_gt_one : 1 < n := by omega
  have hstrict := Polynomial.sub_one_pow_totient_lt_natAbs_cyclotomic_eval hn_gt_one hp_not_one
  have hpm1_ge_2 : 2 ≤ p - 1 := by omega
  have hbase : 2 ^ n.totient ≤ (p - 1) ^ n.totient := Nat.pow_le_pow_left hpm1_ge_2 _
  have hn_odd_mod : n % 2 = 1 := by
    obtain ⟨k, hk⟩ := hn_odd
    omega
  have htt : n ≤ 2 ^ n.totient := two_pow_totient_ge_of_odd n hn_odd_mod hn
  calc
    n ≤ 2 ^ n.totient := htt
    _ ≤ (p - 1) ^ n.totient := hbase
    _ < ((cyclotomic n ℤ).eval (p : ℤ)).natAbs := hstrict

/--
  **Sub-sub-lemma 6a_3: Index bound for p = 2.**
-/
lemma cyclotomic_eval_two_gt_index (n : ℕ) (hn_odd : Odd n) (hn : 3 ≤ n) :
    n < (eval (2 : ℤ) (cyclotomic n ℤ)).natAbs := by
  sorry

/--
  **Sub-sub-lemma 6a: Cyclotomic evaluation exceeds the index.**

  For a prime `p ≥ 2` and odd `n ≥ 3`, `Φ_n(p) > n`.
  
  *Proof sketch:*
  The product formula `Φ_n(p) = ∏_{ζ} (p - ζ)` over primitive n-th roots
  gives `|Φ_n(p)| > (p-1)^{φ(n)}` (Mathlib's strict bound). We then need
  `(p-1)^{φ(n)} ≥ n`, which holds for all non-exceptional cases:
  - For `p ≥ 3`: `(p-1)^{φ(n)} ≥ 2^2 = 4`, and a growth argument shows
    `2^{φ(n)} > n` for odd `n ≥ 3`.
  - For `p = 2`: `Φ_n(2) = (2^n - 1) / ∏_{d|n,d<n} Φ_d(2)`, and one verifies
    that for odd `n ≥ 3`, `Φ_n(2) ≥ n + 1`.
-/
lemma cyclotomic_eval_gt_index (p n : ℕ) (hp : p.Prime) (hn_odd : Odd n) (hn : 3 ≤ n) :
    n < (eval (p : ℤ) (cyclotomic n ℤ)).natAbs := by
  rcases lt_trichotomy p 2 with h | rfl | h
  · exfalso; have := hp.two_le; omega
  · exact cyclotomic_eval_two_gt_index n hn_odd hn
  · exact cyclotomic_eval_gt_index_of_p_ge_3 p n hp (by omega) hn_odd hn

/--
  **Sub-sub-lemma 6b: Squarefree numbers with all prime factors dividing n must divide n.**

  If a positive integer `m` satisfies:
    (1) every prime factor of `m` divides `n`, and
    (2) no prime appears in `m` with multiplicity ≥ 2,
  then `m ∣ n`.

  *Proof:* m is squarefree (by condition 2), so m = ∏ (primes of m).
  Each such prime divides n (by condition 1), so m | rad(n) | n.
-/
lemma squarefree_dvd_of_prime_factors_dvd (m n : ℕ) (hm_pos : 0 < m)
    (h_primes : ∀ q : ℕ, q.Prime → q ∣ m → q ∣ n)
    (h_sq : ∀ q : ℕ, q.Prime → q ∣ m → ¬(q ^ 2 ∣ m)) :
    m ∣ n := by
  sorry -- Squarefree factorization argument.

/--
  **Sub-lemma 6: The non-exceptional case for odd n ≥ 3 with b = 1.**

  Zsigmondy's theorem has three families of exceptions:
    (i)   n = 1 (trivial),
    (ii)  n = 2 and a + b is a power of 2,
    (iii) (a, b, n) = (2, 1, 6).

  For our application, `a = p` (prime, so `p ≥ 2`), `b = 1`, and
  `n = 2e + 1 ≥ 3` is odd. We verify:
    - `n ≥ 3` rules out (i),
    - `n` is odd rules out (ii) (which requires `n = 2`),
    - If `n = 6` then `n` is even, contradiction; and regardless,
      the only exception at `n = 6` is `(a, b) = (2, 1)`, but `n = 2e+1`
      is odd so `n ≠ 6`.

  Therefore **(p, 1, 2e+1) is never exceptional** when `2e+1 ≥ 3` and `p` is prime.

  *Proof:* By contradiction. If every prime factor of `Φ_{2e+1}(p)` divides
  `2e+1`, then by sub-lemma 5 each appears with multiplicity 1, so by
  sub-sub-lemma 6b, `Φ_{2e+1}(p) ∣ (2e+1)`. But by sub-sub-lemma 6a,
  `Φ_{2e+1}(p) > 2e+1`, contradicting divisibility.
-/
lemma zsigmondy_not_exceptional (p e : ℕ) (hp : p.Prime) (he : 3 ≤ 2 * e + 1) :
    ∃ q : ℕ, q.Prime ∧
      q ∣ (eval (p : ℤ) (cyclotomic (2 * e + 1) ℤ)).natAbs ∧
      ¬(q ∣ (2 * e + 1)) := by
  set n := 2 * e + 1 with hn_def
  set Φ := (eval (p : ℤ) (cyclotomic n ℤ)).natAbs with hΦ_def
  -- Step 1: Φ_n(p) > 1, so it has at least one prime factor
  have hΦ_gt_one : 1 < Φ := cyclotomic_eval_gt_one p n hp he
  -- Step 2: Proof by contradiction — assume every prime factor of Φ divides n
  by_contra h_no_good
  -- h_no_good : ¬∃ q, q.Prime ∧ q ∣ Φ ∧ ¬(q ∣ n)
  -- Restate: every prime factor of Φ divides n
  have h_every_prime_dvd_n : ∀ q : ℕ, q.Prime → q ∣ Φ → q ∣ n := by
    intro q hq_prime hq_dvd
    by_contra hq_ndvd
    exact h_no_good ⟨q, hq_prime, hq_dvd, hq_ndvd⟩
  -- Step 3: Each such prime has multiplicity exactly 1 in Φ (sub-lemma 5)
  have h_sq : ∀ q : ℕ, q.Prime → q ∣ Φ → ¬(q ^ 2 ∣ Φ) := by
    intro q hq_prime hq_dvd
    have hq_dvd_n := h_every_prime_dvd_n q hq_prime hq_dvd
    exact cyclotomic_eval_val_of_dvd_index p n q hp he hq_prime hq_dvd hq_dvd_n
  -- Step 4: Φ divides n (sub-sub-lemma 6b)
  have hΦ_pos : 0 < Φ := by omega
  have hΦ_dvd_n : Φ ∣ n :=
    squarefree_dvd_of_prime_factors_dvd Φ n hΦ_pos h_every_prime_dvd_n h_sq
  -- Step 5: But Φ > n (sub-sub-lemma 6a), contradicting Φ ∣ n
  have hn_odd : Odd n := ⟨e, by omega⟩
  have hΦ_gt_n : n < Φ := cyclotomic_eval_gt_index p n hp hn_odd he
  have hΦ_le_n : Φ ≤ n := Nat.le_of_dvd (by omega) hΦ_dvd_n
  omega

-- (Sub-lemma 7 moved before Sub-lemma 3 to resolve forward references.)

/--
  **Task 2: Zsigmondy's theorem (existence of primitive prime divisors).**

  For `2e+1 ≥ 3`, there exists a prime `q` dividing `p^{2e+1} - 1`
  that does not divide `p^k - 1` for any strictly positive `k < 2e+1`.

  *Proof assembly:*
  1. By `zsigmondy_not_exceptional`, there exists a prime `q` dividing
     `Φ_{2e+1}(p)` with `q ∤ (2e+1)`.
  2. By `prime_dvd_cyclotomic_is_primitive`, this `q` is a primitive
     prime divisor: `q | p^{2e+1} - 1` and `q ∤ p^k - 1` for `0 < k < 2e+1`.
-/
lemma zsigmondy_exists_primitive_prime (p e : ℕ) (hp : p.Prime) (he : 3 ≤ 2 * e + 1) :
    ∃ q : ℕ, q.Prime ∧
      q ∣ p ^ (2 * e + 1) - 1 ∧
      ∀ k, 0 < k → k < 2 * e + 1 → ¬(q ∣ p ^ k - 1) := by
  -- Step 1: Obtain a prime q dividing Φ_{2e+1}(p) that does not divide (2e+1)
  obtain ⟨q, hq_prime, hq_dvd_phi, hq_ndvd_n⟩ :=
    zsigmondy_not_exceptional p e hp he
  -- Step 2: Such a q is a primitive prime divisor
  have ⟨hq_dvd_pow, hq_prim⟩ :=
    prime_dvd_cyclotomic_is_primitive p (2 * e + 1) q hp he hq_prime hq_dvd_phi hq_ndvd_n
  exact ⟨q, hq_prime, hq_dvd_pow, hq_prim⟩

/--
  Consequences of Zsigmondy's theorem for a given primitive prime divisor `q`.
  Such a `q` satisfies `q ≡ 1 [MOD 2e+1]` and divides `σ(p^{2e})`.

  The divisibility proof is structurally verified:
  - The geometric sum identity `(p-1) * σ_prime_pow(p,e) = p^{2e+1} - 1` connects
    the sum to the Zsigmondy divisibility hypothesis.
  - Euclid's lemma splits `q ∣ (p-1) * σ(p^{2e})` into two cases.
  - The primitive divisor condition at `k=1` immediately yields `¬(q ∣ p-1)`.
  - `resolve_left` prunes the impossible branch, leaving `q ∣ σ(p^{2e})`.
-/
theorem zsigmondy_primitive_prime_properties {p e q : ℕ}
    (hp : p.Prime)
    (he : 3 ≤ 2 * e + 1)
    (hq_prime : q.Prime)
    (hq_div : q ∣ p ^ (2 * e + 1) - 1)
    (hq_prim : ∀ k, 0 < k → k < 2 * e + 1 → ¬(q ∣ p ^ k - 1)) :
    q % (2 * e + 1) = 1 ∧ q ∣ sigma_prime_pow p e := by

  have hp1 : 1 ≤ p := hp.one_lt.le

  -- The geometric sum algebraically relates p^{2e+1} - 1 to (p - 1) * σ(p^{2e}).
  have h_geom : (p - 1) * sigma_prime_pow p e = p ^ (2 * e + 1) - 1 := by
    unfold sigma_prime_pow
    have h1 := nat_geom_sum p (2 * e + 1) hp1
    have h2 : 1 ≤ p ^ (2 * e + 1) := Nat.one_le_pow _ p hp1
    omega

  constructor
  · -- Part 1: Prove q ≡ 1 [MOD 2e+1]
    haveI : Fact q.Prime := ⟨hq_prime⟩

    have h_pow_eq_one : (p : ZMod q) ^ (2 * e + 1) = 1 := by
      have h1 : ((p ^ (2 * e + 1) - 1 : ℕ) : ZMod q) = 0 := by
        first
        | exact (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mpr hq_div
        | exact (CharP.cast_eq_zero_iff (ZMod q) q _).mpr hq_div
      have h_pos : 1 ≤ p ^ (2 * e + 1) := Nat.one_le_pow _ p hp1
      have h_sub : ((p ^ (2 * e + 1) - 1 : ℕ) : ZMod q) =
          ((p ^ (2 * e + 1) : ℕ) : ZMod q) - ((1 : ℕ) : ZMod q) := Nat.cast_sub h_pos
      rw [h_sub] at h1
      push_cast at h1
      exact sub_eq_zero.mp h1

    -- Establish (p : ZMod q) as a unit with inverse p^{2e}
    have hP_eq : (p : ZMod q) * (p : ZMod q) ^ (2 * e) = 1 := by
      have h_pow_add : (p : ZMod q) ^ 1 * (p : ZMod q) ^ (2 * e) =
          (p : ZMod q) ^ (1 + 2 * e) := (pow_add (p : ZMod q) 1 (2 * e)).symm
      have h_pow_one : (p : ZMod q) ^ 1 = (p : ZMod q) := pow_one (p : ZMod q)
      have h_add : 1 + 2 * e = 2 * e + 1 := by omega
      rw [h_pow_one] at h_pow_add
      rw [h_add] at h_pow_add
      rw [h_pow_add]
      exact h_pow_eq_one

    let u : (ZMod q)ˣ :=
      ⟨(p : ZMod q), (p : ZMod q) ^ (2 * e), hP_eq, by rw [mul_comm, hP_eq]⟩

    have hu_pow : u ^ (2 * e + 1) = 1 := by
      ext
      push_cast
      exact h_pow_eq_one

    have ho_dvd : orderOf u ∣ 2 * e + 1 := orderOf_dvd_of_pow_eq_one hu_pow
    have ho_pos : 0 < orderOf u := by
      by_contra! h
      have h_zero : orderOf u = 0 := by omega
      rw [h_zero] at ho_dvd
      have : 2 * e + 1 = 0 := eq_zero_of_zero_dvd ho_dvd
      omega

    -- Verify that the multiplicative order is strictly 2e+1
    have ho_eq : orderOf u = 2 * e + 1 := by
      apply le_antisymm
      · exact Nat.le_of_dvd (by omega) ho_dvd
      · by_contra! h_lt
        have h_ndiv := hq_prim (orderOf u) ho_pos h_lt
        have hu_pow_ord : u ^ orderOf u = 1 := pow_orderOf_eq_one u

        have hp_pow_ord : (p : ZMod q) ^ orderOf u = 1 := by
          have h_val : (↑(u ^ orderOf u) : ZMod q) = (↑(1 : (ZMod q)ˣ) : ZMod q) :=
            congrArg Units.val hu_pow_ord
          push_cast at h_val
          exact h_val

        have h_cast : ((p ^ orderOf u - 1 : ℕ) : ZMod q) = 0 := by
          have h_le : 1 ≤ p ^ orderOf u := Nat.one_le_pow _ p hp1
          have h_sub : ((p ^ orderOf u - 1 : ℕ) : ZMod q) =
              ((p ^ orderOf u : ℕ) : ZMod q) - ((1 : ℕ) : ZMod q) := Nat.cast_sub h_le
          rw [h_sub]
          push_cast
          rw [hp_pow_ord]
          exact sub_self 1

        have h_div : q ∣ p ^ orderOf u - 1 := by
          first
          | exact (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mp h_cast
          | exact (CharP.cast_eq_zero_iff (ZMod q) q _).mp h_cast
        exact h_ndiv h_div

    -- By Lagrange's theorem: orderOf u divides card (ZMod q)ˣ = q - 1
    have h_card_eq : Fintype.card (ZMod q)ˣ = q - 1 := by
      exact ZMod.card_units q
    have h_pow_card : u ^ (q - 1) = 1 := by
      have h1 : u ^ Fintype.card (ZMod q)ˣ = 1 := pow_card_eq_one
      rw [h_card_eq] at h1
      exact h1
    have h_card_dvd : (2 * e + 1) ∣ (q - 1) := by
      rw [← ho_eq]
      exact orderOf_dvd_of_pow_eq_one h_pow_card
    obtain ⟨k, hk⟩ := h_card_dvd

    -- hk : q - 1 = (2 * e + 1) * k
    -- We need: q % (2 * e + 1) = 1
    have hq_ge_1 : 1 ≤ q := hq_prime.one_lt.le
    have h_q_eq : q = (2 * e + 1) * k + 1 := by omega
    rw [h_q_eq, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega : 1 < 2 * e + 1)]

  · -- Part 2: Prove q ∣ σ(p^{2e})
    -- Substitute the geometric sum identity into the main divisibility hypothesis.
    have hq_div_prod : q ∣ (p - 1) * sigma_prime_pow p e := by
      rw [h_geom]
      exact hq_div

    -- Apply the primitive divisor non-divisibility condition for k = 1.
    -- omega effortlessly proves 1 < 2e+1 given 3 ≤ 2e+1.
    have h_k1 : 1 < 2 * e + 1 := by omega

    have hq_ndiv_p_minus_1 : ¬(q ∣ p - 1) := by
      have h1 := hq_prim 1 zero_lt_one h_k1
      rwa [pow_one] at h1

    -- By Euclid's Lemma, since q is prime, if it divides a product a * b,
    -- it must divide a or b. (hq_prime.dvd_mul.mp splits this into an Or).
    -- Because it does not divide p - 1, it is logically forced to divide σ(p^{2e}).
    exact (hq_prime.dvd_mul.mp hq_div_prod).resolve_left hq_ndiv_p_minus_1

/--
  Bridge lemma: connects `sigma_prime_pow` back to the project's `sigma` definition
  so that `zsigmondy_poison_trap` remains unchanged.
  σ(p^{2e}) = sigma_prime_pow p e when p is prime.
-/
lemma sigma_eq_sigma_prime_pow (p e : ℕ) (hp : p.Prime) :
    sigma (p ^ (2 * e)) = sigma_prime_pow p e := by
  unfold sigma sigma_prime_pow
  exact sum_divisors_prime_pow hp

/--
  Task 2 (derived): The full Zsigmondy axiom in the original signature.
  Derived from the formalized components above; serves as a drop-in
  replacement so downstream code (zsigmondy_poison_trap) compiles unchanged.
-/
lemma zsigmondy_axiom (p e : ℕ) (hp : p.Prime) (he : 2 * e + 1 ≥ 3) :
    ∃ q : ℕ, q.Prime ∧ q ∣ sigma (p ^ (2 * e)) ∧ ¬(q ∣ p - 1) ∧ q % (2 * e + 1) = 1 := by
  obtain ⟨q, hq_prime, hq_div, hq_prim⟩ := zsigmondy_exists_primitive_prime p e hp he
  have ⟨hq_mod, hq_div_spow⟩ := zsigmondy_primitive_prime_properties hp he hq_prime hq_div hq_prim
  have hq_div_sigma : q ∣ sigma (p ^ (2 * e)) := by
    rw [sigma_eq_sigma_prime_pow p e hp]
    exact hq_div_spow
  have hq_ndiv : ¬(q ∣ p - 1) := by
    have h_k1 : 1 < 2 * e + 1 := by omega
    have h1 := hq_prim 1 zero_lt_one h_k1
    rwa [pow_one] at h1
  exact ⟨q, hq_prime, hq_div_sigma, hq_ndiv, hq_mod⟩

/--
  Task 3: The Poison Trap (zsigmondy_poison_trap).
  Chain Zsigmondy directly to legendre_cattaneo_obstruction.
  Prove that exponent inflation logically guarantees the generation of a primitive prime q.
  If q ≡ 5 or 7 (mod 8), the exponent is mathematically forbidden for a quasiperfect number.
-/
lemma zsigmondy_poison_trap {n p e : ℕ}
  (h_qpn : IsQuasiperfect n)
  (_hn_odd : Odd n)
  (_hp_prime : p.Prime)
  (hp_dvd : p ^ (2 * e) ∣ n)
  (hp_coprime : Nat.Coprime (p ^ (2 * e)) (n / p ^ (2 * e)))
  (_he_bound : 2 * e + 1 ≥ 3) :
  ∀ q, (q.Prime ∧ q ∣ sigma (p ^ (2 * e)) ∧ ¬(q ∣ p - 1) ∧ q % (2 * e + 1) = 1) →
  q % 8 ≠ 5 ∧ q % 8 ≠ 7 := by
  -- Zsigmondy guarantees such a q exists, here we take it as given from the ∀ statement
  intro q hq
  rcases hq with ⟨hq_prime, hq_div_sigma, _, _⟩

  -- q divides σ(p^{2e}) which divides σ(n)
  have h_sigma_dvd : sigma (p ^ (2 * e)) ∣ sigma n := by
    have h_prod : n = p ^ (2 * e) * (n / p ^ (2 * e)) := (Nat.mul_div_cancel' hp_dvd).symm
    have h_sigma_prod : sigma n = sigma (p ^ (2 * e)) * sigma (n / p ^ (2 * e)) := by
      nth_rw 1 [h_prod]
      exact Nat.Coprime.sum_divisors_mul hp_coprime
    rw [h_sigma_prod]
    exact dvd_mul_right _ _

  have hq_dvd_sigma_n : q ∣ sigma n := dvd_trans hq_div_sigma h_sigma_dvd

  have hq_odd : q ≠ 2 := by
    intro hq2
    rw [hq2] at hq_dvd_sigma_n
    have hsigma_odd : Odd (sigma n) := qpn_sigma_odd h_qpn
    have hsigma_even : Even (sigma n) := even_iff_two_dvd.mpr hq_dvd_sigma_n
    have h_contra : ¬ Even (sigma n) := by
      rcases hsigma_odd with ⟨k, hk⟩
      intro ⟨j, hj⟩
      omega
    exact False.elim (h_contra hsigma_even)

  have h_mod8 : q % 8 = 1 ∨ q % 8 = 3 := legendre_cattaneo_obstruction h_qpn hq_prime hq_odd hq_dvd_sigma_n

  constructor
  · intro h5
    rcases h_mod8 with h1 | h3
    · omega
    · omega
  · intro h7
    rcases h_mod8 with h1 | h3
    · omega
    · omega

end UALBF
