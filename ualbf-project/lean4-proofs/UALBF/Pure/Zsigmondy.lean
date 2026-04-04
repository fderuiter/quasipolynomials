import UALBF.Pure.Cyclotomic

/-!
# Zsigmondy's Theorem

The classical theorem proving existence of primitive prime divisors
for p^n - 1, assembled from the cyclotomic machinery in Pure.Cyclotomic.

No QPN hypothesis — pure, upstreamable mathematics.
-/

namespace UALBF.Pure.Zsigmondy

open UALBF UALBF.Pure.Cyclotomic UALBF.Pure.Arithmetic
open Finset Nat Polynomial

/--
  Squarefree divisibility from prime-factor containment.

  If a positive integer `m` satisfies:
    (1) every prime factor of `m` divides `n`, and
    (2) no prime appears in `m` with multiplicity ≥ 2,
  then `m ∣ n`.

  *Proof:* `m` is squarefree (by condition 2), so `m = ∏ (primes of m)`.
  Each such prime divides `n` (by condition 1), so `m | rad(n) | n`.
-/
lemma squarefree_dvd_of_prime_factors_dvd (m n : ℕ) (_hm_pos : 0 < m)
    (h_primes : ∀ q : ℕ, q.Prime → q ∣ m → q ∣ n)
    (h_sq : ∀ q : ℕ, q.Prime → q ∣ m → ¬(q ^ 2 ∣ m)) :
    m ∣ n := by
  apply (Nat.dvd_iff_prime_pow_dvd_dvd n m).mpr
  intro p k hp hpk_dvd_m
  rcases Nat.eq_zero_or_pos k with rfl | hk_pos
  · rw [pow_zero]
    exact one_dvd n
  · have hk_ge_1 : 1 ≤ k := hk_pos
    rcases eq_or_lt_of_le hk_ge_1 with rfl | hk_gt_1
    · rw [pow_one] at hpk_dvd_m ⊢
      exact h_primes p hp hpk_dvd_m
    · have h_k_ge_2 : 2 ≤ k := hk_gt_1
      have h_p2_dvd : p ^ 2 ∣ m := dvd_trans (pow_dvd_pow p h_k_ge_2) hpk_dvd_m
      have h_p_dvd_m : p ∣ m := by
        have h1 : p ∣ p ^ k := dvd_pow_self p (Nat.ne_of_gt hk_pos)
        exact dvd_trans h1 hpk_dvd_m
      exact False.elim (h_sq p hp h_p_dvd_m h_p2_dvd)

/--
  Non-exceptional case for Zsigmondy's theorem.

  Zsigmondy's theorem has three families of exceptions:
    (i)   `n = 1` (trivial),
    (ii)  `n = 2` and `a + b` is a power of 2,
    (iii) `(a, b, n) = (2, 1, 6)`.

  For our application, `a = p` (prime, so `p ≥ 2`), `b = 1`, and
  `n = 2e + 1 ≥ 3` is odd. We verify:
    - `n ≥ 3` rules out (i),
    - `n` is odd rules out (ii) (which requires `n = 2`),
    - `n = 2e + 1` is odd so `n ≠ 6`, ruling out (iii).

  Therefore `(p, 1, 2e+1)` is never exceptional when `2e+1 ≥ 3` and `p` is prime.

  *Proof:* By contradiction. If every prime factor of `Φ_{2e+1}(p)` divides
  `2e+1`, then each appears with multiplicity 1 (by the valuation-1 lemma),
  so `Φ_{2e+1}(p) ∣ (2e+1)`. But `Φ_{2e+1}(p) > 2e+1`, a contradiction.
-/
lemma zsigmondy_not_exceptional (p e : ℕ) (hp : p.Prime) (hp_ge_3 : 3 ≤ p) (he : 3 ≤ 2 * e + 1) :
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
  -- Step 3: Each such prime has multiplicity exactly 1 in Φ (valuation-1 lemma)
  have h_sq : ∀ q : ℕ, q.Prime → q ∣ Φ → ¬(q ^ 2 ∣ Φ) := by
    intro q hq_prime hq_dvd
    have hq_dvd_n := h_every_prime_dvd_n q hq_prime hq_dvd
    exact cyclotomic_eval_val_of_dvd_index p n q hp he hq_prime hq_dvd hq_dvd_n
  -- Step 4: Φ divides n (squarefree divisibility lemma)
  have hΦ_pos : 0 < Φ := by omega
  have hΦ_dvd_n : Φ ∣ n :=
    squarefree_dvd_of_prime_factors_dvd Φ n hΦ_pos h_every_prime_dvd_n h_sq
  -- Step 5: But Φ > n (cyclotomic exceeds index), contradicting Φ ∣ n
  have hn_odd : Odd n := ⟨e, by omega⟩
  have hΦ_gt_n : n < Φ := cyclotomic_eval_gt_index p n hp hp_ge_3 hn_odd he
  have hΦ_le_n : Φ ≤ n := Nat.le_of_dvd (by omega) hΦ_dvd_n
  omega



/--
  Zsigmondy's theorem: existence of primitive prime divisors.

  For `2e+1 ≥ 3`, there exists a prime `q` dividing `p^{2e+1} - 1`
  that does not divide `p^k - 1` for any strictly positive `k < 2e+1`.

  *Proof assembly:*
  1. By `zsigmondy_not_exceptional`, there exists a prime `q` dividing
     `Φ_{2e+1}(p)` with `q ∤ (2e+1)`.
  2. By `prime_dvd_cyclotomic_is_primitive`, this `q` is a primitive
     prime divisor: `q | p^{2e+1} - 1` and `q ∤ p^k - 1` for `0 < k < 2e+1`.
-/
lemma zsigmondy_exists_primitive_prime (p e : ℕ) (hp : p.Prime) (hp_ge_3 : 3 ≤ p) (he : 3 ≤ 2 * e + 1) :
    ∃ q : ℕ, q.Prime ∧
      q ∣ p ^ (2 * e + 1) - 1 ∧
      ∀ k, 0 < k → k < 2 * e + 1 → ¬(q ∣ p ^ k - 1) := by
  -- Step 1: Obtain a prime q dividing Φ_{2e+1}(p) that does not divide (2e+1)
  obtain ⟨q, hq_prime, hq_dvd_phi, hq_ndvd_n⟩ :=
    zsigmondy_not_exceptional p e hp hp_ge_3 he
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
  Bridge lemma: connects `sigma_prime_pow` back to the project's `sigma` definition.
  σ(p^{2e}) = sigma_prime_pow p e when p is prime.
-/
lemma sigma_eq_sigma_prime_pow (p e : ℕ) (hp : p.Prime) :
    sigma (p ^ (2 * e)) = sigma_prime_pow p e := by
  unfold sigma sigma_prime_pow
  exact sum_divisors_prime_pow hp

/--
  Full Zsigmondy theorem in the original signature.
  Derived from the formalized components above.
-/
lemma zsigmondy_axiom (p e : ℕ) (hp : p.Prime) (hp_ge_3 : 3 ≤ p) (he : 2 * e + 1 ≥ 3) :
    ∃ q : ℕ, q.Prime ∧ q ∣ sigma (p ^ (2 * e)) ∧ ¬(q ∣ p - 1) ∧ q % (2 * e + 1) = 1 := by
  obtain ⟨q, hq_prime, hq_div, hq_prim⟩ := zsigmondy_exists_primitive_prime p e hp hp_ge_3 he
  have ⟨hq_mod, hq_div_spow⟩ := zsigmondy_primitive_prime_properties hp he hq_prime hq_div hq_prim
  have hq_div_sigma : q ∣ sigma (p ^ (2 * e)) := by
    rw [sigma_eq_sigma_prime_pow p e hp]
    exact hq_div_spow
  have hq_ndiv : ¬(q ∣ p - 1) := by
    have h_k1 : 1 < 2 * e + 1 := by omega
    have h1 := hq_prim 1 zero_lt_one h_k1
    rwa [pow_one] at h1
  exact ⟨q, hq_prime, hq_div_sigma, hq_ndiv, hq_mod⟩


end UALBF.Pure.Zsigmondy
