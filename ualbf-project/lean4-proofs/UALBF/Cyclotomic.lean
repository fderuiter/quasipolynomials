import UALBF.Obstruction
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.Data.Int.NatAbs

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

/--
  Task 2: Zsigmondy's theorem (existence of primitive prime divisors).
  For $2e+1 \ge 3$, there exists a prime `q` dividing `p^{2e+1}-1`
  that does not divide `p^k - 1` for any strictly positive $k < 2e+1$.
  This is a deep result in analytic number theory; we stub it with `sorry`.
-/
lemma zsigmondy_exists_primitive_prime (p e : ℕ) (hp : p.Prime) (he : 3 ≤ 2 * e + 1) :
    ∃ q : ℕ, q.Prime ∧
      q ∣ p ^ (2 * e + 1) - 1 ∧
      ∀ k, 0 < k → k < 2 * e + 1 → ¬(q ∣ p ^ k - 1) := by
  sorry -- Zsigmondy's theorem requires substantial analytic number theory.

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
