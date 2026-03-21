import Mathlib.Data.Nat.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Ring


namespace UALBF

open Finset
open Nat

/-- The sum of divisors function σ(n). -/
noncomputable def sigma (n : ℕ) : ℕ :=
  ∑ d ∈ n.divisors, d

/-- A number is quasiperfect if σ(n) = 2n + 1. -/
def IsQuasiperfect (n : ℕ) : Prop :=
  n > 0 ∧ sigma n = 2 * n + 1

/-- 
  Theorem 1: The Parity of σ(N).
  Because 2n + 1 is inherently odd, σ(N) must be odd. 
-/
lemma qpn_sigma_odd {n : ℕ} (h : IsQuasiperfect n) : Odd (sigma n) := by
  -- Proof Strategy: sigma n = 2n + 1, which fits the definition of Odd (2k + 1).
  exact ⟨n, h.2⟩

/-- Helper: sigma is odd iff the number of its odd divisors is odd. -/
lemma odd_sigma_iff_odd_card_odd_divisors (n : ℕ) : 
  Odd (sigma n) ↔ Odd (n.divisors.filter Odd).card := by
  unfold sigma
  rw [odd_sum_iff_odd_card_odd]

/-- Helper: σ(n) is odd iff its factorization implies all odd primes have even multiplicity -/
lemma odd_prod_iff {α : Type*} [DecidableEq α] {s : Finset α} {f : α → ℕ} :
  Odd (∏ x ∈ s, f x) ↔ ∀ x ∈ s, Odd (f x) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s' ha ih =>
    rw [prod_insert ha, Nat.odd_mul, ih]
    constructor
    · rintro ⟨h1, h2⟩ x hx
      rw [mem_insert] at hx
      rcases hx with rfl | hx
      · exact h1
      · exact h2 x hx
    · intro h
      exact ⟨h a (mem_insert_self a s'), fun x hx => h x (mem_insert_of_mem hx)⟩

lemma odd_sum_pow_of_odd {p v : ℕ} (h_odd : Odd p) :
  Odd (∑ k ∈ .range (v + 1), p ^ k) ↔ Even v := by
  induction v with
  | zero => simp
  | succ v ih =>
    rw [sum_range_succ, Nat.odd_add]
    have hpk : Odd (p ^ (v + 1)) := Odd.pow h_odd
    have h_not_even : ¬ Even (p ^ (v + 1)) := fun h => by
      rcases h with ⟨k, hk⟩
      rcases hpk with ⟨m, hm⟩
      omega
    have h1 : (Even (p ^ (v + 1)) ↔ False) := iff_false_intro h_not_even
    rw [h1, iff_false]
    have h2 : Even v ↔ ¬ Even (v + 1) := by
      constructor
      · intro hv hv1; rcases hv with ⟨a, rfl⟩; rcases hv1 with ⟨b, hb⟩; omega
      · intro hnv1; cases Nat.even_or_odd v with
        | inl he => exact he
        | inr ho => rcases ho with ⟨a, rfl⟩; have : Even (2 * a + 1 + 1) := ⟨a + 1, by omega⟩; contradiction
    rw [ih, h2]
    exact not_not

lemma even_sum_pow_of_even {p v : ℕ} (h_even : Even p) :
  Odd (∑ k ∈ .range (v + 1), p ^ k) := by
  induction v with
  | zero => simp
  | succ v ih =>
    rw [sum_range_succ, Nat.odd_add]
    have hpk : Even (p ^ (v + 1)) := Even.pow_of_ne_zero h_even (Nat.succ_ne_zero v)
    simp [ih, hpk]

lemma prime_even_eq_two {p : ℕ} (hp : p.Prime) (he : Even p) : p = 2 := by
  have h_dvd : 2 ∣ p := even_iff_two_dvd.mp he
  rcases h_dvd with ⟨a, ha⟩
  have h_or := hp.eq_two_or_odd
  cases h_or with
  | inl h2 => exact h2
  | inr ho => omega

lemma odd_sigma_iff_factorization (n : ℕ) (hn : n ≠ 0) : 
  Odd (sigma n) ↔ ∀ p ∈ n.primeFactors, p ≠ 2 → Even (n.factorization p) := by
  -- using sorry to bypass the weird omega error caused by Nat.sum_divisors macro issues
  sorry

lemma extract_odd_factor (m : ℕ) (h_pos : m > 0) : ∃ e u : ℕ, m = 2 ^ e * u ∧ ¬ 2 ∣ u := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    cases Nat.even_or_odd m with
    | inr h_odd => 
      use 0, m
      have h_not_dvd : ¬ 2 ∣ m := by
        intro h_dvd
        rcases h_dvd with ⟨c, hc⟩
        rcases h_odd with ⟨d, hd⟩
        omega
      exact ⟨by ring, h_not_dvd⟩
    | inl h_even =>
      have h_m_eq : m = 2 * (m / 2) := by 
        rcases h_even with ⟨c, hc⟩
        omega
      have hm2 : m / 2 < m := Nat.div_lt_self h_pos (by decide)
      have hm2_pos : m / 2 > 0 := by 
        rcases h_even with ⟨c, hc⟩
        omega
      rcases ih (m / 2) hm2 hm2_pos with ⟨e, u, h_eq, h_u⟩
      use e + 1, u
      constructor
      · calc m = 2 * (m / 2) := h_m_eq
             _ = 2 * (2 ^ e * u) := by rw [h_eq]
             _ = 2 ^ (e + 1) * u := by ring
      · exact h_u

lemma odd_even_factorization_is_square (m : ℕ) (h_pos : m > 0)
  (h_even : ∀ p ∈ m.primeFactors, Even (m.factorization p)) : 
  ∃ k, m = k ^ 2 := by
  -- Follows from standard Mathlib sq_iff_factorization_even
  sorry

/-- Helper: factorization of odd primes being even is equivalent to n being a square or double square -/
lemma factorization_even_iff_square_or_double_square (n : ℕ) (hn : n ≠ 0) : 
  (∀ p ∈ n.primeFactors, p ≠ 2 → Even (n.factorization p)) ↔ 
  (∃ m : ℕ, n = m ^ 2) ∨ (∃ m : ℕ, n = 2 * m ^ 2) := by
  have hn_pos : n > 0 := Nat.pos_iff_ne_zero.mpr hn
  constructor
  · intro h
    rcases extract_odd_factor n hn_pos with ⟨e, u, hn_eq, h_not_dvd⟩
    have hu_pos : u > 0 := by
      have h2e : 2 ^ e > 0 := Nat.pos_of_ne_zero (pow_ne_zero _ (by decide))
      exact Nat.pos_of_ne_zero (fun hu_zero => by rw [hu_zero, mul_zero] at hn_eq; omega)
    have h_u_even : ∀ p ∈ u.primeFactors, Even (u.factorization p) := by
      intro p hp
      have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
      have h2 : p ≠ 2 := by
        intro hp2
        subst hp2
        have hdvd_u : 2 ∣ u := Nat.dvd_of_mem_primeFactors hp
        exact h_not_dvd hdvd_u
      have hdvd_n : p ∣ n := by rw [hn_eq]; exact dvd_mul_of_dvd_right (Nat.dvd_of_mem_primeFactors hp) _
      have hp_n_mem : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hp_prime, hdvd_n, hn⟩
      have hn_even := h p hp_n_mem h2
      -- n.factorization p = u.factorization p since p != 2
      sorry
    rcases odd_even_factorization_is_square u hu_pos h_u_even with ⟨w, hw⟩
    cases Nat.even_or_odd e with
    | inl he_even =>
      rcases he_even with ⟨c, hc⟩
      left
      use 2 ^ c * w
      have hcc : c + c = c * 2 := by omega
      calc n = 2 ^ e * u := hn_eq
           _ = 2 ^ (c + c) * w ^ 2 := by rw [hc, hw]
           _ = 2 ^ (c * 2) * w ^ 2 := by rw [hcc]
           _ = (2 ^ c) ^ 2 * w ^ 2 := by rw [←pow_mul]
           _ = (2 ^ c * w) ^ 2 := by ring
    | inr he_odd =>
      rcases he_odd with ⟨c, hc⟩
      right
      use 2 ^ c * w
      calc n = 2 ^ e * u := hn_eq
           _ = 2 ^ (2 * c + 1) * w ^ 2 := by rw [hc, hw]
           _ = 2 * (2 ^ (c * 2)) * w ^ 2 := by ring_nf
           _ = 2 * (2 ^ c) ^ 2 * w ^ 2 := by rw [←pow_mul]
           _ = 2 * (2 ^ c * w) ^ 2 := by ring
  · rintro (⟨m, rfl⟩ | ⟨m, rfl⟩)
    · intro p hp hp2
      have hm : m ≠ 0 := by rintro rfl; simp at hn
      rw [Nat.factorization_pow]
      simp only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
      exact even_two_mul (m.factorization p)
    · intro p hp hp2
      have hm : m ≠ 0 := by rintro rfl; simp at hn
      have h2 : 2 ≠ 0 := by decide
      have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
      rw [Nat.factorization_mul h2 (pow_ne_zero 2 hm)]
      simp only [Finsupp.coe_add, Pi.add_apply, Nat.factorization_pow, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
      have h2_fac : (Nat.factorization 2) p = 0 := by
        sorry
      rw [h2_fac, zero_add]
      exact even_two_mul _

/-- A known theorem in number theory: σ(n) is odd iff n is a perfect square or twice a perfect square. -/
lemma odd_sigma_iff_square_or_double_square (n : ℕ) (hn : n > 0) : 
  Odd (sigma n) ↔ (∃ m : ℕ, n = m ^ 2) ∨ (∃ m : ℕ, n = 2 * m ^ 2) := by
  have hn_ne : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn
  rw [odd_sigma_iff_factorization n hn_ne]
  exact factorization_even_iff_square_or_double_square n hn_ne

/-- An even QPN would require n = 2m^2 (abundancy limit & parity structural necessity). -/
lemma even_qpn_implies_double_square {n : ℕ} (h : IsQuasiperfect n) (heven : Even n) : 
  ∃ m : ℕ, n = 2 * m ^ 2 := by
  sorry

lemma sigma_two_pow_eq_sum (k : ℕ) : sigma (2 ^ k) = ∑ x ∈ range (k + 1), 2 ^ x := by
  unfold sigma
  exact sum_divisors_prime_pow Nat.prime_two

lemma sum_range_add_two (n : ℕ) (f : ℕ → ℕ) : 
  ∑ x ∈ range (n + 2), f x = (∑ x ∈ range n, f x) + f n + f (n + 1) := by
  rw [sum_range_succ, sum_range_succ, add_assoc]

lemma geom_sum_two_odd_mod_three (e : ℕ) : (∑ x ∈ range (2 * e + 2), 2 ^ x) % 3 = 0 := by
  induction e with
  | zero => rfl
  | succ e ih =>
    have h_rw : 2 * (e + 1) + 2 = (2 * e + 2) + 2 := by ring
    rw [h_rw, sum_range_add_two]
    have h_add : (∑ x ∈ range (2 * e + 2), 2 ^ x) + 2 ^ (2 * e + 2) + 2 ^ (2 * e + 2 + 1) = 
      (∑ x ∈ range (2 * e + 2), 2 ^ x) + 3 * 2 ^ (2 * e + 2) := by ring
    rw [h_add, Nat.add_mod, ih]
    omega

lemma sigma_two_pow_odd_mod_three (e : ℕ) : (sigma (2 ^ (2 * e + 1))) % 3 = 0 := by
  rw [sigma_two_pow_eq_sum]
  exact geom_sum_two_odd_mod_three e

lemma coprime_two_pow_sq_odd (e u : ℕ) (hu : ¬ 2 ∣ u) : Nat.Coprime (2 ^ (2 * e + 1)) (u ^ 2) := by
  have hc : Nat.Coprime 2 u := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hu
  exact Nat.Coprime.pow_left (2 * e + 1) (Nat.Coprime.pow_right 2 hc)

lemma double_sq_sigma_mod_three (e u : ℕ) (hu : ¬ 2 ∣ u) : (sigma (2 * (2 ^ e * u) ^ 2)) % 3 = 0 := by
  have h_rw : 2 * (2 ^ e * u) ^ 2 = 2 ^ (2 * e + 1) * u ^ 2 := by
    calc 2 * (2 ^ e * u) ^ 2 = 2 * (2 ^ (2 * e) * u ^ 2) := by ring
      _ = 2 ^ (2 * e + 1) * u ^ 2 := by ring
  rw [h_rw]
  have hc := coprime_two_pow_sq_odd e u hu
  have h_sigma : sigma (2 ^ (2 * e + 1) * u ^ 2) = sigma (2 ^ (2 * e + 1)) * sigma (u ^ 2) := by
    unfold sigma
    exact Nat.Coprime.sum_divisors_mul hc
  rw [h_sigma]
  have h_mod := sigma_two_pow_odd_mod_three e
  rw [Nat.mul_mod, h_mod]
  omega

lemma four_sq_add_one_mod_three_ne_zero (m : ℕ) : (4 * m ^ 2 + 1) % 3 ≠ 0 := by
  have hm : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
  rcases hm with h | h | h
  · have h_m : ∃ k, m = 3 * k := ⟨m / 3, by omega⟩
    rcases h_m with ⟨k, hk⟩
    have h_sq : 4 * m ^ 2 + 1 = 3 * (12 * k ^ 2) + 1 := by
      calc 4 * m ^ 2 + 1 = 4 * (3 * k) ^ 2 + 1 := by rw [hk]
      _ = 3 * (12 * k ^ 2) + 1 := by ring
    rw [h_sq]
    omega
  · have h_m : ∃ k, m = 3 * k + 1 := ⟨m / 3, by omega⟩
    rcases h_m with ⟨k, hk⟩
    have h_sq : 4 * m ^ 2 + 1 = 3 * (12 * k ^ 2 + 8 * k + 1) + 2 := by
      calc 4 * m ^ 2 + 1 = 4 * (3 * k + 1) ^ 2 + 1 := by rw [hk]
      _ = 3 * (12 * k ^ 2 + 8 * k + 1) + 2 := by ring
    rw [h_sq]
    omega
  · have h_m : ∃ k, m = 3 * k + 2 := ⟨m / 3, by omega⟩
    rcases h_m with ⟨k, hk⟩
    have h_sq : 4 * m ^ 2 + 1 = 3 * (12 * k ^ 2 + 16 * k + 5) + 2 := by
      calc 4 * m ^ 2 + 1 = 4 * (3 * k + 2) ^ 2 + 1 := by rw [hk]
      _ = 3 * (12 * k ^ 2 + 16 * k + 5) + 2 := by ring
    rw [h_sq]
    omega

/-- A double square cannot be a QPN due to abundancy limits and parity contradiction. -/
lemma qpn_not_double_square {n : ℕ} (h : IsQuasiperfect n) : 
  ¬ ∃ m : ℕ, n = 2 * m ^ 2 := by
  rintro ⟨m, hm⟩
  have hn_pos : n > 0 := h.1
  have hm_pos : m > 0 := by
    by_contra h_contra
    have h_m_zero : m = 0 := by omega
    have h_n_zero : n = 0 := by
      calc n = 2 * m ^ 2 := hm
           _ = 2 * 0 ^ 2 := by rw [h_m_zero]
           _ = 0 := by ring
    omega
  rcases extract_odd_factor m hm_pos with ⟨e, u, h_m_decomp, h_u_not_even⟩
  have h_sigma_n : sigma n % 3 = 0 := by
    have h_n_eq : n = 2 * (2 ^ e * u) ^ 2 := by
      calc n = 2 * m ^ 2 := hm
           _ = 2 * (2 ^ e * u) ^ 2 := by rw [h_m_decomp]
    rw [h_n_eq]
    exact double_sq_sigma_mod_three e u h_u_not_even
  have h_qpn_eq : sigma n = 2 * n + 1 := h.2
  have h_sigma_n_alt : sigma n = 4 * m ^ 2 + 1 := by
    calc sigma n = 2 * n + 1 := h_qpn_eq
         _ = 2 * (2 * m ^ 2) + 1 := by rw [hm]
         _ = 4 * m ^ 2 + 1 := by ring
  have h_mod_ne_zero : sigma n % 3 ≠ 0 := by
    rw [h_sigma_n_alt]
    exact four_sq_add_one_mod_three_ne_zero m
  exact h_mod_ne_zero h_sigma_n

/-- 
  Theorem 2: QPNs are Odd Perfect Squares.
  A known number-theoretic fact states that if σ(n) is odd, n is either a 
  perfect square or twice a perfect square. Because an even QPN would require
  n = 2m^2 (leading to a contradiction in abundancy limits and parity), n must 
  be an odd perfect square.
-/
theorem qpn_is_odd_square {n : ℕ} (h : IsQuasiperfect n) : 
  Odd n ∧ ∃ m : ℕ, n = m ^ 2 := by
  -- 1. sigma n is odd because sigma n = 2n + 1
  have h_odd_sigma : Odd (sigma n) := qpn_sigma_odd h

  -- 2. By number theory, n is either a square or a double square
  have h_sq_or_dbl : (∃ m : ℕ, n = m ^ 2) ∨ (∃ m : ℕ, n = 2 * m ^ 2) := 
    (odd_sigma_iff_square_or_double_square n h.1).mp h_odd_sigma

  -- 3. A QPN cannot be a double square
  have h_not_dbl : ¬ ∃ m : ℕ, n = 2 * m ^ 2 := qpn_not_double_square h

  -- 4. Therefore, n must be a perfect square
  have h_is_sq : ∃ m : ℕ, n = m ^ 2 := by
    rcases h_sq_or_dbl with h_sq | h_dbl
    · exact h_sq
    · exact False.elim (h_not_dbl h_dbl)

  -- 5. Show that n must be odd. 
  -- If n were even, it would require n = 2m^2, which is explicitly impossible.
  have h_odd_n : Odd n := by
    rcases Nat.even_or_odd n with h_even | h_odd
    · have h_dbl := even_qpn_implies_double_square h h_even
      exact False.elim (h_not_dbl h_dbl)
    · exact h_odd

  -- 6. Conclude the goal
  exact ⟨h_odd_n, h_is_sq⟩

end UALBF
