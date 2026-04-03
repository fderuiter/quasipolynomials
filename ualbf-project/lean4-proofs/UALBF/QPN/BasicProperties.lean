import UALBF.Basic
import UALBF.Pure.Arithmetic

/-!
# QPN Basic Properties

Core theorems about Quasiperfect Numbers (QPNs):
- σ(N) is odd
- QPNs cannot be double squares
- QPNs are odd perfect squares

Every theorem here has `h : IsQuasiperfect N` in its hypothesis.
-/

namespace UALBF.QPN.BasicProperties

open Finset Nat
open UALBF
open UALBF.Pure.Arithmetic

/--
  Parity of σ(N).
  Because 2n + 1 is inherently odd, σ(N) must be odd.
-/
lemma qpn_sigma_odd {n : ℕ} (h : IsQuasiperfect n) : Odd (sigma n) := by
  exact ⟨n, h.2⟩

lemma square_qpn_parity_obstruction {m : ℕ} (h_qpn : IsQuasiperfect (m^2)) (heven : Even m) : False := by
  have hm_pos : m > 0 := by
    have h_sq_pos : m ^ 2 > 0 := h_qpn.1
    have hm_zero : m ≠ 0 := by
      intro h
      rw [h] at h_sq_pos
      revert h_sq_pos
      decide
    omega
  rcases extract_odd_factor m hm_pos with ⟨e, u, hm_eq, hu_odd⟩
  have he_ge_1 : e ≥ 1 := by
    rcases even_iff_two_dvd.mp heven with ⟨k, hk⟩
    by_contra h_contra
    have h_e_zero : e = 0 := by omega
    have h_u_eq : u = 2 * k := by
      calc u = 1 * u := by ring
           _ = 2 ^ e * u := by rw [h_e_zero, pow_zero]
           _ = m := hm_eq.symm
           _ = 2 * k := hk
    have hdvd_u : 2 ∣ u := ⟨k, h_u_eq⟩
    exact hu_odd hdvd_u

  have hm_sq : m ^ 2 = 2 ^ (2 * e) * u ^ 2 := by
    calc m ^ 2 = (2 ^ e * u) ^ 2 := by rw [hm_eq]
         _ = 2 ^ (2 * e) * u ^ 2 := by ring

  have h_sigma : sigma (2 ^ (2 * e) * u ^ 2) = 2 * (2 ^ (2 * e) * u ^ 2) + 1 := by
    have h1 := h_qpn.2
    rw [←hm_sq]
    exact h1

  have h_dvd : (2 ^ (2 * e + 1) - 1) ∣ (u ^ 2 + 1) := qpn_sq_divisibility e u hu_odd h_sigma

  have h_mod : (2 ^ (2 * e + 1) - 1) % 4 = 3 := by
    have h_pow_ge : 2 * e + 1 ≥ 2 := by omega
    exact two_pow_sub_one_mod_four h_pow_ge

  have h_prime_factor := mod_four_eq_three_has_prime_factor (2 ^ (2 * e + 1) - 1) (by omega) h_mod
  rcases h_prime_factor with ⟨q, hq_prime, hq_dvdM, hq_mod⟩

  have hqu2 : q ∣ (u ^ 2 + 1) := dvd_trans hq_dvdM h_dvd

  have h_sq_mod : ((u ^ 2 + 1 : ℕ) : ZMod q) = 0 := by
    rcases hqu2 with ⟨c, hc⟩
    rw [hc, Nat.cast_mul, CharP.cast_eq_zero (ZMod q) q, zero_mul]

  have h_sq_eq : (u : ZMod q) ^ 2 = -1 := by
    have h_cast : ((u ^ 2 : ℕ) : ZMod q) = (u : ZMod q) ^ 2 := by exact Nat.cast_pow u 2
    have h_cast_add : ((u ^ 2 + 1 : ℕ) : ZMod q) = ((u ^ 2 : ℕ) : ZMod q) + 1 := by
      push_cast
      rfl
    calc (u : ZMod q) ^ 2 = ((u ^ 2 + 1 : ℕ) : ZMod q) - 1 := by rw [h_cast_add, h_cast]; ring
         _ = 0 - 1 := by rw [h_sq_mod]
         _ = -1 := by ring

  have h_is_sq : IsSquare (-1 : ZMod q) := by
    use (u : ZMod q)
    calc -1 = (u : ZMod q) ^ 2 := h_sq_eq.symm
         _ = (u : ZMod q) * (u : ZMod q) := by ring

  haveI : Fact q.Prime := ⟨hq_prime⟩
  have h_not_3 := (ZMod.exists_sq_eq_neg_one_iff (p := q)).mp h_is_sq

  have h_contra : q % 4 ≠ 3 := h_not_3
  exact h_contra hq_mod

/-- An even QPN would require n = 2m^2 (abundancy limit & parity structural necessity). -/
lemma even_qpn_implies_double_square {n : ℕ} (h : IsQuasiperfect n) (heven : Even n) :
  ∃ m : ℕ, n = 2 * m ^ 2 := by
  have h_odd_sigma : Odd (sigma n) := qpn_sigma_odd h
  have h_or : (∃ m : ℕ, n = m ^ 2) ∨ (∃ m : ℕ, n = 2 * m ^ 2) :=
    (odd_sigma_iff_square_or_double_square n h.1).mp h_odd_sigma
  rcases h_or with ⟨m, rfl⟩ | ⟨m, hm_dbl⟩
  · have hm_even : Even m := by
      cases Nat.even_or_odd m with
      | inl he => exact he
      | inr ho =>
        have ho_sq : Odd (m^2) := Odd.pow ho
        have h_contra : ¬ Even (m^2) := fun h_even => by
          rcases ho_sq with ⟨k, hk⟩
          rcases h_even with ⟨j, hj⟩
          omega
        exact False.elim (h_contra heven)
    have h_false := square_qpn_parity_obstruction h hm_even
    exact False.elim h_false
  · exact ⟨m, hm_dbl⟩

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
  QPNs are Odd Perfect Squares.
  A known number-theoretic fact states that if σ(n) is odd, n is either a
  perfect square or twice a perfect square. Because an even QPN would require
  n = 2m^2 (leading to a contradiction in abundancy limits and parity), n must
  be an odd perfect square.
-/
theorem qpn_is_odd_square {n : ℕ} (h : IsQuasiperfect n) :
  Odd n ∧ ∃ m : ℕ, n = m ^ 2 := by
  have h_odd_sigma : Odd (sigma n) := qpn_sigma_odd h
  have h_sq_or_dbl : (∃ m : ℕ, n = m ^ 2) ∨ (∃ m : ℕ, n = 2 * m ^ 2) :=
    (odd_sigma_iff_square_or_double_square n h.1).mp h_odd_sigma
  have h_not_dbl : ¬ ∃ m : ℕ, n = 2 * m ^ 2 := qpn_not_double_square h
  have h_is_sq : ∃ m : ℕ, n = m ^ 2 := by
    rcases h_sq_or_dbl with h_sq | h_dbl
    · exact h_sq
    · exact False.elim (h_not_dbl h_dbl)
  have h_odd_n : Odd n := by
    rcases Nat.even_or_odd n with h_even | h_odd
    · have h_dbl := even_qpn_implies_double_square h h_even
      exact False.elim (h_not_dbl h_dbl)
    · exact h_odd
  exact ⟨h_odd_n, h_is_sq⟩

end UALBF.QPN.BasicProperties
