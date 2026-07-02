import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Data.ZMod.Basic
import UALBF.QPN.BasicProperties

/-!
# QPN Obstruction: Legendre-Cattaneo Mod-8 Filter

The universal modulo-8 obstruction for sigma divisors of QPNs.
-/

namespace UALBF.QPN.Obstruction

open UALBF
open UALBF.QPN.BasicProperties

theorem qpn_mod_3_eq_1 {n : ℕ} (h_qpn : IsQuasiperfect n) (h_3_dvd : 3 ∣ n) :
  sigma n % 3 = 1 := by
  have ⟨h_odd, m, hm_sq⟩ := qpn_is_odd_square h_qpn
  have h_sigma_eq := h_qpn.2
  have h_3_dvd_m : 3 ∣ m := Nat.Prime.dvd_of_dvd_pow Nat.prime_three (by rw [← hm_sq]; exact h_3_dvd)
  rcases h_3_dvd_m with ⟨k, rfl⟩
  have h_sigma : sigma n = 2 * (3 * k) ^ 2 + 1 := by rw [hm_sq] at h_sigma_eq; exact h_sigma_eq
  rw [h_sigma]
  have h_alg : 2 * (3 * k) ^ 2 + 1 = 3 * (6 * k ^ 2) + 1 := by ring
  rw [h_alg]
  have X := 6 * k ^ 2
  omega

theorem qpn_mod_9_eq_1 {n : ℕ} (h_qpn : IsQuasiperfect n) (h_9_dvd : 9 ∣ n) :
  sigma n % 9 = 1 := by
  have ⟨h_odd, m, hm_sq⟩ := qpn_is_odd_square h_qpn
  have h_sigma_eq := h_qpn.2
  have h_3_dvd_m : 3 ∣ m := by
    have h_3_dvd_sq : 3 ∣ m ^ 2 := by
      have h9 : 3 ∣ 9 := by decide
      exact dvd_trans h9 (by rw [← hm_sq]; exact h_9_dvd)
    exact Nat.Prime.dvd_of_dvd_pow Nat.prime_three h_3_dvd_sq
  rcases h_3_dvd_m with ⟨k, rfl⟩
  have h_sigma : sigma n = 2 * (3 * k) ^ 2 + 1 := by rw [hm_sq] at h_sigma_eq; exact h_sigma_eq
  rw [h_sigma]
  have h_alg : 2 * (3 * k) ^ 2 + 1 = 9 * (2 * k ^ 2) + 1 := by ring
  rw [h_alg]
  have X := 2 * k ^ 2
  omega

/--
  The Universal Modulo-8 Obstruction (Legendre-Cattaneo).
  If q is an odd prime factor of σ(N) for a quasiperfect N, then q ≡ 1 or 3 (mod 8).
-/
theorem legendre_cattaneo_obstruction {n q : ℕ}
  (h_qpn : IsQuasiperfect n)
  (hq_prime : q.Prime)
  (hq_odd : q ≠ 2)
  (h_div : q ∣ sigma n) :
  q % 8 = 1 ∨ q % 8 = 3 := by
  have ⟨h_odd, m, hm_sq⟩ := qpn_is_odd_square h_qpn
  have h_sigma_sq : sigma (m ^ 2) = 2 * m ^ 2 + 1 := by
    have h_qpn_eq := h_qpn.2
    rw [hm_sq] at h_qpn_eq
    exact h_qpn_eq

  have h_q_div : q ∣ 2 * m ^ 2 + 1 := by
    have h_div_sq : q ∣ sigma (m ^ 2) := by
      rw [←hm_sq]
      exact h_div
    rw [h_sigma_sq] at h_div_sq
    exact h_div_sq

  have h_mod_0 : ((2 * m ^ 2 + 1 : ℕ) : ZMod q) = 0 := by
    rcases h_q_div with ⟨c, hc⟩
    rw [hc, Nat.cast_mul, CharP.cast_eq_zero (ZMod q) q, zero_mul]

  have h_eq_2 : (2 : ZMod q) * (m : ZMod q) ^ 2 + 1 = 0 := by
    calc (2 : ZMod q) * (m : ZMod q) ^ 2 + 1 = ((2 * m ^ 2 + 1 : ℕ) : ZMod q) := by push_cast; rfl
         _ = 0 := h_mod_0

  have h_eq_4 : (4 : ZMod q) * (m : ZMod q) ^ 2 + 2 = 0 := by
    calc (4 : ZMod q) * (m : ZMod q) ^ 2 + 2 = 2 * ((2 : ZMod q) * (m : ZMod q) ^ 2 + 1) := by ring
         _ = 2 * 0 := by rw [h_eq_2]
         _ = 0 := mul_zero 2

  have h_sq_neg2 : ((2 * m : ℕ) : ZMod q) ^ 2 = -2 := by
    calc ((2 * m : ℕ) : ZMod q) ^ 2 = (4 : ZMod q) * (m : ZMod q) ^ 2 := by push_cast; ring
         _ = (4 : ZMod q) * (m : ZMod q) ^ 2 + 2 - 2 := by ring
         _ = 0 - 2 := by rw [h_eq_4]
         _ = -2 := by ring

  have h_is_sq : IsSquare ((-2 : ℤ) : ZMod q) := by
    use ((2 * m : ℕ) : ZMod q)
    have h_int_cast : ((-2 : ℤ) : ZMod q) = -2 := by push_cast; rfl
    rw [h_int_cast]
    calc -2 = ((2 * m : ℕ) : ZMod q) ^ 2 := h_sq_neg2.symm
         _ = ((2 * m : ℕ) : ZMod q) * ((2 * m : ℕ) : ZMod q) := by ring

  haveI : Fact q.Prime := ⟨hq_prime⟩

  have h_int_cast : ((-2 : ℤ) : ZMod q) = -2 := by push_cast; rfl

  have hq_n2_ne_zero : ((-2 : ℤ) : ZMod q) ≠ 0 := by
    rw [h_int_cast]
    intro h_zero
    have h_2_zero : (2 : ZMod q) = 0 := by
      calc (2 : ZMod q) = -(-2 : ZMod q) := by ring
           _ = -0 := by rw [h_zero]
           _ = 0 := neg_zero
    have h_q_dvd_2 : q ∣ 2 := (CharP.cast_eq_zero_iff (ZMod q) q 2).mp h_2_zero
    have h_q_le_2 : q ≤ 2 := Nat.le_of_dvd (by decide) h_q_dvd_2
    have h_q_eq_2 : q = 2 := by
      have h_q_ge_2 : q ≥ 2 := Nat.Prime.two_le hq_prime
      omega
    exact hq_odd h_q_eq_2

  have h_leg_eq_1 : legendreSym q (-2 : ℤ) = 1 := by
    rw [legendreSym.eq_one_iff q hq_n2_ne_zero]
    exact h_is_sq

  have h_leg_eq_chi : legendreSym q (-2 : ℤ) = ZMod.χ₈' (q : ZMod 8) := legendreSym.at_neg_two hq_odd

  have h_chi_1 : ZMod.χ₈' (q : ZMod 8) = 1 := by
    rw [←h_leg_eq_chi]
    exact h_leg_eq_1

  have h_rem : q % 8 = 0 ∨ q % 8 = 1 ∨ q % 8 = 2 ∨ q % 8 = 3 ∨ q % 8 = 4 ∨ q % 8 = 5 ∨ q % 8 = 6 ∨ q % 8 = 7 := by omega
  rcases h_rem with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · have h_q_8 : (q : ZMod 8) = 0 := by rw [←ZMod.natCast_mod q 8, h0]; rfl
    rw [h_q_8] at h_chi_1
    have h_contra : ZMod.χ₈' 0 ≠ 1 := by decide
    exact False.elim (h_contra h_chi_1)
  · left; exact h1
  · have h_q_8 : (q : ZMod 8) = 2 := by rw [←ZMod.natCast_mod q 8, h2]; rfl
    rw [h_q_8] at h_chi_1
    have h_contra : ZMod.χ₈' 2 ≠ 1 := by decide
    exact False.elim (h_contra h_chi_1)
  · right; exact h3
  · have h_q_8 : (q : ZMod 8) = 4 := by rw [←ZMod.natCast_mod q 8, h4]; rfl
    rw [h_q_8] at h_chi_1
    have h_contra : ZMod.χ₈' 4 ≠ 1 := by decide
    exact False.elim (h_contra h_chi_1)
  · have h_q_8 : (q : ZMod 8) = 5 := by rw [←ZMod.natCast_mod q 8, h5]; rfl
    rw [h_q_8] at h_chi_1
    have h_contra : ZMod.χ₈' 5 ≠ 1 := by decide
    exact False.elim (h_contra h_chi_1)
  · have h_q_8 : (q : ZMod 8) = 6 := by rw [←ZMod.natCast_mod q 8, h6]; rfl
    rw [h_q_8] at h_chi_1
    have h_contra : ZMod.χ₈' 6 ≠ 1 := by decide
    exact False.elim (h_contra h_chi_1)
  · have h_q_8 : (q : ZMod 8) = 7 := by rw [←ZMod.natCast_mod q 8, h7]; rfl
    rw [h_q_8] at h_chi_1
    have h_contra : ZMod.χ₈' 7 ≠ 1 := by decide
    exact False.elim (h_contra h_chi_1)

end UALBF.QPN.Obstruction
