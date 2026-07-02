import UALBF.QPN.BasicProperties
import UALBF.QPN.Obstruction
import UALBF.Pure.Zsigmondy

namespace UALBF.Engine.Obstruction
open UALBF UALBF.QPN.BasicProperties UALBF.QPN.Obstruction UALBF.Pure.Zsigmondy

theorem qpn_sigma_mod_3 {N : Nat} (h : IsQuasiperfect N) (h_mod3 : N % 3 = 0) : sigma N % 3 ≠ 0 := by
  have h_sigma : sigma N = 2 * N + 1 := h.2
  have h_N_3 : 3 ∣ N := Nat.dvd_of_mod_eq_zero h_mod3
  rcases h_N_3 with ⟨k, hk⟩
  rw [h_sigma, hk]
  intro h_zero
  have h_3_dvd : 3 ∣ 2 * (3 * k) + 1 := Nat.dvd_of_mod_eq_zero h_zero
  have h_3_dvd_2 : 3 ∣ 2 * (3 * k) := ⟨2 * k, by ring⟩
  have h_1 : 3 ∣ 1 := by
    have h_diff := Nat.dvd_sub h_3_dvd h_3_dvd_2
    have h_eq : 2 * (3 * k) + 1 - 2 * (3 * k) = 1 := Nat.add_sub_cancel_left _ _
    rwa [h_eq] at h_diff
  revert h_1; decide

theorem qpn_sigma_mod_9 {N : Nat} (h : IsQuasiperfect N) (h_mod9 : N % 9 = 0) : sigma N % 9 ≠ 0 ∧ sigma N % 9 ≠ 3 ∧ sigma N % 9 ≠ 6 := by
  have h_sigma : sigma N = 2 * N + 1 := h.2
  have h_N_9 : 9 ∣ N := Nat.dvd_of_mod_eq_zero h_mod9
  rcases h_N_9 with ⟨k, hk⟩
  rw [h_sigma, hk]
  have h_3_dvd_2 : 3 ∣ 2 * (9 * k) := ⟨6 * k, by ring⟩
  constructor
  · intro h_zero
    have h_9_dvd : 9 ∣ 2 * (9 * k) + 1 := Nat.dvd_of_mod_eq_zero h_zero
    have h_3_dvd : 3 ∣ 2 * (9 * k) + 1 := dvd_trans (by decide : 3 ∣ 9) h_9_dvd
    have h_1 : 3 ∣ 1 := by
      have h_diff := Nat.dvd_sub h_3_dvd h_3_dvd_2
      have h_eq : 2 * (9 * k) + 1 - 2 * (9 * k) = 1 := Nat.add_sub_cancel_left _ _
      rwa [h_eq] at h_diff
    revert h_1; decide
  · constructor
    · intro h_three
      have h_3_dvd : 3 ∣ 2 * (9 * k) + 1 := by
        have h_eq : 2 * (9 * k) + 1 = 9 * ((2 * (9 * k) + 1) / 9) + 2 * (9 * k) + 1 % 9 := by omega
        -- actually simpler:
        omega
      have h_1 : 3 ∣ 1 := by
        have h_diff := Nat.dvd_sub h_3_dvd h_3_dvd_2
        have h_eq : 2 * (9 * k) + 1 - 2 * (9 * k) = 1 := Nat.add_sub_cancel_left _ _
        rwa [h_eq] at h_diff
      revert h_1; decide
    · intro h_six
      have h_3_dvd : 3 ∣ 2 * (9 * k) + 1 := by
        omega
      have h_1 : 3 ∣ 1 := by
        have h_diff := Nat.dvd_sub h_3_dvd h_3_dvd_2
        have h_eq : 2 * (9 * k) + 1 - 2 * (9 * k) = 1 := Nat.add_sub_cancel_left _ _
        rwa [h_eq] at h_diff
      revert h_1; decide

end UALBF.Engine.Obstruction
