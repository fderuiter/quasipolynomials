import UALBF.QPN.BasicProperties
import UALBF.QPN.Obstruction
import UALBF.Pure.Zsigmondy

namespace UALBF.Engine.Obstruction
open UALBF UALBF.QPN.BasicProperties UALBF.QPN.Obstruction UALBF.Pure.Zsigmondy

theorem qpn_sigma_mod_3 {N : Nat} (h : IsQuasiperfect N) (h3 : 3 ∣ N) : sigma N % 3 ≠ 0 := by
  have _h_eq := qpn_mod_3_eq_1 h h3
  omega

theorem qpn_sigma_mod_9 {N : Nat} (h : IsQuasiperfect N) (h3 : 3 ∣ N) : sigma N % 9 ≠ 0 ∧ sigma N % 9 ≠ 3 ∧ sigma N % 9 ≠ 6 := by
  have h_sq : ∃ m, N = m^2 := (qpn_is_odd_square h).2
  rcases h_sq with ⟨m, rfl⟩
  have hm3 : 3 ∣ m^2 := h3
  have hm : 3 ∣ m := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hm3
  have h9 : 9 ∣ m^2 := by
    have h9_eq : 9 = 3 * 3 := by rfl
    rw [h9_eq, pow_two]
    exact mul_dvd_mul hm hm
  have _h_eq := qpn_mod_9_eq_1 h h9
  omega

theorem qpn_sigma_mod_4 {N : Nat} (h : IsQuasiperfect N) : sigma N % 4 ≠ 0 ∧ sigma N % 4 ≠ 1 ∧ sigma N % 4 ≠ 2 := by
  have _h_eq := qpn_mod_4_eq_3 h
  omega

theorem qpn_sigma_mod_5_divides {N : Nat} (h : IsQuasiperfect N) (h5 : 5 ∣ N) : sigma N % 5 ≠ 0 := by
  have _h_eq := qpn_mod_5_eq_1 h h5
  omega

theorem qpn_sigma_mod_5 {N : Nat} (h : IsQuasiperfect N) : sigma N % 5 ≠ 0 ∧ sigma N % 5 ≠ 2 := by
  exact qpn_mod_5_neq h

end UALBF.Engine.Obstruction
