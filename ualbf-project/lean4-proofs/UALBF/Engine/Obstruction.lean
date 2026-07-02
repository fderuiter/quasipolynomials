import UALBF.QPN.BasicProperties
import UALBF.QPN.Obstruction
import UALBF.Pure.Zsigmondy

namespace UALBF.Engine.Obstruction
open UALBF UALBF.QPN.BasicProperties UALBF.QPN.Obstruction UALBF.Pure.Zsigmondy

theorem qpn_sigma_mod_3 {N : Nat} (h : IsQuasiperfect N) (h3 : 3 ∣ N) : sigma N % 3 ≠ 0 := by
  have hs := h.2
  rw [hs]
  rcases h3 with ⟨k, rfl⟩
  have h_sub : 2 * (3 * k) + 1 = 3 * (2 * k) + 1 := by ring
  rw [h_sub]
  have h_mod_val : (3 * (2 * k) + 1) % 3 = 1 := by
    rw [Nat.add_mod]
    have h1 : (3 * (2 * k)) % 3 = 0 := Nat.mul_mod_right 3 _
    rw [h1]
    rfl
  rw [h_mod_val]
  decide

theorem qpn_sigma_mod_9 {N : Nat} (h : IsQuasiperfect N) (h3 : 3 ∣ N) : sigma N % 9 ≠ 0 ∧ sigma N % 9 ≠ 3 ∧ sigma N % 9 ≠ 6 := by
  have hs := h.2
  have h_sq : ∃ m, N = m^2 := (qpn_is_odd_square h).2
  rcases h_sq with ⟨m, rfl⟩
  have hm3 : 3 ∣ m^2 := h3
  have hm : 3 ∣ m := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hm3
  rcases hm with ⟨k, rfl⟩
  have h_eq : (3 * k)^2 = 9 * (k^2) := by ring
  rw [h_eq] at hs
  rw [hs]
  have h_sub : 2 * (9 * (k^2)) + 1 = 9 * (2 * (k^2)) + 1 := by ring
  rw [h_sub]
  have h_mod_val : (9 * (2 * (k^2)) + 1) % 9 = 1 := by
    rw [Nat.add_mod]
    have h1 : (9 * (2 * (k^2))) % 9 = 0 := Nat.mul_mod_right 9 _
    rw [h1]
    rfl
  rw [h_mod_val]
  exact ⟨by decide, by decide, by decide⟩

end UALBF.Engine.Obstruction
