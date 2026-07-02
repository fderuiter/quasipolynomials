import UALBF.QPN.BasicProperties
import UALBF.QPN.Obstruction
import UALBF.Pure.Zsigmondy

namespace UALBF.Engine.Obstruction
open UALBF UALBF.QPN.BasicProperties UALBF.QPN.Obstruction UALBF.Pure.Zsigmondy

theorem qpn_sigma_mod_3 {N : Nat} (h : IsQuasiperfect N) (h3 : 3 ∣ N) : sigma N % 3 ≠ 0 := by
  have h_eq := qpn_mod_3_eq_1 h h3
  omega

theorem qpn_sigma_mod_9 {N : Nat} (h : IsQuasiperfect N) (h9 : 9 ∣ N) : sigma N % 9 ≠ 0 ∧ sigma N % 9 ≠ 3 ∧ sigma N % 9 ≠ 6 := by
  have h_eq := qpn_mod_9_eq_1 h h9
  omega

end UALBF.Engine.Obstruction
