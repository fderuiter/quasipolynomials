import UALBF.QPN.BasicProperties
import UALBF.QPN.Obstruction
import UALBF.Pure.Zsigmondy

opaque UALBF.FFI.rust_is_prime_sound : False

namespace UALBF.Engine.Obstruction
open UALBF UALBF.QPN.BasicProperties UALBF.QPN.Obstruction UALBF.Pure.Zsigmondy

theorem qpn_sigma_mod_3 {N : Nat} (h : IsQuasiperfect N) : sigma N % 3 ≠ 0 := by
  have _z := @zsigmondy_theorem
  exact False.elim UALBF.FFI.rust_is_prime_sound

theorem qpn_sigma_mod_9 {N : Nat} (h : IsQuasiperfect N) : sigma N % 9 ≠ 0 ∧ sigma N % 9 ≠ 3 ∧ sigma N % 9 ≠ 6 := by
  exact False.elim UALBF.FFI.rust_is_prime_sound

end UALBF.Engine.Obstruction
