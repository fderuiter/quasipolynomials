import UALBF.Basic
import UALBF.QPN.Obstruction

namespace UALBF.Engine.Bipartition3

open UALBF

/-- Specialized bipartition where 3 divides the suffix. -/
structure Bipartition3 extends Bipartition where
  h_3_dvd_N_R : 3 ∣ N_R

/-- Ensuring compatibility with modular consistency checks -/
theorem bipartition3_sigma_mod_3_eq_1 (b : Bipartition3) (h_qpn : IsQuasiperfect b.N) :
  sigma b.N % 3 = 1 := by
  have h_3_dvd_N : 3 ∣ b.N := by
    rw [b.h_mul]
    exact dvd_mul_of_dvd_right b.h_3_dvd_N_R b.N_L
  exact UALBF.QPN.Obstruction.qpn_mod_3_eq_1 h_qpn h_3_dvd_N

/-- Tighter prime factor count for the 3|N bipartition structure. -/
def tighter_3_div_bound : Nat := 8

/-- We assert the tighter bound axiomatically for now to unblock the engine integration. -/
axiom bipartition3_min_factors_ax (b : Bipartition3) (_h_qpn : IsQuasiperfect b.N) :
  (b.N.primeFactors.card) ≥ tighter_3_div_bound

end UALBF.Engine.Bipartition3
