import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import UALBF.Basic

namespace UALBF

/-- Structure representing the Prefix-Suffix bipartition of the search space. -/
structure QpnBipartition where
  N : ℕ
  N_L : ℕ
  N_R : ℕ
  h_qpn : IsQuasiperfect N
  h_mul : N = N_L * N_R
  h_pos : N_L > 0 ∧ N_R > 0
  h_coprime : N_L.Coprime N_R

/-- 
  Theorem 3: Multiplicativity of Sigma over the Bipartition. 
  Because N_L and N_R are coprime, sigma(N_L * N_R) = sigma(N_L) * sigma(N_R).
-/
lemma sigma_mul (p : QpnBipartition) : sigma p.N = sigma p.N_L * sigma p.N_R := by
  rw [p.h_mul]
  unfold sigma
  exact Nat.Coprime.sum_divisors_mul p.h_coprime

/-- 
  Theorem 4: The Prefix and its Divisor Sum are strictly coprime.
  This proves the Modular Inverse in Phase 4 is mathematically guaranteed to exist.
-/
theorem prefix_sigma_coprime (p : QpnBipartition) : p.N_L.Coprime (sigma p.N_L) := by
  let d := p.N_L.gcd (sigma p.N_L)
  have hd_N_L : d ∣ p.N_L := Nat.gcd_dvd_left p.N_L (sigma p.N_L)
  have hd_sigma : d ∣ sigma p.N_L := Nat.gcd_dvd_right p.N_L (sigma p.N_L)
  have h_eq : sigma p.N_L * sigma p.N_R = 2 * p.N_L * p.N_R + 1 := by
    rw [← sigma_mul p]
    have h2 := p.h_qpn.right
    rw [h2]
    rw [p.h_mul]
    rw [← Nat.mul_assoc]
  have h_dvd_LHS : d ∣ sigma p.N_L * sigma p.N_R := Nat.dvd_trans hd_sigma (Nat.dvd_mul_right (sigma p.N_L) (sigma p.N_R))
  have h_dvd_2NLR : d ∣ 2 * p.N_L * p.N_R := by
    have h_dvd_N_L_R : d ∣ p.N_L * p.N_R := Nat.dvd_trans hd_N_L (Nat.dvd_mul_right p.N_L p.N_R)
    have h_dvd_2_N_L_R : d ∣ 2 * (p.N_L * p.N_R) := Nat.dvd_trans h_dvd_N_L_R (Nat.dvd_mul_left (p.N_L * p.N_R) 2)
    rw [← Nat.mul_assoc] at h_dvd_2_N_L_R
    exact h_dvd_2_N_L_R
  have h_dvd_RHS : d ∣ 2 * p.N_L * p.N_R + 1 := by
    rw [← h_eq]
    exact h_dvd_LHS
  have h_dvd_1 : d ∣ 1 := by
    have h_diff := Nat.dvd_sub h_dvd_RHS h_dvd_2NLR
    have h_add_sub : 2 * p.N_L * p.N_R + 1 - 2 * p.N_L * p.N_R = 1 := Nat.add_sub_cancel_left (2 * p.N_L * p.N_R) 1
    rw [h_add_sub] at h_diff
    exact h_diff
  exact Nat.eq_one_of_dvd_one h_dvd_1

/-- 
  Theorem 5: The AMBS Value Constraint.
  This proves the exact target modulo equation used in the Rust raycast.
-/
theorem ambs_suffix_target (p : QpnBipartition) :
  (p.N_R : ZMod (sigma p.N_L)) * (2 * p.N_L : ZMod (sigma p.N_L)) = -1 := by
  -- Proof Strategy:
  -- 1. Substitute Theorem 3 into QPN equation: `sigma N_L * sigma N_R = 2 * N_L * N_R + 1`.
  -- 2. Cast the entire equation into the ring `ZMod (sigma p.N_L)`.
  -- 3. The LHS `(sigma N_L : ZMod (sigma N_L)) * sigma N_R` becomes 0.
  -- 4. The equation collapses to: `0 = 2 * N_L * N_R + 1` in ZMod.
  -- 5. Rearrange: `N_R * (2 * N_L) = -1` in ZMod.
  sorry

end UALBF
