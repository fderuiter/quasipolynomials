import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import UALBF.Basic

namespace UALBF.Math.Bipartition

open UALBF

set_option linter.dupNamespace false
/-- Structure representing the Prefix-Suffix bipartition of the search space.
    This is purely algebraic: it captures that N factors as N_L * N_R with coprime,
    positive components. No QPN assumption is required — the Rust engine constructs
    these speculatively during DFS before any QPN check occurs. The QPN hypothesis
    is supplied separately to theorems that need it.

    Corresponds to the Rust engine's `Prefix` struct, which carries `n_l`, `s_l`,
    `factors`, and `sigma_factors` without any number-theoretic precondition. -/
structure Bipartition where
  N : ℕ
  N_L : ℕ
  N_R : ℕ
  h_mul : N = N_L * N_R
  h_pos : N_L > 0 ∧ N_R > 0
  h_coprime : N_L.Coprime N_R

/--
  Theorem 3: Multiplicativity of Sigma over the Bipartition.
  Because N_L and N_R are coprime, sigma(N_L * N_R) = sigma(N_L) * sigma(N_R).
  This is a purely algebraic fact — no QPN assumption needed.
-/
lemma sigma_mul (b : Bipartition) : sigma b.N = sigma b.N_L * sigma b.N_R := by
  rw [b.h_mul]
  unfold sigma
  exact Nat.Coprime.sum_divisors_mul b.h_coprime

/--
  Theorem 4: The Prefix and its Divisor Sum are strictly coprime.
  This proves the Modular Inverse in Phase 4 is mathematically guaranteed to exist.
  Note: This requires the QPN hypothesis, supplied separately from the bipartition.
-/
theorem prefix_sigma_coprime (b : Bipartition) (h_qpn : IsQuasiperfect b.N) :
    b.N_L.Coprime (sigma b.N_L) := by
  let d := b.N_L.gcd (sigma b.N_L)
  have hd_N_L : d ∣ b.N_L := Nat.gcd_dvd_left b.N_L (sigma b.N_L)
  have hd_sigma : d ∣ sigma b.N_L := Nat.gcd_dvd_right b.N_L (sigma b.N_L)
  have h_eq : sigma b.N_L * sigma b.N_R = 2 * b.N_L * b.N_R + 1 := by
    rw [← sigma_mul b]
    have h2 := h_qpn.right
    rw [h2]
    rw [b.h_mul]
    rw [← Nat.mul_assoc]
  have h_dvd_LHS : d ∣ sigma b.N_L * sigma b.N_R := Nat.dvd_trans hd_sigma (Nat.dvd_mul_right (sigma b.N_L) (sigma b.N_R))
  have h_dvd_2NLR : d ∣ 2 * b.N_L * b.N_R := by
    have h_dvd_N_L_R : d ∣ b.N_L * b.N_R := Nat.dvd_trans hd_N_L (Nat.dvd_mul_right b.N_L b.N_R)
    have h_dvd_2_N_L_R : d ∣ 2 * (b.N_L * b.N_R) := Nat.dvd_trans h_dvd_N_L_R (Nat.dvd_mul_left (b.N_L * b.N_R) 2)
    rw [← Nat.mul_assoc] at h_dvd_2_N_L_R
    exact h_dvd_2_N_L_R
  have h_dvd_RHS : d ∣ 2 * b.N_L * b.N_R + 1 := by
    rw [← h_eq]
    exact h_dvd_LHS
  have h_dvd_1 : d ∣ 1 := by
    have h_diff := Nat.dvd_sub h_dvd_RHS h_dvd_2NLR
    have h_add_sub : 2 * b.N_L * b.N_R + 1 - 2 * b.N_L * b.N_R = 1 := Nat.add_sub_cancel_left (2 * b.N_L * b.N_R) 1
    rw [h_add_sub] at h_diff
    exact h_diff
  exact Nat.eq_one_of_dvd_one h_dvd_1

/--
  Theorem 5: The AMBS Value Constraint.
  This proves the exact target modulo equation used in the Rust raycast.
  Note: This requires the QPN hypothesis, supplied separately from the bipartition.
-/
theorem ambs_suffix_target (b : Bipartition) (h_qpn : IsQuasiperfect b.N) :
    (b.N_R : ZMod (sigma b.N_L)) * (2 * b.N_L : ZMod (sigma b.N_L)) = -1 := by
  -- Proof Strategy:
  -- 1. Substitute Theorem 3 into QPN equation: `sigma N_L * sigma N_R = 2 * N_L * N_R + 1`.
  have h_eq : sigma b.N_L * sigma b.N_R = 2 * b.N_L * b.N_R + 1 := by
    rw [← sigma_mul b]
    have h2 := h_qpn.right
    rw [h2]
    rw [b.h_mul]
    rw [← Nat.mul_assoc]
  -- 2. Cast the entire equation into the ring `ZMod (sigma b.N_L)`.
  have h_cast : ((2 * b.N_L * b.N_R + 1 : ℕ) : ZMod (sigma b.N_L)) = ((sigma b.N_L * sigma b.N_R : ℕ) : ZMod (sigma b.N_L)) := by
    rw [h_eq]
  -- 3. The LHS `(sigma N_L : ZMod (sigma N_L)) * sigma N_R` becomes 0.
  have h_rhs_zero : ((sigma b.N_L * sigma b.N_R : ℕ) : ZMod (sigma b.N_L)) = 0 := by
    push_cast
    have hc : (sigma b.N_L : ZMod (sigma b.N_L)) = 0 := ZMod.natCast_self (sigma b.N_L)
    rw [hc]
    exact zero_mul _
  -- 4. The equation collapses to: `0 = 2 * N_L * N_R + 1` in ZMod.
  have h_lhs : ((2 * b.N_L * b.N_R + 1 : ℕ) : ZMod (sigma b.N_L)) =
    (2 * b.N_L : ZMod (sigma b.N_L)) * (b.N_R : ZMod (sigma b.N_L)) + 1 := by
    push_cast
    ring
  have h_comb : (2 * b.N_L : ZMod (sigma b.N_L)) * (b.N_R : ZMod (sigma b.N_L)) + 1 = 0 := by
    rw [← h_lhs, h_cast, h_rhs_zero]
  -- 5. Rearrange: `N_R * (2 * N_L) = -1` in ZMod.
  calc (b.N_R : ZMod (sigma b.N_L)) * (2 * b.N_L : ZMod (sigma b.N_L))
    _ = (2 * b.N_L : ZMod (sigma b.N_L)) * (b.N_R : ZMod (sigma b.N_L)) := mul_comm _ _
    _ = -1 := eq_neg_of_add_eq_zero_left h_comb

/--
  Contrapositive of `ambs_suffix_target`:
  If no N_R satisfying the bipartition's constraints also satisfies the modular
  QPN equation, then N cannot be quasiperfect. This is exactly what the Rust
  engine's ray-cast proves when it exhausts all candidate suffixes without finding
  σ(N) = 2N + 1: it has formally ruled out the existence of a QPN with this prefix.
-/
theorem no_solution_no_qpn (b : Bipartition)
    (h_no_sol : (b.N_R : ZMod (sigma b.N_L)) * (2 * b.N_L : ZMod (sigma b.N_L)) ≠ -1) :
    ¬ IsQuasiperfect b.N := by
  intro h_qpn
  exact h_no_sol (ambs_suffix_target b h_qpn)

end UALBF.Math.Bipartition
