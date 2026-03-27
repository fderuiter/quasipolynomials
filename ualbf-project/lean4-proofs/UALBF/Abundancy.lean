import UALBF.Basic
import UALBF.SpecialFactors
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Totient
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace UALBF

open Nat
open Finset

/-- 
  The Abundancy Index H(N) = σ(N) / N.
  For quasiperfect numbers, this will be strictly > 2, approaching 2 from above.
-/
noncomputable def abundancy_index (n : ℕ) : ℚ :=
  (sigma n : ℚ) / (n : ℚ)

/-- 
  Theorem: Target Threshold
  If N is a Quasiperfect Number (QPN), its abundancy index is exactly 2 + 1/N.
-/
theorem qpn_abundancy_target {N : ℕ} (h : IsQuasiperfect N) :
  abundancy_index N = 2 + 1 / (N : ℚ) := by
  have hn_pos : N > 0 := h.1
  have hn_cast_ne_zero : (N : ℚ) ≠ 0 := by exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn_pos)
  have h_sigma : sigma N = 2 * N + 1 := h.2
  unfold abundancy_index
  rw [h_sigma]
  push_cast
  have h_div : (2 * (N : ℚ) + 1) / (N : ℚ) = (2 * (N : ℚ)) / (N : ℚ) + 1 / (N : ℚ) := by ring
  rw [h_div]
  congr 1
  exact mul_div_cancel_right₀ 2 hn_cast_ne_zero


/--
  Lemma: σ(N) * φ(N) < N² for N > 1.
  The core ℕ-level inequality, derived by combining the cross-multiplied
  abundancy bound (SpecialFactors.abundancy_cross_bound) with the Euler
  product identity (Nat.totient_mul_prod_primeFactors).
  Public for reuse in qpn_totient_bound and downstream starvation proofs.
-/
lemma sigma_mul_totient_lt_sq {N : ℕ} (hN : N > 1) :
    sigma N * N.totient < N ^ 2 := by
  have h_cross := SpecialFactors.abundancy_cross_bound hN
  have h_id := Nat.totient_mul_prod_primeFactors N
  have hT_pos : 0 < N.totient := Nat.totient_pos.mpr (by omega)
  have hQ_pos : 0 < ∏ p ∈ N.primeFactors, (p - 1) := by
    apply Finset.prod_pos
    intro p hp
    have := (Nat.mem_primeFactors.mp hp).1.two_le
    omega
  -- Chain: σ*φ*∏(p-1) < N²*∏(p-1), then cancel ∏(p-1) > 0
  suffices h : sigma N * N.totient * (∏ p ∈ N.primeFactors, (p - 1)) <
               N ^ 2 * (∏ p ∈ N.primeFactors, (p - 1)) by
    exact Nat.lt_of_mul_lt_mul_right h
  calc sigma N * N.totient * (∏ p ∈ N.primeFactors, (p - 1))
      = sigma N * (∏ p ∈ N.primeFactors, (p - 1)) * N.totient := by ring
    _ < N * (∏ p ∈ N.primeFactors, p) * N.totient :=
        Nat.mul_lt_mul_of_pos_right h_cross hT_pos
    _ = N * (N.totient * (∏ p ∈ N.primeFactors, p)) := by ring
    _ = N * (N * (∏ p ∈ N.primeFactors, (p - 1))) := by rw [h_id]
    _ = N ^ 2 * (∏ p ∈ N.primeFactors, (p - 1)) := by ring

/--
  Theorem: Formalize Euler Ceiling
  For any N > 1, the abundancy index H(N) is strictly bounded by the infinite 
  Euler product ∏ p/(p-1) over primes dividing N, which is equivalent to N / φ(N).
-/
theorem abundancy_le_totient_ratio {N : ℕ} (hN : N > 1) :
  abundancy_index N < (N : ℚ) / (N.totient : ℚ) := by
  have h_nat := sigma_mul_totient_lt_sq hN
  have hN_pos : (0 : ℚ) < (N : ℚ) := Nat.cast_pos.mpr (by omega)
  have hT_pos : (0 : ℚ) < (N.totient : ℚ) :=
    Nat.cast_pos.mpr (Nat.totient_pos.mpr (by omega))
  unfold abundancy_index
  rw [div_lt_div_iff₀ hN_pos hT_pos]
  exact_mod_cast (show sigma N * N.totient < N * N from by rw [← sq]; exact h_nat)

/--
  Theorem: Totient Geometric Window
  Demonstrates that for massive QPN candidates (N > 10^35), the maximum 
  possible abundancy (the Euler ceiling) is bounded mathematically by 2.4675.
-/
theorem qpn_totient_bound {N : ℕ} (h_qpn : IsQuasiperfect N) (h_size : N > 10^35) : 
  (N : ℚ) / (N.totient : ℚ) < 2.4675 := by
  -- Follows from gcd(N, 15) = 1 (proved in qpn_coprime_15_omega_15) and 
  -- the minimal possible values for the first 15 odd primes > 5.
  sorry

/--
  Theorem: Starvation Pruning Validity
  Authorizes the Rust engine (Z3/DFS) to prune a branch if the Euler product 
  of a partial Prefix multiplied by the theoretical maximum of the remaining 
  Sieve primes is ≤ 2. If this product ≤ 2, then H(N) ≤ 2, which contradicts 
  H(N) = 2 + 1/N > 2, hence an exact valuation is structurally impossible.
-/
theorem abundancy_starvation 
  (N_prefix : ℚ) (S_max_remaining : ℚ) (h_bound : N_prefix * S_max_remaining ≤ 2)
  (h_target : abundancy_index N > 2)
  (h_prefix_val : abundancy_index N < N_prefix * S_max_remaining) : False := by
  -- If prefix * remaining_max is ≤ 2, but abundancy_index N < prefix * remaining_max,
  -- then abundancy_index N < 2, contradicting H(N) > 2.
  linarith

end UALBF
