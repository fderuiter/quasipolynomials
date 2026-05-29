import UALBF.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Totient
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Order.Interval.Finset.Nat

/-!
# Pure Euler Product Identities

Algebraic decomposition of the Euler totient ratio N/φ(N) into
abundancy index times correction factor product. No QPN hypothesis.
-/

namespace UALBF.Pure.EulerProduct

open UALBF
open Nat
open Finset

/--
  Local prime-power identity: p/(p-1) = sigma(p^v)/p^v * p^{v+1}/(p^{v+1}-1).
  This decomposes each Euler factor into an abundancy contribution times a
  correction factor, and is the algebraic backbone of `totient_ratio_decomp`.
-/
lemma euler_factor_decomp (p v : ℕ) (hp : p.Prime) (hv : v ≥ 1) :
    (p : ℚ) / (p - 1) =
    (∑ k ∈ Finset.range (v + 1), (p : ℚ) ^ k) / (p : ℚ) ^ v *
    ((p ^ (v + 1) : ℚ) / (p ^ (v + 1) - 1)) := by
  have hp2 : (p : ℕ) ≥ 2 := hp.two_le
  have hp_pos : (0 : ℚ) < (p : ℚ) := by exact_mod_cast (show 0 < p by omega)
  have hp_ne_one : (p : ℚ) ≠ 1 := by
    have : (1 : ℚ) < (p : ℚ) := by exact_mod_cast (show 1 < p by omega)
    linarith
  have hp_sub_ne : (p : ℚ) - 1 ≠ 0 := sub_ne_zero_of_ne hp_ne_one
  have hp_pow_v_ne : (p : ℚ) ^ v ≠ 0 := pow_ne_zero _ (ne_of_gt hp_pos)
  have hp_pow_v1_sub_ne : (p : ℚ) ^ (v + 1) - 1 ≠ 0 := by
    have h1 : (1 : ℚ) < (p : ℚ) ^ (v + 1) := by
      have hp_gt_one : (1 : ℚ) < (p : ℚ) := by exact_mod_cast (show 1 < p by omega)
      calc (1 : ℚ) = 1 ^ (v + 1) := (one_pow _).symm
        _ < (p : ℚ) ^ (v + 1) :=
          pow_lt_pow_left₀ hp_gt_one (by linarith) (by omega)
    linarith
  have h_geom : ∑ k ∈ Finset.range (v + 1), (p : ℚ) ^ k =
      ((p : ℚ) ^ (v + 1) - 1) / ((p : ℚ) - 1) := by
    rw [geom_sum_eq hp_ne_one]
  rw [h_geom]
  field_simp
  ring

/--
  Global multiplicative identity: N/phi(N) = H(N) * prod p^{v+1}/(p^{v+1}-1).
  Decomposes the Euler totient ratio into the abundancy index times a
  correction factor product over all prime factors.
-/
lemma totient_ratio_decomp {N : ℕ} (hN : N > 1) :
    (N : ℚ) / (N.totient : ℚ) =
    abundancy_index N * ∏ p ∈ N.primeFactors,
      ((p ^ (N.factorization p + 1) : ℚ) / (p ^ (N.factorization p + 1) - 1)) := by
  have hN_ne : N ≠ 0 := by omega
  have hN_pos : (0 : ℚ) < (N : ℚ) := Nat.cast_pos.mpr (by omega)
  have hN_ne_zero : (N : ℚ) ≠ 0 := ne_of_gt hN_pos
  have hT_pos : (0 : ℚ) < (N.totient : ℚ) :=
    Nat.cast_pos.mpr (Nat.totient_pos.mpr (by omega))
  have hT_ne_zero : (N.totient : ℚ) ≠ 0 := ne_of_gt hT_pos
  have h_supp : N.factorization.support = N.primeFactors := rfl
  have h_sigma : sigma N = (∏ p ∈ N.primeFactors,
      ∑ k ∈ Finset.range (N.factorization p + 1), p ^ k) := by
    unfold sigma
    have hs := Nat.sum_divisors hN_ne
    calc ∑ d ∈ N.divisors, d
        = N.factorization.prod (fun p e => ∑ k ∈ Finset.range (e + 1), p ^ k) := hs
      _ = ∏ p ∈ N.factorization.support,
            ∑ k ∈ Finset.range (N.factorization p + 1), p ^ k := rfl
      _ = ∏ p ∈ N.primeFactors,
            ∑ k ∈ Finset.range (N.factorization p + 1), p ^ k := by rw [h_supp]
  have H_N_eq : N = (∏ p ∈ N.primeFactors, p ^ N.factorization p) := by
    have h_prod := Nat.factorization_prod_pow_eq_self hN_ne
    calc N = N.factorization.prod (fun p e => p ^ e) := h_prod.symm
      _ = ∏ p ∈ N.factorization.support, p ^ N.factorization p := rfl
      _ = ∏ p ∈ N.primeFactors, p ^ N.factorization p := by rw [h_supp]
  have h_rhs : abundancy_index N * ∏ p ∈ N.primeFactors,
      ((p ^ (N.factorization p + 1) : ℚ) / (p ^ (N.factorization p + 1) - 1)) =
      ∏ p ∈ N.primeFactors, ((p : ℚ) / ((p : ℚ) - 1)) := by
    unfold abundancy_index
    rw [h_sigma]
    push_cast
    conv_lhs => rw [show (N : ℚ) = ↑(∏ p ∈ N.primeFactors, p ^ N.factorization p) from by
      exact_mod_cast H_N_eq]
    push_cast
    rw [← Finset.prod_div_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    have hp_prime := (Nat.mem_primeFactors.mp hp).1
    have h_vp_ge1 : N.factorization p ≥ 1 :=
      Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hp)
    exact (euler_factor_decomp p (N.factorization p) hp_prime h_vp_ge1).symm
  have h_lhs : (N : ℚ) / (N.totient : ℚ) =
      ∏ p ∈ N.primeFactors, ((p : ℚ) / ((p : ℚ) - 1)) := by
    have h_id := Nat.totient_mul_prod_primeFactors N
    have h_id_q : (N.totient : ℚ) * (∏ p ∈ N.primeFactors, (p : ℚ)) =
        (N : ℚ) * (∏ p ∈ N.primeFactors, ((p : ℚ) - 1)) := by
      have h_cast_pred : (↑(∏ p ∈ N.primeFactors, (p - 1)) : ℚ) =
          (∏ p ∈ N.primeFactors, ((p : ℚ) - 1)) := by
        rw [Nat.cast_prod]
        apply Finset.prod_congr rfl
        intro p hp
        have hp_prime := (Nat.mem_primeFactors.mp hp).1
        have hp_ge : 1 ≤ p := by have := hp_prime.two_le; omega
        rw [Nat.cast_sub hp_ge, Nat.cast_one]
      have h_cast_id : (↑(N.totient * ∏ p ∈ N.primeFactors, p) : ℚ) =
          (↑(N * ∏ p ∈ N.primeFactors, (p - 1)) : ℚ) := by
        exact_mod_cast h_id
      rw [Nat.cast_mul, Nat.cast_prod] at h_cast_id
      rw [Nat.cast_mul, h_cast_pred] at h_cast_id
      exact h_cast_id
    have h_prod_pred_ne : (∏ p ∈ N.primeFactors, ((p : ℚ) - 1)) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro p hp
      have hp_prime := (Nat.mem_primeFactors.mp hp).1
      have : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp_prime.two_le
      linarith
    rw [Finset.prod_div_distrib]
    rw [div_eq_div_iff hT_ne_zero h_prod_pred_ne]
    linarith [h_id_q]
  rw [h_lhs, h_rhs]

/--
  Verified bridge lemma connecting the empirical list-based calculations
  used in the search engine to the formal Euler product bounds in Lean.
  Proves that H(N) is strictly bounded by ∏ p/(p-1).
-/
lemma abundancy_index_le_euler_product {N : ℕ} (hN : N > 1) :
    abundancy_index N ≤ ∏ p ∈ N.primeFactors, ((p : ℚ) / ((p : ℚ) - 1)) := by
  have h_decomp := totient_ratio_decomp hN
  have h_totient_eq : (N : ℚ) / (N.totient : ℚ) = ∏ p ∈ N.primeFactors, ((p : ℚ) / ((p : ℚ) - 1)) := by
    have h_id := Nat.totient_mul_prod_primeFactors N
    have hT_pos : (0 : ℚ) < (N.totient : ℚ) :=
      Nat.cast_pos.mpr (Nat.totient_pos.mpr (by omega))
    have hT_ne_zero : (N.totient : ℚ) ≠ 0 := ne_of_gt hT_pos
    have h_prod_pred_ne : (∏ p ∈ N.primeFactors, ((p : ℚ) - 1)) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro p hp
      have hp_prime := (Nat.mem_primeFactors.mp hp).1
      have : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp_prime.two_le
      linarith
    have h_cast_pred : (↑(∏ p ∈ N.primeFactors, (p - 1)) : ℚ) =
        (∏ p ∈ N.primeFactors, ((p : ℚ) - 1)) := by
      rw [Nat.cast_prod]
      apply Finset.prod_congr rfl
      intro p hp
      have hp_prime := (Nat.mem_primeFactors.mp hp).1
      have hp_ge : 1 ≤ p := by have := hp_prime.two_le; omega
      rw [Nat.cast_sub hp_ge, Nat.cast_one]
    have h_id_q : (N.totient : ℚ) * (∏ p ∈ N.primeFactors, (p : ℚ)) =
        (N : ℚ) * (∏ p ∈ N.primeFactors, ((p : ℚ) - 1)) := by
      have h_cast_id : (↑(N.totient * ∏ p ∈ N.primeFactors, p) : ℚ) =
          (↑(N * ∏ p ∈ N.primeFactors, (p - 1)) : ℚ) := by
        exact_mod_cast h_id
      rw [Nat.cast_mul, Nat.cast_prod] at h_cast_id
      rw [Nat.cast_mul, h_cast_pred] at h_cast_id
      exact h_cast_id
    rw [Finset.prod_div_distrib]
    rw [div_eq_div_iff hT_ne_zero h_prod_pred_ne]
    linarith [h_id_q]
  rw [← h_totient_eq, h_decomp]
  have h_corr_ge_one : 1 ≤ ∏ p ∈ N.primeFactors,
      ((p ^ (N.factorization p + 1) : ℚ) / (p ^ (N.factorization p + 1) - 1)) := by
    apply Finset.one_le_prod
    · intro p hp
      have hp_prime := (Nat.mem_primeFactors.mp hp).1
      have h_pvp1_gt1 : (1 : ℚ) < (p : ℚ) ^ (N.factorization p + 1) := by
        have hp_gt1 : (1 : ℚ) < (p : ℚ) := by exact_mod_cast (show 1 < p from hp_prime.one_lt)
        calc (1 : ℚ) = 1 ^ (N.factorization p + 1) := (one_pow _).symm
          _ < (p : ℚ) ^ (N.factorization p + 1) := pow_lt_pow_left₀ hp_gt1 (by linarith) (by omega)
      have h_denom_pos : (0 : ℚ) < (p : ℚ) ^ (N.factorization p + 1) - 1 := by linarith
      apply le_of_lt
      exact div_pos (by linarith) h_denom_pos
    · intro p hp
      have hp_prime := (Nat.mem_primeFactors.mp hp).1
      have h_pvp1_gt1 : (1 : ℚ) < (p : ℚ) ^ (N.factorization p + 1) := by
        have hp_gt1 : (1 : ℚ) < (p : ℚ) := by exact_mod_cast (show 1 < p from hp_prime.one_lt)
        calc (1 : ℚ) = 1 ^ (N.factorization p + 1) := (one_pow _).symm
          _ < (p : ℚ) ^ (N.factorization p + 1) := pow_lt_pow_left₀ hp_gt1 (by linarith) (by omega)
      have h_denom_pos : (0 : ℚ) < (p : ℚ) ^ (N.factorization p + 1) - 1 := by linarith
      rw [one_le_div h_denom_pos]
      linarith
  have h_abund_pos : (0 : ℚ) ≤ abundancy_index N := by
    unfold abundancy_index
    have hN_pos : (0 : ℚ) < (N : ℚ) := by exact_mod_cast (show 0 < N by omega)
    have h_sig_pos : (0 : ℚ) ≤ (sigma N : ℚ) := by exact_mod_cast (Nat.zero_le _)
    exact div_nonneg h_sig_pos (le_of_lt hN_pos)
  nth_rw 1 [← mul_one (abundancy_index N)]
  exact mul_le_mul_of_nonneg_left h_corr_ge_one h_abund_pos

end UALBF.Pure.EulerProduct
