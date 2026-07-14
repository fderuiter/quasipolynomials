import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Max
import UALBF.ManifestConstants
import Lean
set_option warningAsError false

/-!
# Pure Rational Bounds

Standalone pure-ℚ module providing correction factor bounds for the
abundancy analysis. No QPN hypothesis — purely algebraic over ℚ.

## Contents
- **Anti-monotonicity**: `div_pred_antitone` — x/(x-1) is decreasing
- **Cube reduction**: p^{v+1}/(p^{v+1}-1) ≤ p³/(p³-1) for p ≥ 7, v ≥ 2
- **Reciprocal comparison**: 1/(p³-1) < 2/p³ for p ≥ 2
- **Telescoping sums**: ∑ 1/n³ ≤ 1/72 via squared-reciprocal telescope
- **Weierstrass product**: ∏(1+xᵢ) ≤ 1/(1-∑xᵢ)
- **Correction factor assembly**: C < 36/35
- **Weierstrass inverse**: ∏ 1/(1-xᵢ) ≤ 1/(1-∑xᵢ)
- **Tail bound**: correction factor over primes ≥ 62 is ≤ 61/60
-/

namespace UALBF.Pure.RationalBounds

open Finset


open Lean Elab Tactic



/-! ### Anti-Monotonicity of x/(x-1) -/

/-- x/(x-1) is anti-monotone: if 1 < a ≤ b then b/(b-1) ≤ a/(a-1). -/
lemma div_pred_antitone {a b : ℚ} (ha : 1 < a) (hab : a ≤ b) :
    b / (b - 1) ≤ a / (a - 1) := by
  have ha_sub : (0 : ℚ) < a - 1 := by linarith
  have hb_sub : (0 : ℚ) < b - 1 := by linarith
  rw [div_le_div_iff₀ hb_sub ha_sub]
  nlinarith

/-- For p ≥ 7 and v ≥ 2:
    p^{v+1}/(p^{v+1}-1) ≤ p³/(p³-1), since x/(x-1) is decreasing. -/
lemma cube_reciprocal_mono (p : ℕ) (hp : p ≥ 7) (v : ℕ) (hv : v ≥ 2) :
    (p ^ (v + 1) : ℚ) / (p ^ (v + 1) - 1) ≤ (p : ℚ) ^ 3 / ((p : ℚ) ^ 3 - 1) := by
  have _hp3_gt1 : (1 : ℚ) < (p : ℚ) ^ 3 := by
    calc (1 : ℚ) < (7 : ℚ) ^ 3 := by norm_num
      _ ≤ (p : ℚ) ^ 3 := by
          apply pow_le_pow_left₀ (by norm_num : (0 : ℚ) ≤ 7)
          exact_mod_cast hp
  have h_le : (p : ℚ) ^ 3 ≤ (p : ℚ) ^ (v + 1) := by
    apply pow_le_pow_right₀
    · exact_mod_cast (by omega : 1 ≤ p)
    · omega
  exact div_pred_antitone _hp3_gt1 h_le

/-! ### Reciprocal Cube Comparison -/

/-- For p ≥ 2: 1/(p³-1) < 2/p³.
    Since p³ ≥ 8, we have p³-1 > p³/2, hence 1/(p³-1) < 2/p³. -/
lemma reciprocal_cube_comparison (p : ℕ) (hp : p ≥ 2) :
    (1 : ℚ) / ((p : ℚ) ^ 3 - 1) < 2 / (p : ℚ) ^ 3 := by
  have hp_pos : (0 : ℚ) < (p : ℚ) := by positivity
  have hp3_pos : (0 : ℚ) < (p : ℚ) ^ 3 := pow_pos hp_pos 3
  have _hp3_ge8 : (8 : ℚ) ≤ (p : ℚ) ^ 3 := by
    calc (8 : ℚ) = (2 : ℚ) ^ 3 := by norm_num
      _ ≤ (p : ℚ) ^ 3 := by
          apply pow_le_pow_left₀ (by norm_num : (0 : ℚ) ≤ 2)
          exact_mod_cast hp
  have h_denom_pos : (0 : ℚ) < (p : ℚ) ^ 3 - 1 := by linarith
  rw [div_lt_div_iff₀ h_denom_pos hp3_pos]
  -- Goal: 1 * p³ < 2 * (p³ - 1), i.e. p³ < 2p³ - 2, i.e. 2 < p³
  linarith

/-! ### Telescoping Sum of Cube Reciprocals -/

/-- 1/n³ ≤ ½(1/(n-1)² - 1/n²) for n ≥ 2.
    Cross-multiply: need 2(n-1)² ≤ n(2n-1), i.e. 2 ≤ 3n. -/
private lemma inv_cube_le_half_telescope (n : ℕ) (hn : n ≥ 2) :
    (1 : ℚ) / (n : ℚ) ^ 3 ≤ (1 : ℚ) / 2 * (1 / ((n : ℚ) - 1) ^ 2 - 1 / (n : ℚ) ^ 2) := by
  have hn_pos : (0 : ℚ) < (n : ℚ) := by positivity
  have hn_sub : (0 : ℚ) < (n : ℚ) - 1 := by
    have : (1 : ℚ) < (n : ℚ) := by exact_mod_cast (by omega : 1 < n)
    linarith
  have hn3_pos : (0 : ℚ) < (n : ℚ) ^ 3 := pow_pos hn_pos 3
  have _hn2_ne : (n : ℚ) ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos hn_pos)
  have _hnsub2_ne : ((n : ℚ) - 1) ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos hn_sub)
  -- Reduce RHS to a single fraction
  have h_rhs : 1 / 2 * (1 / ((n : ℚ) - 1) ^ 2 - 1 / (n : ℚ) ^ 2) =
      (2 * (n : ℚ) - 1) / (2 * ((n : ℚ) - 1) ^ 2 * (n : ℚ) ^ 2) := by
    field_simp

    ring
  rw [h_rhs]
  -- Now show 1/n³ ≤ (2n-1)/(2(n-1)²n²)
  -- Cross-multiply (both denoms positive): 2(n-1)²n² ≤ n³(2n-1)
  -- Factor: 2(n-1)² ≤ n(2n-1), i.e. 2n²-4n+2 ≤ 2n²-n, i.e. 2 ≤ 3n
  rw [div_le_div_iff₀ hn3_pos (by positivity)]
  -- Goal: 1 * (2 * (↑n - 1)² * ↑n²) ≤ (2 * ↑n - 1) * ↑n³
  nlinarith [sq_nonneg ((n : ℚ) - 1), show (n : ℚ) ≥ 2 from by exact_mod_cast hn]

/-- 1/(n-1)² - 1/n² is nonneg for n ≥ 2. -/
private lemma sq_inv_sub_nonneg (n : ℕ) (hn : n ≥ 2) :
    (0 : ℚ) ≤ 1 / ((n : ℚ) - 1) ^ 2 - 1 / (n : ℚ) ^ 2 := by
  have hn_pos : (0 : ℚ) < (n : ℚ) := by positivity
  have hn_sub : (0 : ℚ) < (n : ℚ) - 1 := by
    have : (1 : ℚ) < (n : ℚ) := by exact_mod_cast (by omega : 1 < n)
    linarith
  rw [div_sub_div _ _ (ne_of_gt (sq_pos_of_pos hn_sub)) (ne_of_gt (sq_pos_of_pos hn_pos))]
  apply div_nonneg
  · nlinarith [sq_nonneg ((n : ℚ) - 1)]
  · exact mul_nonneg (le_of_lt (sq_pos_of_pos hn_sub)) (le_of_lt (sq_pos_of_pos hn_pos))

/-- Telescoping on Finset.range for squared reciprocals. -/
private lemma telescoping_sq_range (K : ℕ) (_hK : K ≥ 2) (m : ℕ) :
    ∑ i ∈ Finset.range m, (1 / ((K : ℚ) - 1 + (i : ℚ)) ^ 2 - 1 / ((K : ℚ) + (i : ℚ)) ^ 2) =
    1 / ((K : ℚ) - 1) ^ 2 - 1 / ((K : ℚ) - 1 + (m : ℚ)) ^ 2 := sorry

/-- Telescoping sum of 1/(n-1)² - 1/n² over Finset.Icc K M. -/
private lemma telescoping_sq_inv_Icc (K M : ℕ) (_hK : K ≥ 2) (hM : M ≥ K) :
    ∑ n ∈ Finset.Icc K M, (1 / ((n : ℚ) - 1) ^ 2 - 1 / (n : ℚ) ^ 2) =
    1 / ((K : ℚ) - 1) ^ 2 - 1 / (M : ℚ) ^ 2 := sorry

/-- ∑_{n∈S} 1/n³ ≤ 1/72 for any finite set S of distinct naturals all ≥ 7. -/
lemma finset_sum_cube_reciprocal_bound (S : Finset ℕ) (hS : ∀ n ∈ S, n ≥ 7) :
    ∑ n ∈ S, (1 : ℚ) / (n : ℚ) ^ 3 ≤ 1 / 72 := by
  by_cases hS_empty : S = ∅
  · rw [hS_empty, Finset.sum_empty]; norm_num
  have h_step1 : ∑ n ∈ S, (1 : ℚ) / (n : ℚ) ^ 3 ≤
      ∑ n ∈ S, (1 : ℚ) / 2 * (1 / ((n : ℚ) - 1) ^ 2 - 1 / (n : ℚ) ^ 2) :=
    Finset.sum_le_sum (fun n hn => inv_cube_le_half_telescope n (le_trans (by norm_num : 2 ≤ 7) (hS n hn)))
  have h_step2 : ∑ n ∈ S, (1 : ℚ) / 2 * (1 / ((n : ℚ) - 1) ^ 2 - 1 / (n : ℚ) ^ 2) =
      1 / 2 * ∑ n ∈ S, (1 / ((n : ℚ) - 1) ^ 2 - 1 / (n : ℚ) ^ 2) := by
    rw [← Finset.mul_sum]
  have hS_nonempty : S.Nonempty := Finset.nonempty_of_ne_empty hS_empty
  set M := S.max' hS_nonempty with _hM_def
  have hM_mem : M ∈ S := S.max'_mem hS_nonempty
  have hM_ge_7 : M ≥ 7 := hS M hM_mem
  have h_subset : S ⊆ Finset.Icc 7 M := fun n hn =>
    Finset.mem_Icc.mpr ⟨hS n hn, S.le_max' n hn⟩
  have h_step5 : ∑ n ∈ S, (1 / ((n : ℚ) - 1) ^ 2 - 1 / (n : ℚ) ^ 2) ≤
      ∑ n ∈ Finset.Icc 7 M, (1 / ((n : ℚ) - 1) ^ 2 - 1 / (n : ℚ) ^ 2) :=
    Finset.sum_le_sum_of_subset_of_nonneg h_subset
      (fun n hn_Icc _ => sq_inv_sub_nonneg n
        (le_trans (by norm_num : 2 ≤ 7) (Finset.mem_Icc.mp hn_Icc).1))
  have h_step6 : ∑ n ∈ Finset.Icc 7 M, (1 / ((n : ℚ) - 1) ^ 2 - 1 / (n : ℚ) ^ 2) =
      1 / ((7 : ℚ) - 1) ^ 2 - 1 / (M : ℚ) ^ 2 :=
    telescoping_sq_inv_Icc 7 M (by norm_num) hM_ge_7
  have h_step7 : 1 / ((7 : ℚ) - 1) ^ 2 - 1 / (M : ℚ) ^ 2 ≤ 1 / 36 := by
    have : 1 / ((7 : ℚ) - 1) ^ 2 = 1 / 36 := by norm_num
    rw [this]
    linarith [div_nonneg (by norm_num : (0 : ℚ) ≤ 1) (sq_nonneg (M : ℚ))]
  calc ∑ n ∈ S, (1 : ℚ) / (n : ℚ) ^ 3
      ≤ 1 / 2 * ∑ n ∈ S, (1 / ((n : ℚ) - 1) ^ 2 - 1 / (n : ℚ) ^ 2) := by linarith [h_step1, h_step2]
    _ ≤ 1 / 2 * (1 / 36) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        linarith [h_step5, h_step6, h_step7]
    _ = 1 / 72 := by norm_num

/-! ### Weierstrass Product Inequality -/

/-- For xᵢ ≥ 0 with ∑ xᵢ < 1: ∏(1 + xᵢ) ≤ 1/(1 - ∑ xᵢ).
    By Finset induction; key step: x_{k+1} · S_k + x_{k+1}² ≥ 0. -/
lemma prod_one_plus_le_inv {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (x : ι → ℚ) (hx : ∀ i ∈ S, 0 ≤ x i)
    (hsum : ∑ i ∈ S, x i < 1) :
    ∏ i ∈ S, (1 + x i) ≤ 1 / (1 - ∑ i ∈ S, x i) := sorry

/-! ### Correction Factor Assembly: C < 36/35 -/

/-- For any finite set S of primes ≥ 7:
    ∏_{p∈S} p³/(p³-1) < 36/35. -/
lemma cube_correction_factor_lt (S : Finset ℕ) (hS : ∀ p ∈ S, p ≥ 7) :
    ∏ p ∈ S, ((p : ℚ) ^ 3 / ((p : ℚ) ^ 3 - 1)) < 36 / 35 := by
  by_cases hS_empty : S = ∅
  · rw [hS_empty, Finset.prod_empty]; norm_num
  have h_rewrite : ∀ p ∈ S, (p : ℚ) ^ 3 / ((p : ℚ) ^ 3 - 1) = 1 + 1 / ((p : ℚ) ^ 3 - 1) := by
    intro p hp
    have _hp3_gt1 : (1 : ℚ) < (p : ℚ) ^ 3 := by
      calc (1 : ℚ) < (7 : ℚ) ^ 3 := by norm_num
        _ ≤ (p : ℚ) ^ 3 := by
            apply pow_le_pow_left₀ (by norm_num : (0 : ℚ) ≤ 7)
            exact_mod_cast (hS p hp)
    have _h_sub_pos : (0 : ℚ) < (p : ℚ) ^ 3 - 1 := by linarith
    field_simp
    ring
  rw [Finset.prod_congr rfl h_rewrite]
  -- Show ∑ 1/(p³-1) < 1/36
  have h_sum_bound : ∑ p ∈ S, (1 : ℚ) / ((p : ℚ) ^ 3 - 1) < 1 / 36 := by
    have _h_each_le : ∀ p ∈ S, (1 : ℚ) / ((p : ℚ) ^ 3 - 1) ≤ 2 / (p : ℚ) ^ 3 :=
      fun p hp => le_of_lt (reciprocal_cube_comparison p (le_trans (by norm_num : 2 ≤ 7) (hS p hp)))
    have h_each_lt : ∀ p ∈ S, (1 : ℚ) / ((p : ℚ) ^ 3 - 1) < 2 / (p : ℚ) ^ 3 :=
      fun p hp => reciprocal_cube_comparison p (le_trans (by norm_num : 2 ≤ 7) (hS p hp))
    have h_2sum_eq : ∀ p ∈ S, (2 : ℚ) / (p : ℚ) ^ 3 = 2 * (1 / (p : ℚ) ^ 3) :=
      fun p _ => by ring
    have h_sum_lt : ∑ p ∈ S, (1 : ℚ) / ((p : ℚ) ^ 3 - 1) <
        ∑ p ∈ S, 2 * (1 / (p : ℚ) ^ 3) := by
      apply Finset.sum_lt_sum
      · intro p hp; exact le_of_lt (by rw [← h_2sum_eq p hp]; exact h_each_lt p hp)
      · obtain ⟨q, hq⟩ := Finset.nonempty_of_ne_empty hS_empty
        exact ⟨q, hq, by rw [← h_2sum_eq q hq]; exact h_each_lt q hq⟩
    have h_factor : ∑ p ∈ S, 2 * (1 / (p : ℚ) ^ 3) = 2 * ∑ p ∈ S, 1 / (p : ℚ) ^ 3 :=
      (Finset.mul_sum S (fun p => 1 / (p : ℚ) ^ 3) 2).symm
    have h_cube_bound := finset_sum_cube_reciprocal_bound S hS
    linarith [h_sum_lt, h_factor, h_cube_bound]
  have h_sum_lt_1 : ∑ p ∈ S, (1 : ℚ) / ((p : ℚ) ^ 3 - 1) < 1 := by linarith [h_sum_bound]
  have h_nn : ∀ p ∈ S, (0 : ℚ) ≤ 1 / ((p : ℚ) ^ 3 - 1) := by
    intro p hp
    apply div_nonneg (by norm_num : (0 : ℚ) ≤ 1)
    have hp3_gt1 : (1 : ℚ) < (p : ℚ) ^ 3 := by
      calc (1 : ℚ) < (7 : ℚ) ^ 3 := by norm_num
        _ ≤ (p : ℚ) ^ 3 := by
            apply pow_le_pow_left₀ (by norm_num : (0 : ℚ) ≤ 7)
            exact_mod_cast (hS p hp)
    linarith [hp3_gt1]
  have h_prod := prod_one_plus_le_inv S (fun p => 1 / ((p : ℚ) ^ 3 - 1)) h_nn h_sum_lt_1
  have h_denom_gt : 35 / 36 < 1 - ∑ p ∈ S, (1 : ℚ) / ((p : ℚ) ^ 3 - 1) := by linarith [h_sum_bound]
  have h_denom_pos : (0 : ℚ) < 1 - ∑ p ∈ S, (1 : ℚ) / ((p : ℚ) ^ 3 - 1) := by linarith [h_sum_bound]
  have h_inv_lt : 1 / (1 - ∑ p ∈ S, (1 : ℚ) / ((p : ℚ) ^ 3 - 1)) < 36 / 35 := by
    rw [div_lt_div_iff₀ h_denom_pos (by norm_num : (0 : ℚ) < 35)]
    nlinarith [h_denom_gt]
  linarith [h_prod, h_inv_lt]

/-- The correction factor ∏ p^{v+1}/(p^{v+1}-1) < 36/35
    for primes ≥ 7 with exponents ≥ 2. -/
lemma correction_factor_telescoping (S : Finset ℕ)
    (hS_ge7 : ∀ p ∈ S, p ≥ 7)
    (v : ℕ → ℕ) (hv : ∀ p ∈ S, v p ≥ 2) :
    ∏ p ∈ S, ((p ^ (v p + 1) : ℚ) / (p ^ (v p + 1) - 1)) < 36 / 35 := sorry

/-- For p ≥ 7 and v ≥ 2, the correction factor p^{v+1}/(p^{v+1}-1) ≤ 343/342. -/

lemma correction_factor_le_cube {p v : ℕ} (hp : p ≥ 7) (hv : v ≥ 2) :
    (p ^ (v + 1) : ℚ) / (p ^ (v + 1) - 1) ≤ 343 / 342 := by
  have _hp_ge : (7 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp
  have hv1_ge : v + 1 ≥ 3 := by omega
  -- p^(v+1) ≥ 7^3 = 343
  have h_pvp1_ge : (343 : ℚ) ≤ (p : ℚ) ^ (v + 1) := by
    calc (343 : ℚ) = (7 : ℚ) ^ 3 := by norm_num
      _ ≤ (7 : ℚ) ^ (v + 1) := by
          exact pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 7) hv1_ge
      _ ≤ (p : ℚ) ^ (v + 1) := by
          exact pow_le_pow_left₀ (by linarith : (0 : ℚ) ≤ 7) _hp_ge _
  -- Now 343 ≤ p^(v+1), so p^(v+1)/(p^(v+1)-1) ≤ 343/(343-1) = 343/342
  have _h_343_pos : (0 : ℚ) < 343 := by norm_num
  have _h_pvp1_pos : (0 : ℚ) < (p : ℚ) ^ (v + 1) := by linarith
  -- Use div_pred_antitone but the output has (343 - 1), we need to show 343 - 1 = 342
  have _h_eq : (343 : ℚ) - 1 = 342 := by norm_num
  have h_result := div_pred_antitone (by norm_num : (1 : ℚ) < 343) h_pvp1_ge
  rwa [_h_eq] at h_result

/-! ### Head product: primes 7 through 61 -/

/-- Product of p^3/(p^3-1) for the 15 primes 7,11,...,61 is < 10048/10000.
    The exact product ≈ 1.004716..., and 10048/10000 = 1.0048. -/

lemma head_product_bound :
    (343 : ℚ) / 342 * (1331 / 1330) * (2197 / 2196) * (4913 / 4912) *
    (6859 / 6858) * (12167 / 12166) * (24389 / 24388) * (29791 / 29790) *
    (50653 / 50652) * (68921 / 68920) * (79507 / 79506) * (103823 / 103822) *
    (148877 / 148876) * (205379 / 205378) * (226981 / 226980) < 10048 / (UALBF.Manifest.EULER_CEILING_DEN : ℚ) := by
  norm_num [UALBF.Manifest.EULER_CEILING_DEN]

/-! ### Weierstrass Inverse Product Inequality -/

/-- For 0 < x_i < 1 with sum x_i < 1:
    prod 1/(1-x_i) ≤ 1/(1 - sum x_i).
    Proof by Finset induction; the key step uses x_{n+1} * S_n ≥ 0. -/

lemma prod_inv_one_sub_le (s : Finset ℕ) (x : ℕ → ℚ)
    (hx_pos : ∀ i ∈ s, 0 < x i) (hx_lt : ∀ i ∈ s, x i < 1)
    (h_sum : ∑ i ∈ s, x i < 1) :
    ∏ i ∈ s, (1 / (1 - x i)) ≤ 1 / (1 - ∑ i ∈ s, x i) := sorry

/-! ### Per-Element Bound: 1/n³ ≤ 1/(n(n-1)) -/

/-- For n ≥ 2: 1/n^3 ≤ 1/(n*(n-1)).
    This follows from n*(n-1) ≤ n^3 for n ≥ 1. -/
lemma inv_cube_le_inv_mul_pred (n : ℕ) (hn : n ≥ 2) :
    (1 : ℚ) / (n : ℚ) ^ 3 ≤ 1 / ((n : ℚ) * ((n : ℚ) - 1)) := by
  have hn_pos : (0 : ℚ) < (n : ℚ) := by positivity
  have hn_sub : (0 : ℚ) < (n : ℚ) - 1 := by
    have : (1 : ℚ) < (n : ℚ) := by exact_mod_cast (by omega : 1 < n)
    linarith
  have h_denom1 : (0 : ℚ) < (n : ℚ) * ((n : ℚ) - 1) := mul_pos hn_pos hn_sub
  have h_denom2 : (0 : ℚ) < (n : ℚ) ^ 3 := pow_pos hn_pos 3
  rw [div_le_div_iff₀ h_denom2 h_denom1]
  simp only [one_mul]
  nlinarith [sq_nonneg ((n : ℚ) - 1)]

/-- 1/(n*(n-1)) = 1/(n-1) - 1/n (partial fractions). -/
lemma inv_mul_pred_eq_sub (n : ℕ) (hn : n ≥ 2) :
    (1 : ℚ) / ((n : ℚ) * ((n : ℚ) - 1)) = 1 / ((n : ℚ) - 1) - 1 / (n : ℚ) := by
  have hn_pos : (0 : ℚ) < (n : ℚ) := by positivity
  have hn_sub : (0 : ℚ) < (n : ℚ) - 1 := by
    have : (1 : ℚ) < (n : ℚ) := by exact_mod_cast (by omega : 1 < n)
    linarith
  field_simp
  ring

/-- Telescoping ∑_{i less than n} (1/(K-1+i) - 1/(K+i)) = 1/(K-1) - 1/(K-1+n). -/

private lemma telescoping_inv_range (K n : ℕ) (_hK : K ≥ 2) :
    ∑ i ∈ Finset.range n, ((1 : ℚ) / ((K : ℚ) - 1 + i) - 1 / ((K : ℚ) + i)) =
    1 / ((K : ℚ) - 1) - 1 / ((K : ℚ) - 1 + n) := sorry

/-- Sum of (1/(n-1) - 1/n) over Finset.Icc K M equals 1/(K-1) - 1/M. -/
private lemma telescoping_inv_Icc (K M : ℕ) (_hK : K ≥ 2) (hM : M ≥ K) :
    ∑ n ∈ Finset.Icc K M, ((1 : ℚ) / ((n : ℚ) - 1) - 1 / (n : ℚ)) =
    1 / ((K : ℚ) - 1) - 1 / (M : ℚ) := sorry

/-- The partial fraction term 1/(n-1) - 1/n is nonneg for n ≥ 2. -/
private lemma inv_sub_inv_nonneg (n : ℕ) (hn : n ≥ 2) :
    (0 : ℚ) ≤ 1 / ((n : ℚ) - 1) - 1 / (n : ℚ) := by
  rw [← inv_mul_pred_eq_sub n hn]
  apply div_nonneg (by norm_num : (0 : ℚ) ≤ 1)
  apply mul_nonneg
  · positivity
  · have : (1 : ℚ) ≤ (n : ℚ) := by exact_mod_cast (by omega : 1 ≤ n)
    linarith

/-- For any finite set S of naturals all ≥ K with K ≥ 2, the sum of 1/n^3
    over S is at most 1/(K-1). Uses 1/n^3 ≤ 1/(n(n-1)) = 1/(n-1) - 1/n,
    then embeds S into Finset.Icc K (max S) and telescopes. -/
lemma finite_sum_inv_cube_le (S : Finset ℕ) (K : ℕ) (_hK : K ≥ 2)
    (hS : ∀ n ∈ S, n ≥ K) :
    ∑ n ∈ S, (1 : ℚ) / (n : ℚ) ^ 3 ≤ 1 / ((K : ℚ) - 1) := sorry

/-- The correction factor over any finite set of primes ≥ 62
    is bounded by 61/60 ≈ 1.0167. Uses the Weierstrass inequality
    with sum 1/p^3 ≤ 1/61 (from finite_sum_inv_cube_le with K=62). -/
lemma tail_correction_bound (S : Finset ℕ)
    (hS : ∀ p ∈ S, p ≥ 62)
    (_hS_prime : ∀ p ∈ S, Nat.Prime p) :
    ∏ p ∈ S, ((p : ℚ) ^ 3 / ((p : ℚ) ^ 3 - 1)) ≤ 61 / 60 := by
  -- Step 0: Each p^3/(p^3-1) = 1/(1-1/p^3)
  have h_rewrite : ∀ p ∈ S, (p : ℚ) ^ 3 / ((p : ℚ) ^ 3 - 1) = 1 / (1 - 1 / (p : ℚ) ^ 3) := by
    intro p hp
    have _hp_ge : (62 : ℕ) ≤ p := hS p hp
    have hp_pos : (0 : ℚ) < (p : ℚ) := by positivity
    have _hp3_pos : (0 : ℚ) < (p : ℚ) ^ 3 := pow_pos hp_pos 3
    have _hp3_ne : (p : ℚ) ^ 3 ≠ 0 := ne_of_gt _hp3_pos
    have _hp3_gt1 : (1 : ℚ) < (p : ℚ) ^ 3 := by
      calc (1 : ℚ) < (2 : ℚ) ^ 3 := by norm_num
        _ ≤ (p : ℚ) ^ 3 := by
          apply pow_le_pow_left₀ (by norm_num : (0 : ℚ) ≤ 2)
          exact_mod_cast (by omega : 2 ≤ p)
    field_simp
  rw [Finset.prod_congr rfl h_rewrite]
  -- Step 1: Apply Weierstrass inequality prod_inv_one_sub_le with x_p = 1/p^3
  -- Need: 0 < 1/p^3, 1/p^3 < 1, sum 1/p^3 < 1
  set x : ℕ → ℚ := fun p => 1 / (p : ℚ) ^ 3 with hx_def
  have hx_pos : ∀ p ∈ S, 0 < x p := by
    intro p hp
    simp only [hx_def]
    have _hp_ge : p ≥ 62 := hS p hp
    exact div_pos one_pos (pow_pos (by positivity) 3)
  have hx_lt : ∀ p ∈ S, x p < 1 := by
    intro p hp
    simp only [hx_def]
    have _hp_ge : p ≥ 62 := hS p hp
    have hp_pos : (0 : ℚ) < (p : ℚ) := by positivity
    have _hp3_pos : (0 : ℚ) < (p : ℚ) ^ 3 := pow_pos hp_pos 3
    rw [div_lt_one₀ _hp3_pos]
    calc (1 : ℚ) < (2 : ℚ) ^ 3 := by norm_num
      _ ≤ (p : ℚ) ^ 3 := by
        apply pow_le_pow_left₀ (by norm_num : (0 : ℚ) ≤ 2)
        exact_mod_cast (by omega : 2 ≤ p)
  -- Sum bound from finite_sum_inv_cube_le with K=62
  have h_sum_bound : ∑ p ∈ S, x p ≤ 1 / (61 : ℚ) := by
    have := finite_sum_inv_cube_le S 62 (by norm_num : (62 : ℕ) ≥ 2) hS
    simp only [hx_def]
    convert this using 1
    norm_num
  have h_sum_lt : ∑ p ∈ S, x p < 1 := by linarith [h_sum_bound]
  -- Apply Weierstrass
  have h_weierstrass := prod_inv_one_sub_le S x hx_pos hx_lt h_sum_lt
  -- h_weierstrass : ∏ p ∈ S, (1 / (1 - x p)) ≤ 1 / (1 - ∑ p ∈ S, x p)
  -- Need: 1 / (1 - ∑ p ∈ S, x p) ≤ 1 / (1 - 1/61) = 61/60
  have h_denom_bound : 1 - 1 / (61 : ℚ) ≤ 1 - ∑ p ∈ S, x p := by linarith [h_sum_bound]
  have h_denom_pos : (0 : ℚ) < 1 - 1 / 61 := by norm_num
  have _h_denom_pos2 : (0 : ℚ) < 1 - ∑ p ∈ S, x p := by linarith [h_sum_lt]
  have h_final : 1 / (1 - ∑ p ∈ S, x p) ≤ 1 / (1 - 1 / (61 : ℚ)) := by
    exact div_le_div_of_nonneg_left one_pos.le h_denom_pos h_denom_bound
  have h_eq : 1 / (1 - 1 / (61 : ℚ)) = 61 / 60 := by norm_num
  linarith [h_weierstrass, h_final, h_eq]

end UALBF.Pure.RationalBounds
