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

set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.unreachableTactic false

/-!
# CorrectionFactor: Path B Fixed — Telescoping Sum Approach

Standalone module providing five lemmas that bound the correction factor
C = ∏ₚ p^{vₚ+1}/(p^{vₚ+1}-1) < 36/35 for any finite set of primes ≥ 7
with exponents ≥ 2. Uses only ℚ arithmetic — no Mathlib.Analysis imports.

## Mathematical Outline (PATH_B_ANALYSIS.md §4–6)

1. **Monotonicity**: p^{v+1}/(p^{v+1}-1) ≤ p³/(p³-1) for p ≥ 7, v ≥ 2
2. **Reciprocal comparison**: 1/(p³-1) < 2/p³ for p ≥ 2
3. **Telescoping sum**: ∑_{n∈S} 1/n³ ≤ 1/72 for distinct n ≥ 7
4. **Product-sum inequality**: ∏(1+xᵢ) ≤ 1/(1-∑xᵢ) by Finset induction
5. **Assembly**: C < 36/35
-/

namespace UALBF.Compute.CorrectionFactor

open Finset

-- ════════════════════════════════════════════════════════════════════
-- Lemma 1: cube_reciprocal_mono
-- ════════════════════════════════════════════════════════════════════

/-- x/(x-1) is anti-monotone: if 1 < a ≤ b then b/(b-1) ≤ a/(a-1). -/
private lemma div_pred_antitone' {a b : ℚ} (ha : 1 < a) (hab : a ≤ b) :
    b / (b - 1) ≤ a / (a - 1) := by
  have ha_sub : (0 : ℚ) < a - 1 := by linarith
  have hb_sub : (0 : ℚ) < b - 1 := by linarith
  rw [div_le_div_iff₀ hb_sub ha_sub]
  nlinarith

/-- **Lemma 1.** For p ≥ 7 and v ≥ 2:
    p^{v+1}/(p^{v+1}-1) ≤ p³/(p³-1). -/
lemma cube_reciprocal_mono (p : ℕ) (hp : p ≥ 7) (v : ℕ) (hv : v ≥ 2) :
    (p ^ (v + 1) : ℚ) / (p ^ (v + 1) - 1) ≤ (p : ℚ) ^ 3 / ((p : ℚ) ^ 3 - 1) := by
  have hp3_gt1 : (1 : ℚ) < (p : ℚ) ^ 3 := by
    calc (1 : ℚ) < (7 : ℚ) ^ 3 := by norm_num
      _ ≤ (p : ℚ) ^ 3 := by
          apply pow_le_pow_left₀ (by norm_num : (0 : ℚ) ≤ 7)
          exact_mod_cast hp
  have h_le : (p : ℚ) ^ 3 ≤ (p : ℚ) ^ (v + 1) := by
    apply pow_le_pow_right₀
    · exact_mod_cast (show 1 ≤ p by omega)
    · omega
  exact div_pred_antitone' hp3_gt1 h_le

-- ════════════════════════════════════════════════════════════════════
-- Lemma 2: reciprocal_cube_comparison
-- ════════════════════════════════════════════════════════════════════

/-- **Lemma 2.** For p ≥ 2: 1/(p³-1) < 2/p³.
    Proof: p³ ≥ 8 > 2, so p³-1 > p³/2, hence 1/(p³-1) < 2/p³. -/
lemma reciprocal_cube_comparison (p : ℕ) (hp : p ≥ 2) :
    (1 : ℚ) / ((p : ℚ) ^ 3 - 1) < 2 / (p : ℚ) ^ 3 := by
  have hp_pos : (0 : ℚ) < (p : ℚ) := by exact_mod_cast (show 0 < p by omega)
  have hp3_pos : (0 : ℚ) < (p : ℚ) ^ 3 := pow_pos hp_pos 3
  have hp3_ge8 : (8 : ℚ) ≤ (p : ℚ) ^ 3 := by
    calc (8 : ℚ) = (2 : ℚ) ^ 3 := by norm_num
      _ ≤ (p : ℚ) ^ 3 := by
          apply pow_le_pow_left₀ (by norm_num : (0 : ℚ) ≤ 2)
          exact_mod_cast hp
  have h_denom_pos : (0 : ℚ) < (p : ℚ) ^ 3 - 1 := by linarith
  rw [div_lt_div_iff₀ h_denom_pos hp3_pos]
  -- Goal: 1 * p³ < 2 * (p³ - 1), i.e. p³ < 2p³ - 2, i.e. 2 < p³
  linarith

-- ════════════════════════════════════════════════════════════════════
-- Lemma 3: finset_sum_cube_reciprocal_bound
-- ════════════════════════════════════════════════════════════════════

/-- 1/n³ ≤ ½(1/(n-1)² - 1/n²) for n ≥ 2.
    Cross-multiply: need 2(n-1)² ≤ n(2n-1), i.e. 2 ≤ 3n. -/
private lemma inv_cube_le_half_telescope (n : ℕ) (hn : n ≥ 2) :
    (1 : ℚ) / (n : ℚ) ^ 3 ≤ (1 : ℚ) / 2 * (1 / ((n : ℚ) - 1) ^ 2 - 1 / (n : ℚ) ^ 2) := by
  have hn_pos : (0 : ℚ) < (n : ℚ) := by exact_mod_cast (show 0 < n by omega)
  have hn_sub : (0 : ℚ) < (n : ℚ) - 1 := by
    have : (1 : ℚ) < (n : ℚ) := by exact_mod_cast (show 1 < n by omega)
    linarith
  have hn3_pos : (0 : ℚ) < (n : ℚ) ^ 3 := pow_pos hn_pos 3
  have hn2_ne : (n : ℚ) ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos hn_pos)
  have hnsub2_ne : ((n : ℚ) - 1) ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos hn_sub)
  -- Reduce RHS to a single fraction
  have h_rhs : 1 / 2 * (1 / ((n : ℚ) - 1) ^ 2 - 1 / (n : ℚ) ^ 2) =
      (2 * (n : ℚ) - 1) / (2 * ((n : ℚ) - 1) ^ 2 * (n : ℚ) ^ 2) := by
    field_simp
    push_cast
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
  have hn_pos : (0 : ℚ) < (n : ℚ) := by exact_mod_cast (show 0 < n by omega)
  have hn_sub : (0 : ℚ) < (n : ℚ) - 1 := by
    have : (1 : ℚ) < (n : ℚ) := by exact_mod_cast (show 1 < n by omega)
    linarith
  rw [div_sub_div _ _ (ne_of_gt (sq_pos_of_pos hn_sub)) (ne_of_gt (sq_pos_of_pos hn_pos))]
  apply div_nonneg
  · nlinarith [sq_nonneg ((n : ℚ) - 1)]
  · exact mul_nonneg (le_of_lt (sq_pos_of_pos hn_sub)) (le_of_lt (sq_pos_of_pos hn_pos))

/-- Telescoping on Finset.range for squared reciprocals. -/
private lemma telescoping_sq_range (K : ℕ) (hK : K ≥ 2) (m : ℕ) :
    ∑ i ∈ Finset.range m, (1 / ((K : ℚ) - 1 + (i : ℚ)) ^ 2 - 1 / ((K : ℚ) + (i : ℚ)) ^ 2) =
    1 / ((K : ℚ) - 1) ^ 2 - 1 / ((K : ℚ) - 1 + (m : ℚ)) ^ 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    have h_eq : ((K : ℚ) + (m : ℚ)) ^ 2 = ((K : ℚ) - 1 + ((m : ℚ) + 1)) ^ 2 := by ring
    rw [h_eq]
    have h_succ : ((m : ℚ) + 1) = ((m + 1 : ℕ) : ℚ) := by push_cast; ring
    rw [h_succ]
    ring

/-- Telescoping sum of 1/(n-1)² - 1/n² over Finset.Icc K M. -/
private lemma telescoping_sq_inv_Icc (K M : ℕ) (hK : K ≥ 2) (hM : M ≥ K) :
    ∑ n ∈ Finset.Icc K M, (1 / ((n : ℚ) - 1) ^ 2 - 1 / (n : ℚ) ^ 2) =
    1 / ((K : ℚ) - 1) ^ 2 - 1 / (M : ℚ) ^ 2 := by
  rw [show Finset.Icc K M = (Finset.range (M - K + 1)).image (fun i => i + K) from by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · intro ⟨hx1, hx2⟩; exact ⟨x - K, by omega, by omega⟩
    · rintro ⟨i, hi, rfl⟩; exact ⟨by omega, by omega⟩]
  rw [Finset.sum_image (fun a _ b _ hab => by omega)]
  have h_eq : ∀ i ∈ Finset.range (M - K + 1),
      (1 / (((i + K : ℕ) : ℚ) - 1) ^ 2 - 1 / ((i + K : ℕ) : ℚ) ^ 2) =
      (1 / ((K : ℚ) - 1 + (i : ℚ)) ^ 2 - 1 / ((K : ℚ) + (i : ℚ)) ^ 2) := by
    intro i _
    congr 1
    · congr 1; push_cast; ring
    · congr 1; push_cast; ring
  rw [Finset.sum_congr rfl h_eq, telescoping_sq_range K hK (M - K + 1)]
  congr 1
  congr 1
  rw [Nat.cast_add, Nat.cast_one, Nat.cast_sub (by omega : K ≤ M)]
  ring

/-- **Lemma 3.** ∑_{n∈S} 1/n³ ≤ 1/72 for any finite set S of distinct naturals all ≥ 7. -/
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
  set M := S.max' hS_nonempty with hM_def
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
      ≤ 1 / 2 * ∑ n ∈ S, (1 / ((n : ℚ) - 1) ^ 2 - 1 / (n : ℚ) ^ 2) := by linarith
    _ ≤ 1 / 2 * (1 / 36) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        linarith
    _ = 1 / 72 := by norm_num

-- ════════════════════════════════════════════════════════════════════
-- Lemma 4: prod_one_plus_le_inv
-- ════════════════════════════════════════════════════════════════════

/-- **Lemma 4.** For xᵢ ≥ 0 with ∑ xᵢ < 1: ∏(1 + xᵢ) ≤ 1/(1 - ∑ xᵢ).
    Proof by Finset induction. Key step: x_{k+1} · S_k + x_{k+1}² ≥ 0. -/
lemma prod_one_plus_le_inv {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (x : ι → ℚ) (hx : ∀ i ∈ S, 0 ≤ x i)
    (hsum : ∑ i ∈ S, x i < 1) :
    ∏ i ∈ S, (1 + x i) ≤ 1 / (1 - ∑ i ∈ S, x i) := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a s' ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have hxa_nn : 0 ≤ x a := hx a (Finset.mem_insert_self a s')
    have hx' : ∀ i ∈ s', 0 ≤ x i :=
      fun i hi => hx i (Finset.mem_insert_of_mem hi)
    set S' := ∑ i ∈ s', x i
    have hS'_nn : 0 ≤ S' := Finset.sum_nonneg (fun i hi => hx' i hi)
    have hsum_eq : ∑ i ∈ insert a s', x i = x a + S' := Finset.sum_insert ha
    have h_sum' : S' < 1 := by linarith [hsum_eq ▸ hsum]
    have ih_applied := ih hx' h_sum'
    have h1_sub_S' : 0 < 1 - S' := by linarith
    have h1_sub_sum : 0 < 1 - (x a + S') := by linarith [hsum_eq ▸ hsum]
    have h1 : (1 + x a) * ∏ i ∈ s', (1 + x i) ≤ (1 + x a) * (1 / (1 - S')) :=
      mul_le_mul_of_nonneg_left ih_applied (by linarith)
    have h2 : (1 + x a) * (1 / (1 - S')) ≤ 1 / (1 - (x a + S')) := by
      rw [mul_one_div, div_le_div_iff₀ h1_sub_S' h1_sub_sum]
      nlinarith [mul_nonneg hxa_nn hS'_nn, sq_nonneg (x a)]
    linarith

-- ════════════════════════════════════════════════════════════════════
-- Lemma 5: Assembly — C < 36/35
-- ════════════════════════════════════════════════════════════════════

/-- **Lemma 5 (Assembly).** For any finite set S of primes ≥ 7:
    ∏_{p∈S} p³/(p³-1) < 36/35. -/
lemma cube_correction_factor_lt (S : Finset ℕ) (hS : ∀ p ∈ S, p ≥ 7) :
    ∏ p ∈ S, ((p : ℚ) ^ 3 / ((p : ℚ) ^ 3 - 1)) < 36 / 35 := by
  by_cases hS_empty : S = ∅
  · rw [hS_empty, Finset.prod_empty]; norm_num
  have h_rewrite : ∀ p ∈ S, (p : ℚ) ^ 3 / ((p : ℚ) ^ 3 - 1) = 1 + 1 / ((p : ℚ) ^ 3 - 1) := by
    intro p hp
    have hp3_gt1 : (1 : ℚ) < (p : ℚ) ^ 3 := by
      calc (1 : ℚ) < (7 : ℚ) ^ 3 := by norm_num
        _ ≤ (p : ℚ) ^ 3 := by
            apply pow_le_pow_left₀ (by norm_num : (0 : ℚ) ≤ 7)
            exact_mod_cast (hS p hp)
    have h_sub_pos : (0 : ℚ) < (p : ℚ) ^ 3 - 1 := by linarith
    field_simp
    ring
  rw [Finset.prod_congr rfl h_rewrite]
  -- Show ∑ 1/(p³-1) < 1/36
  have h_sum_bound : ∑ p ∈ S, (1 : ℚ) / ((p : ℚ) ^ 3 - 1) < 1 / 36 := by
    have h_each_le : ∀ p ∈ S, (1 : ℚ) / ((p : ℚ) ^ 3 - 1) ≤ 2 / (p : ℚ) ^ 3 :=
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
    linarith [h_factor]
  have h_sum_lt_1 : ∑ p ∈ S, (1 : ℚ) / ((p : ℚ) ^ 3 - 1) < 1 := by linarith
  have h_nn : ∀ p ∈ S, (0 : ℚ) ≤ 1 / ((p : ℚ) ^ 3 - 1) := by
    intro p hp
    apply div_nonneg (by norm_num : (0 : ℚ) ≤ 1)
    have hp3_gt1 : (1 : ℚ) < (p : ℚ) ^ 3 := by
      calc (1 : ℚ) < (7 : ℚ) ^ 3 := by norm_num
        _ ≤ (p : ℚ) ^ 3 := by
            apply pow_le_pow_left₀ (by norm_num : (0 : ℚ) ≤ 7)
            exact_mod_cast (hS p hp)
    linarith
  have h_prod := prod_one_plus_le_inv S (fun p => 1 / ((p : ℚ) ^ 3 - 1)) h_nn h_sum_lt_1
  have h_denom_gt : 35 / 36 < 1 - ∑ p ∈ S, (1 : ℚ) / ((p : ℚ) ^ 3 - 1) := by linarith
  have h_denom_pos : (0 : ℚ) < 1 - ∑ p ∈ S, (1 : ℚ) / ((p : ℚ) ^ 3 - 1) := by linarith
  have h_inv_lt : 1 / (1 - ∑ p ∈ S, (1 : ℚ) / ((p : ℚ) ^ 3 - 1)) < 36 / 35 := by
    rw [div_lt_div_iff₀ h_denom_pos (by norm_num : (0 : ℚ) < 35)]
    nlinarith
  linarith

/-- **Assembly corollary.** The correction factor ∏ p^{v+1}/(p^{v+1}-1) < 36/35
    for primes ≥ 7 with exponents ≥ 2. -/
lemma correction_factor_telescoping (S : Finset ℕ)
    (hS_ge7 : ∀ p ∈ S, p ≥ 7)
    (v : ℕ → ℕ) (hv : ∀ p ∈ S, v p ≥ 2) :
    ∏ p ∈ S, ((p ^ (v p + 1) : ℚ) / (p ^ (v p + 1) - 1)) < 36 / 35 := by
  have h_bound : ∏ p ∈ S, ((p ^ (v p + 1) : ℚ) / (p ^ (v p + 1) - 1)) ≤
      ∏ p ∈ S, ((p : ℚ) ^ 3 / ((p : ℚ) ^ 3 - 1)) := by
    apply Finset.prod_le_prod
    · intro p hp
      have hp_pos : (0 : ℚ) < (p : ℚ) := by exact_mod_cast (show (0 : ℕ) < p by
        have := hS_ge7 p hp; omega)
      have h_pow_pos : (0 : ℚ) < (p : ℚ) ^ (v p + 1) := pow_pos hp_pos _
      have h_pow_gt1 : (1 : ℚ) < (p : ℚ) ^ (v p + 1) := by
        have hp_gt1 : (1 : ℚ) < (p : ℚ) := by exact_mod_cast (show (1 : ℕ) < p by
          have := hS_ge7 p hp; omega)
        calc (1 : ℚ) < (p : ℚ) := hp_gt1
          _ = (p : ℚ) ^ 1 := (pow_one _).symm
          _ ≤ (p : ℚ) ^ (v p + 1) := by
              apply pow_le_pow_right₀
              · exact le_of_lt (by linarith)
              · omega
      exact le_of_lt (div_pos h_pow_pos (by linarith))
    · intro p hp
      exact cube_reciprocal_mono p (hS_ge7 p hp) (v p) (hv p hp)
  calc ∏ p ∈ S, ((p ^ (v p + 1) : ℚ) / (p ^ (v p + 1) - 1))
      ≤ ∏ p ∈ S, ((p : ℚ) ^ 3 / ((p : ℚ) ^ 3 - 1)) := h_bound
    _ < 36 / 35 := cube_correction_factor_lt S hS_ge7

end UALBF.Compute.CorrectionFactor
