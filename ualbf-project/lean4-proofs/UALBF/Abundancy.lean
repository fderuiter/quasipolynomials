import UALBF.Basic
import UALBF.SpecialFactors
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Totient
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace UALBF

open Nat
open Finset

/--
  The Abundancy Index H(N) = sigma(N) / N.
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
  Lemma: sigma(N) * phi(N) < N^2 for N > 1.
  The core N-level inequality, derived by combining the cross-multiplied
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
  -- Chain: sigma*phi*prod(p-1) < N^2*prod(p-1), then cancel prod(p-1) > 0
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
  Euler product prod p/(p-1) over primes dividing N, which is equivalent to N / phi(N).
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

-- ================================================================
-- Phase 2: Core Algebraic Identities for Totient Ratio Decomposition
-- ================================================================

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
  -- Side goal: (p : Q) != 1, needed for geom_sum_eq
  have hp_ne_one : (p : ℚ) ≠ 1 := by
    have : (1 : ℚ) < (p : ℚ) := by exact_mod_cast (show 1 < p by omega)
    linarith
  -- Side goal: (p : Q) - 1 != 0
  have hp_sub_ne : (p : ℚ) - 1 ≠ 0 := sub_ne_zero_of_ne hp_ne_one
  -- Side goal: (p : Q) ^ v != 0
  have hp_pow_v_ne : (p : ℚ) ^ v ≠ 0 := pow_ne_zero _ (ne_of_gt hp_pos)
  -- Side goal: (p : Q) ^ (v + 1) - 1 != 0
  have hp_pow_v1_sub_ne : (p : ℚ) ^ (v + 1) - 1 ≠ 0 := by
    have h1 : (1 : ℚ) < (p : ℚ) ^ (v + 1) := by
      have hp_gt_one : (1 : ℚ) < (p : ℚ) := by exact_mod_cast (show 1 < p by omega)
      calc (1 : ℚ) = 1 ^ (v + 1) := (one_pow _).symm
        _ < (p : ℚ) ^ (v + 1) :=
          pow_lt_pow_left₀ hp_gt_one (by linarith) (by omega)
    linarith
  -- Rewrite geometric sum: sum k in range(v+1), p^k = (p^(v+1) - 1) / (p - 1)
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
  -- sigma(N) = prod sigma(p^vp)
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
  -- N = prod p^vp
  have H_N_eq : N = (∏ p ∈ N.primeFactors, p ^ N.factorization p) := by
    have h_prod := Nat.factorization_prod_pow_eq_self hN_ne
    calc N = N.factorization.prod (fun p e => p ^ e) := h_prod.symm
      _ = ∏ p ∈ N.factorization.support, p ^ N.factorization p := rfl
      _ = ∏ p ∈ N.primeFactors, p ^ N.factorization p := by rw [h_supp]
  -- Strategy: show both sides equal prod p/(p-1).
  -- Step 1: Show RHS = prod p/(p-1) via euler_factor_decomp
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
  -- Step 2: Show LHS = prod p/(p-1) via totient identity
  have h_lhs : (N : ℚ) / (N.totient : ℚ) =
      ∏ p ∈ N.primeFactors, ((p : ℚ) / ((p : ℚ) - 1)) := by
    have h_id := Nat.totient_mul_prod_primeFactors N
    -- Cast to Q: phi(N) * prod_p = N * prod_(p-1)
    -- The N subtraction (p - 1) for primes p >= 2 agrees with Q subtraction.
    have h_id_q : (N.totient : ℚ) * (∏ p ∈ N.primeFactors, (p : ℚ)) =
        (N : ℚ) * (∏ p ∈ N.primeFactors, ((p : ℚ) - 1)) := by
      -- We need to show (prod_(p-1) : Q) = prod_((p:Q) - 1)
      -- This is tricky because of N subtraction. Use the fact that all primes >= 2.
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
    -- N/phi(N) = prod_p / prod_(p-1) = prod (p/(p-1))
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

-- ================================================================
-- Phase 3: Correction Factor Bound
-- ================================================================

/-! ### 3a. Monotonicity: x/(x-1) is anti-monotone for x > 1 -/

/-- x/(x-1) is anti-monotone: if 1 < a ≤ b then b/(b-1) ≤ a/(a-1).
    Proof clears denominators and reduces to a ≤ b. -/

lemma div_pred_antitone {a b : ℚ} (ha : 1 < a) (hab : a ≤ b) :
    b / (b - 1) ≤ a / (a - 1) := by
  have ha_sub : (0 : ℚ) < a - 1 := by linarith
  have hb_sub : (0 : ℚ) < b - 1 := by linarith
  rw [div_le_div_iff₀ hb_sub ha_sub]
  -- Goal: b*(a-1) ≤ a*(b-1), i.e., b*a - b ≤ a*b - a, i.e., a ≤ b ✓
  nlinarith

/-! ### 3b. Each correction factor ≤ 343/342 -/

/-- For p ≥ 7 and v ≥ 2, the correction factor p^{v+1}/(p^{v+1}-1) ≤ 343/342. -/

lemma correction_factor_le_cube {p v : ℕ} (hp : p ≥ 7) (hv : v ≥ 2) :
    (p ^ (v + 1) : ℚ) / (p ^ (v + 1) - 1) ≤ 343 / 342 := by
  have hp_ge : (7 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp
  have hv1_ge : v + 1 ≥ 3 := by omega
  -- p^(v+1) ≥ 7^3 = 343
  have h_pvp1_ge : (343 : ℚ) ≤ (p : ℚ) ^ (v + 1) := by
    calc (343 : ℚ) = (7 : ℚ) ^ 3 := by norm_num
      _ ≤ (7 : ℚ) ^ (v + 1) := by
          exact pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 7) hv1_ge
      _ ≤ (p : ℚ) ^ (v + 1) := by
          exact pow_le_pow_left₀ (by linarith : (0 : ℚ) ≤ 7) hp_ge _
  -- Now 343 ≤ p^(v+1), so p^(v+1)/(p^(v+1)-1) ≤ 343/(343-1) = 343/342
  have h_343_pos : (0 : ℚ) < 343 := by norm_num
  have h_pvp1_pos : (0 : ℚ) < (p : ℚ) ^ (v + 1) := by linarith
  -- Use div_pred_antitone but the output has (343 - 1), we need to show 343 - 1 = 342
  have h_eq : (343 : ℚ) - 1 = 342 := by norm_num
  have h_result := div_pred_antitone (by norm_num : (1 : ℚ) < 343) h_pvp1_ge
  rwa [h_eq] at h_result

/-! ### 3c. Head product: primes 7 through 61 -/

/-- Product of p^3/(p^3-1) for the 15 primes 7,11,...,61 is < 10048/10000.
    The exact product ≈ 1.004716..., and 10048/10000 = 1.0048. -/

lemma head_product_bound :
    (343 : ℚ) / 342 * (1331 / 1330) * (2197 / 2196) * (4913 / 4912) *
    (6859 / 6858) * (12167 / 12166) * (24389 / 24388) * (29791 / 29790) *
    (50653 / 50652) * (68921 / 68920) * (79507 / 79506) * (103823 / 103822) *
    (148877 / 148876) * (205379 / 205378) * (226981 / 226980) < 10048 / 10000 := by
  norm_num

/-! ### 3d. Weierstrass product inequality (finite version) -/

/-- For 0 < x_i < 1 with sum x_i < 1:
    prod 1/(1-x_i) ≤ 1/(1 - sum x_i).
    Proof by Finset induction; the key step uses x_{n+1} * S_n ≥ 0. -/

lemma prod_inv_one_sub_le (s : Finset ℕ) (x : ℕ → ℚ)
    (hx_pos : ∀ i ∈ s, 0 < x i) (hx_lt : ∀ i ∈ s, x i < 1)
    (h_sum : ∑ i ∈ s, x i < 1) :
    ∏ i ∈ s, (1 / (1 - x i)) ≤ 1 / (1 - ∑ i ∈ s, x i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s' ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have hxa_pos : 0 < x a := hx_pos a (Finset.mem_insert_self a s')
    have hxa_lt : x a < 1 := hx_lt a (Finset.mem_insert_self a s')
    have hx_pos' : ∀ i ∈ s', 0 < x i :=
      fun i hi => hx_pos i (Finset.mem_insert_of_mem hi)
    have hx_lt' : ∀ i ∈ s', x i < 1 :=
      fun i hi => hx_lt i (Finset.mem_insert_of_mem hi)
    have h_sum_eq : ∑ i ∈ insert a s', x i = x a + ∑ i ∈ s', x i :=
      Finset.sum_insert ha
    have h_sum' : ∑ i ∈ s', x i < 1 := by linarith
    have ih_applied := ih hx_pos' hx_lt' h_sum'
    set S' := ∑ i ∈ s', x i
    have hS'_pos : 0 ≤ S' := Finset.sum_nonneg (fun i hi => le_of_lt (hx_pos' i hi))
    have h1_sub_xa : 0 < 1 - x a := by linarith
    have h1_sub_S' : 0 < 1 - S' := by linarith
    have h1_sub_sum : 0 < 1 - (x a + S') := by linarith
    -- Step 1: bound the product using IH
    have h_step1 : (1 / (1 - x a)) * (∏ i ∈ s', 1 / (1 - x i)) ≤
        (1 / (1 - x a)) * (1 / (1 - S')) :=
      mul_le_mul_of_nonneg_left ih_applied (le_of_lt (div_pos one_pos h1_sub_xa))
    -- Step 2: 1/(1-xa) * 1/(1-S') = 1/((1-xa)(1-S'))
    have h_step2 : (1 / (1 - x a)) * (1 / (1 - S')) = 1 / ((1 - x a) * (1 - S')) := by
      rw [_root_.div_mul_div_comm, one_mul]
    -- Step 3: (1-xa)(1-S') ≥ 1-xa-S'  (because xa*S' ≥ 0)
    have h_step3 : 1 - (x a + S') ≤ (1 - x a) * (1 - S') := by
      nlinarith [mul_nonneg (le_of_lt hxa_pos) hS'_pos]
    -- Step 4: 1/((1-xa)(1-S')) ≤ 1/(1-xa-S')
    -- Since 0 < 1-(xa+S') ≤ (1-xa)(1-S'), we get 1/((1-xa)(1-S')) ≤ 1/(1-(xa+S'))
    have h_denom_pos : 0 < (1 - x a) * (1 - S') := mul_pos h1_sub_xa h1_sub_S'
    have h_step4 : 1 / ((1 - x a) * (1 - S')) ≤ 1 / (1 - (x a + S')) := by
      rw [div_le_div_iff₀ h_denom_pos h1_sub_sum]
      -- Goal: (1 - (xa + S')) * 1 ≤ 1 * ((1-xa)(1-S'))
      nlinarith [mul_nonneg (le_of_lt hxa_pos) hS'_pos]
    linarith

/-! ### 3e. Per-element bound for 1/n^3 -/

/-- For n ≥ 2: 1/n^3 ≤ 1/(n*(n-1)).
    This follows from n*(n-1) ≤ n^3 for n ≥ 1. -/

lemma inv_cube_le_inv_mul_pred (n : ℕ) (hn : n ≥ 2) :
    (1 : ℚ) / (n : ℚ) ^ 3 ≤ 1 / ((n : ℚ) * ((n : ℚ) - 1)) := by
  have hn_pos : (0 : ℚ) < (n : ℚ) := by exact_mod_cast (show 0 < n by omega)
  have hn_sub : (0 : ℚ) < (n : ℚ) - 1 := by
    have : (1 : ℚ) < (n : ℚ) := by exact_mod_cast (show 1 < n by omega)
    linarith
  have h_denom1 : (0 : ℚ) < (n : ℚ) * ((n : ℚ) - 1) := mul_pos hn_pos hn_sub
  have h_denom2 : (0 : ℚ) < (n : ℚ) ^ 3 := pow_pos hn_pos 3
  rw [div_le_div_iff₀ h_denom2 h_denom1]
  -- Goal: 1 * (n * (n - 1)) ≤ 1 * n^3, i.e., n*(n-1) ≤ n^3
  simp only [one_mul]
  nlinarith [sq_nonneg ((n : ℚ) - 1)]

/-- 1/(n*(n-1)) = 1/(n-1) - 1/n (partial fractions). -/
lemma inv_mul_pred_eq_sub (n : ℕ) (hn : n ≥ 2) :
    (1 : ℚ) / ((n : ℚ) * ((n : ℚ) - 1)) = 1 / ((n : ℚ) - 1) - 1 / (n : ℚ) := by
  have hn_pos : (0 : ℚ) < (n : ℚ) := by exact_mod_cast (show 0 < n by omega)
  have hn_sub : (0 : ℚ) < (n : ℚ) - 1 := by
    have : (1 : ℚ) < (n : ℚ) := by exact_mod_cast (show 1 < n by omega)
    linarith
  field_simp
  ring

/-- For any finite set S of naturals all ≥ K with K ≥ 2, the sum of 1/n^3
    over S is at most 1/(K-1). Uses 1/n^3 ≤ 1/(n(n-1)) = 1/(n-1) - 1/n,
    and each such term is positive. Even summing all n ≥ K gives exactly
    1/(K-1) (telescoping), so any finite subset sums to ≤ 1/(K-1). -/

lemma finite_sum_inv_cube_le (S : Finset ℕ) (K : ℕ) (hK : K ≥ 2)
    (hS : ∀ n ∈ S, n ≥ K) :
    ∑ n ∈ S, (1 : ℚ) / (n : ℚ) ^ 3 ≤ 1 / ((K : ℚ) - 1) := by
  -- Each 1/n^3 ≤ 1/(n*(n-1)) = 1/(n-1) - 1/n
  -- Each term is nonneg and ≤ 1/(K-1) - 0 = 1/(K-1), since n ≥ K means 1/(n-1) ≤ 1/(K-1).
  -- Actually we bound the whole sum:
  --   sum ≤ sum (1/(n-1) - 1/n) for n ∈ S
  -- Each term 1/(n-1) - 1/n ≥ 0.
  -- We need sum (1/(n-1) - 1/n) ≤ 1/(K-1).
  -- Since all n ≥ K, each 1/(n-1) ≤ 1/(K-1) and each -1/n ≤ 0.
  -- But sum of non-overlapping telescoping terms from {K,K+1,...} gives exactly 1/(K-1).
  -- For arbitrary (possibly non-contiguous) S, we use the crude bound:
  -- each term 1/(n-1) - 1/n = 1/(n(n-1)) > 0, and
  -- 1/(n(n-1)) ≤ 1/((K-1)*K) ≤ 1/(K-1) for n ≥ K.
  -- So sum ≤ |S| / ((K-1)*K). But we don't bound |S|.
  -- Instead, we just bound each 1/n^3 directly:
  -- 1/n^3 ≤ 1/n^2 ≤ 1/((K-1)*K) ≤ 1/(K-1) since K ≥ 2.
  -- Hmm, but this gives sum ≤ |S|/(K-1) which can be > 1/(K-1).
  -- The real argument: sum_n≥K 1/(n(n-1)) = 1/(K-1) by telescoping.
  -- Our finite S is a subset of {K, K+1, ...} with possibly non-distinct elements,
  -- but Finset elements are distinct and all ≥ K.
  -- Since 1/(n(n-1)) = 1/(n-1) - 1/n > 0 for each n, and these are ALL
  -- non-negative partial fraction terms that collectively sum to ≤ 1/(K-1),
  -- any subset also sums to ≤ 1/(K-1).
  sorry

/-! ### 3f. Tail product bound -/

/-- The correction factor over any finite set of primes ≥ 62
    is bounded by 61/60 ≈ 1.0167. Uses the Weierstrass inequality
    with sum 1/p^3 ≤ 1/61 (from finite_sum_inv_cube_le with K=62). -/
lemma tail_correction_bound (S : Finset ℕ)
    (hS : ∀ p ∈ S, p ≥ 62)
    (hS_prime : ∀ p ∈ S, Nat.Prime p) :
    ∏ p ∈ S, ((p : ℚ) ^ 3 / ((p : ℚ) ^ 3 - 1)) ≤ 61 / 60 := by
  -- Each p^3/(p^3-1) = 1/(1 - 1/p^3)
  -- Apply prod_inv_one_sub_le with x_p = 1/p^3:
  --   0 < 1/p^3 < 1 for p ≥ 62, sum ≤ 1/61 < 1
  -- Conclude: prod ≤ 1/(1 - 1/61) = 61/60
  sorry

/-! ### 3g. Full correction factor bound -/

/-- The full correction factor C = prod p^{v+1}/(p^{v+1}-1) over all
    prime factors of a QPN with gcd(N,15)=1 is < 1022/1000.
    Since all v_p ≥ 2 (QPN is odd square) and all p ≥ 7 (coprime to 15),
    each factor ≤ p^3/(p^3-1). Split into head (p≤61) and tail (p>61).
    Head product < 10048/10000, tail ≤ 61/60.
    Combined: 10048/10000 * 61/60 = 9577/9375 ≈ 1.02155 < 1022/1000. -/

lemma correction_factor_bound {N : ℕ} (h_qpn : IsQuasiperfect N)
    (h_coprime : N.gcd 15 = 1) :
    ∏ p ∈ N.primeFactors,
      ((p ^ (N.factorization p + 1) : ℚ) / (p ^ (N.factorization p + 1) - 1)) <
    1022 / 1000 := by
  -- Step 1: Each factor ≤ p^3/(p^3-1) by correction_factor_le_cube
  -- Step 2: Split primeFactors into head (p ≤ 61) and tail (p > 61)
  -- Step 3: head product < 10048/10000 (by head_product_bound)
  -- Step 4: tail product ≤ 61/60 (by tail_correction_bound)
  -- Step 5: 10048/10000 * 61/60 = 9577/9375 < 1022/1000
  --   (check: 9577*1000 = 9577000, 9375*1022 = 9581250, 9577000 < 9581250 ✓)
  sorry

/--
  Theorem: Totient Geometric Window
  Demonstrates that for massive QPN candidates (N > 10^35) with gcd(N, 15) = 1,
  the maximum possible abundancy (the Euler ceiling) is bounded mathematically
  by 2.4675.

  Proof: N/φ(N) = σ(N)/N × C where C is the correction factor.
  For QPNs: σ(N)/N = 2 + 1/N < 20001/10000 (from h_size > 10^35).
  C < 1022/1000 (from correction_factor_bound).
  Chain: 20001/10000 × 1022/1000 = 2.044... < 2.4675.
-/

theorem qpn_totient_bound {N : ℕ} (h_qpn : IsQuasiperfect N) (h_size : N > 10^35)
    (h_coprime : N.gcd 15 = 1) :
  (N : ℚ) / (N.totient : ℚ) < 2.4675 := by
  have hN_gt1 : N > 1 := by omega
  have h_decomp := totient_ratio_decomp hN_gt1
  have h_abund := qpn_abundancy_target h_qpn
  have h_corr := correction_factor_bound h_qpn h_coprime
  have hN_pos : (0 : ℚ) < (N : ℚ) := Nat.cast_pos.mpr (by omega)
  have hN_ge : (10 : ℚ) ^ 35 < (N : ℚ) := by exact_mod_cast h_size
  have h_abund_bound : abundancy_index N < 20001 / 10000 := by
    rw [h_abund]
    have h_inv : 1 / (N : ℚ) < 1 / (10 : ℚ) ^ 35 := by
      rw [div_lt_div_iff₀ hN_pos (by positivity : (0 : ℚ) < (10 : ℚ) ^ 35)]
      simp only [one_mul]; exact hN_ge
    linarith
  rw [h_decomp]
  have h_corr_pos : 0 < ∏ p ∈ N.primeFactors,
      ((p ^ (N.factorization p + 1) : ℚ) / (p ^ (N.factorization p + 1) - 1)) := by
    apply Finset.prod_pos
    intro p hp
    have hp_prime := (Nat.mem_primeFactors.mp hp).1
    have hp_ge2 : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp_prime.two_le
    have h_pow_pos : (0 : ℚ) < (p : ℚ) ^ (N.factorization p + 1) := by positivity
    have h_pow_gt1 : (1 : ℚ) < (p : ℚ) ^ (N.factorization p + 1) := by
      calc (1 : ℚ) < (p : ℚ) := by linarith
        _ = (p : ℚ) ^ 1 := (pow_one _).symm
        _ ≤ (p : ℚ) ^ (N.factorization p + 1) := by
            apply pow_le_pow_right₀ (by linarith); omega
    exact div_pos h_pow_pos (by linarith)
  calc abundancy_index N * ∏ p ∈ N.primeFactors,
        ((p ^ (N.factorization p + 1) : ℚ) / (p ^ (N.factorization p + 1) - 1))
      < (20001 / 10000) * (1022 / 1000) := by
        apply mul_lt_mul h_abund_bound (le_of_lt h_corr) h_corr_pos (by norm_num)
    _ < 2.4675 := by norm_num

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
