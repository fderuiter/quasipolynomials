import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases
import UALBF.Basic

/-!
# SpecialFactors: The Prasad-Sunitha ω(N) ≥ 15 Bound (UALBF-301)

Proof that any Quasiperfect number N with gcd(N, 15) = 1 must have ω(N) ≥ 15.
-/

namespace UALBF.SpecialFactors

open Finset Nat

-- ════════════════════════════════════════════════════════════════════
-- § 0. Definitions & Computational Facts
-- ════════════════════════════════════════════════════════════════════

def cubeCPrimes : List ℕ :=
  [7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59]

private lemma length_eq : cubeCPrimes.length = 14 := rfl

def nthCubeCPrime (i : Fin 14) : ℕ :=
  cubeCPrimes.get (i.cast length_eq.symm)

def maxAbundancy (primes : List ℕ) : ℚ :=
  primes.foldl (fun acc p => acc * (p : ℚ) / ((p - 1) : ℚ)) 1

theorem abundancy_cube_c_lt_two : maxAbundancy cubeCPrimes < 2 := by
  unfold maxAbundancy cubeCPrimes List.foldl
  norm_num

-- ════════════════════════════════════════════════════════════════════
-- § 1. σ(N) > 2N for QPNs
-- ════════════════════════════════════════════════════════════════════

lemma qpn_sigma_gt_two_n {N : ℕ} (h : IsQuasiperfect N) :
    sigma N > 2 * N := by
  unfold IsQuasiperfect at h
  omega

-- ════════════════════════════════════════════════════════════════════
-- § 2. σ(N) · ∏(p-1) < N · ∏ p  (cross-multiplied abundancy bound)
-- ════════════════════════════════════════════════════════════════════

lemma sum_range_prime_pow_mul_pred {p e : ℕ} (hp : p.Prime) :
    (∑ k ∈ Finset.range (e + 1), p ^ k) * (p - 1) = p ^ (e + 1) - 1 := by
  have hp_pos : 0 < p := by have := hp.two_le; omega
  induction e with
  | zero => simp
  | succ e ih =>
    rw [Finset.sum_range_succ, add_mul, ih]
    have h1 : 1 ≤ p ^ (e + 1) := Nat.one_le_pow _ _ hp_pos
    have h2 : p ^ (e + 1) * p = p ^ (e + 1 + 1) := by ring
    have h3 : p ^ (e + 1) * (p - 1) = p ^ (e + 1 + 1) - p ^ (e + 1) := by
      calc p ^ (e + 1) * (p - 1)
        _ = p ^ (e + 1) * p - p ^ (e + 1) * 1 := Nat.mul_sub_left_distrib (p ^ (e + 1)) p 1
        _ = p ^ (e + 1 + 1) - p ^ (e + 1) := by rw [h2, mul_one]
    have h4 : p ^ (e + 1) ≤ p ^ (e + 1 + 1) := by
      rw [← h2]
      have step : p ^ (e + 1) * 1 ≤ p ^ (e + 1) * p := Nat.mul_le_mul_left _ (by omega)
      rwa [mul_one] at step
    -- Protect omega from non-linear exponent failures via abstract generalization
    generalize p ^ (e + 1) = A at h1 h3 h4 ⊢
    generalize p ^ (e + 1 + 1) = B at h3 h4 ⊢
    omega

lemma abundancy_cross_bound {N : ℕ} (hN : N > 1) :
    sigma N * ∏ p ∈ N.primeFactors, (p - 1) <
    N * ∏ p ∈ N.primeFactors, p := by
  have hN_ne : N ≠ 0 := by omega
  have h_supp : N.factorization.support = N.primeFactors := rfl
  have H_N_eq : N = ∏ p ∈ N.primeFactors, p ^ N.factorization p := by
    calc N = N.factorization.prod (fun p e => p ^ e) := (Nat.factorization_prod_pow_eq_self hN_ne).symm
      _ = ∏ p ∈ N.factorization.support, p ^ N.factorization p := rfl
      _ = ∏ p ∈ N.primeFactors, p ^ N.factorization p := by rw [h_supp]

  have h_sigma : sigma N = ∏ p ∈ N.primeFactors, ∑ k ∈ Finset.range (N.factorization p + 1), p ^ k := by
    unfold sigma
    rw [Nat.sum_divisors hN_ne]
    rfl

  have h1 : sigma N * ∏ p ∈ N.primeFactors, (p - 1) = ∏ p ∈ N.primeFactors, ((∑ k ∈ Finset.range (N.factorization p + 1), p ^ k) * (p - 1)) := by
    calc sigma N * ∏ p ∈ N.primeFactors, (p - 1)
      _ = (∏ p ∈ N.primeFactors, ∑ k ∈ Finset.range (N.factorization p + 1), p ^ k) * ∏ p ∈ N.primeFactors, (p - 1) := by rw [h_sigma]
      _ = ∏ p ∈ N.primeFactors, ((∑ k ∈ Finset.range (N.factorization p + 1), p ^ k) * (p - 1)) := Finset.prod_mul_distrib.symm

  have h2 : N * ∏ p ∈ N.primeFactors, p = ∏ p ∈ N.primeFactors, (p ^ N.factorization p * p) := by
    calc N * ∏ p ∈ N.primeFactors, p
      _ = (∏ p ∈ N.primeFactors, p ^ N.factorization p) * ∏ p ∈ N.primeFactors, p := by rw [H_N_eq]
      _ = ∏ p ∈ N.primeFactors, (p ^ N.factorization p * p) := Finset.prod_mul_distrib.symm

  rw [h1, h2]
  have hs_ne : N.primeFactors.Nonempty := Nat.primeFactors_nonempty.mpr (by omega)
  obtain ⟨p0, hp0⟩ := hs_ne

  apply Finset.prod_lt_prod
  · intro p _
    exact Nat.zero_le _
  · intro p hp
    have hp_prime := Nat.prime_of_mem_primeFactors hp
    have H : (∑ k ∈ Finset.range (N.factorization p + 1), p ^ k) * (p - 1) = p ^ (N.factorization p + 1) - 1 := sum_range_prime_pow_mul_pred hp_prime
    rw [H]
    have H2 : p ^ N.factorization p * p = p ^ (N.factorization p + 1) := by ring
    rw [H2]
    have h_pos : 1 ≤ p ^ (N.factorization p + 1) := Nat.one_le_pow _ _ (by have := hp_prime.two_le; omega)
    generalize p ^ (N.factorization p + 1) = A at h_pos ⊢
    omega
  · use p0, hp0
    have hp_prime := Nat.prime_of_mem_primeFactors hp0
    have hv_pos : 1 ≤ N.factorization p0 := by rwa [Nat.Prime.one_le_factorization_iff hp_prime hN_ne] at hp0
    have H : (∑ k ∈ Finset.range (N.factorization p0 + 1), p0 ^ k) * (p0 - 1) = p0 ^ (N.factorization p0 + 1) - 1 := sum_range_prime_pow_mul_pred hp_prime
    rw [H]
    have H2 : p0 ^ N.factorization p0 * p0 = p0 ^ (N.factorization p0 + 1) := by ring
    rw [H2]
    have h_pos : 1 ≤ p0 ^ (N.factorization p0 + 1) := Nat.one_le_pow _ _ (by have := hp_prime.two_le; omega)
    generalize p0 ^ (N.factorization p0 + 1) = A at h_pos ⊢
    omega

-- ════════════════════════════════════════════════════════════════════
-- § 3. Prime Pool: gcd(N,15) = 1 ∧ QPN ⟹ all prime factors ≥ 7
-- ════════════════════════════════════════════════════════════════════

lemma coprime_15_not_dvd_3 {N : ℕ} (h : N.gcd 15 = 1) : ¬ (3 ∣ N) := by
  intro h3; have H : 3 ∣ N.gcd 15 := Nat.dvd_gcd h3 (by norm_num)
  rw [h] at H; revert H; norm_num

lemma coprime_15_not_dvd_5 {N : ℕ} (h : N.gcd 15 = 1) : ¬ (5 ∣ N) := by
  intro h5; have H : 5 ∣ N.gcd 15 := Nat.dvd_gcd h5 (by norm_num)
  rw [h] at H; revert H; norm_num

lemma qpn_coprime_15_primes_ge_7 {N : ℕ} (h_qpn : IsQuasiperfect N)
    (h_coprime : N.gcd 15 = 1) (p : ℕ) (hp : p ∈ N.primeFactors) :
    p ≥ 7 := by
  have hp_prime := Nat.prime_of_mem_primeFactors hp
  have hp_dvd := Nat.dvd_of_mem_primeFactors hp
  have hp_ne_2 : p ≠ 2 := by
    rintro rfl
    have ⟨h_odd, _⟩ := qpn_is_odd_square h_qpn
    unfold Odd at h_odd
    obtain ⟨k, _⟩ := h_odd
    obtain ⟨m, _⟩ := hp_dvd
    omega
  have hp_ne_3 : p ≠ 3 := by
    intro heq; subst heq; exact coprime_15_not_dvd_3 h_coprime hp_dvd
  have hp_ne_5 : p ≠ 5 := by
    intro heq; subst heq; exact coprime_15_not_dvd_5 h_coprime hp_dvd

  by_contra h_lt
  push_neg at h_lt
  have hp_cases : p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6 := by
    have : 2 ≤ p := hp_prime.two_le
    omega
  rcases hp_cases with rfl | rfl | rfl | rfl | rfl
  · exact hp_ne_2 rfl
  · exact hp_ne_3 rfl
  · revert hp_prime; decide
  · exact hp_ne_5 rfl
  · revert hp_prime; decide

-- ════════════════════════════════════════════════════════════════════
-- § 4. The Squeeze: ∏ p/(p-1) ≤ maxAbundancy cubeCPrimes < 2
-- ════════════════════════════════════════════════════════════════════

/-! ### 4a. Anti-monotonicity of Euler factors -/

private lemma cross_antitone {a b : ℕ} (ha : a ≥ 2) (hab : a ≤ b) :
    b * (a - 1) ≤ a * (b - 1) := by
  have h1 : b * (a - 1) = b * a - b := by
    calc b * (a - 1) = b * a - b * 1 := Nat.mul_sub_left_distrib b a 1
      _ = b * a - b := by rw [mul_one]
  have h2 : a * (b - 1) = a * b - a := by
    calc a * (b - 1) = a * b - a * 1 := Nat.mul_sub_left_distrib a b 1
      _ = a * b - a := by rw [mul_one]
  have h3 : b * a = a * b := mul_comm b a
  omega

/-! ### 4b. Pigeonhole: cubeCPrimes are the first 14 primes ≥ 7 -/

private theorem cubeCPrimes_minimal (i : Fin 14) :
    (Finset.filter Nat.Prime (Finset.Ico 7 (nthCubeCPrime i))).card = i.val := by
  revert i; decide

/-! ### 4c. Cross-multiplied cubeCPrimes bound for truncated prefixes -/

private theorem cubec_take_cross_bound (k : ℕ) (hk : k ≤ 14) :
    (cubeCPrimes.take k).prod ≤ 2 * ((cubeCPrimes.take k).map (· - 1)).prod := by
  have hk0 : 0 ≤ k := by omega
  interval_cases k <;> decide

/-! ### 4d. Explicit Bounds Bridging -/

private lemma cube_take_get (k : ℕ) (hk : k ≤ 14) :
    ∀ i : Fin (cubeCPrimes.take k).length,
    (cubeCPrimes.take k).get i = nthCubeCPrime ⟨i.val, by omega⟩ := by
  revert hk
  interval_cases k <;> (intro _ i; revert i; decide)

/-! ### 4e. Anti-monotone list product comparison -/

private lemma list_cross_antitone :
    ∀ (L₁ L₂ : List ℕ) (h_len : L₁.length = L₂.length),
      (∀ i : Fin L₁.length, L₁.get i ≤ L₂.get ⟨i.val, by omega⟩) →
      (∀ i : Fin L₁.length, L₁.get i ≥ 2) →
      L₂.prod * (L₁.map (· - 1)).prod ≤
      L₁.prod * (L₂.map (· - 1)).prod := by
  intro L₁
  induction L₁ with
  | nil =>
    intro L₂ h_len h_le h_ge
    cases L₂
    · simp
    · contradiction
  | cons a₁ tl₁ ih =>
    intro L₂ h_len h_le h_ge
    cases L₂ with
    | nil => contradiction
    | cons a₂ tl₂ =>
      simp only [List.prod_cons, List.map_cons]
      have h_len_tl : tl₁.length = tl₂.length := by change tl₁.length + 1 = tl₂.length + 1 at h_len; omega
      have ha_le : a₁ ≤ a₂ := h_le ⟨0, by omega⟩
      have ha_ge : a₁ ≥ 2 := h_ge ⟨0, by omega⟩
      have h_cross := cross_antitone ha_ge ha_le
      have ih_tl := ih tl₂ h_len_tl
        (fun ⟨i, hi⟩ => h_le ⟨i + 1, by omega⟩)
        (fun ⟨i, hi⟩ => h_ge ⟨i + 1, by omega⟩)
      have h_bound := Nat.mul_le_mul h_cross ih_tl
      calc (a₂ * tl₂.prod) * ((a₁ - 1) * (tl₁.map (· - 1)).prod)
        _ = (a₂ * (a₁ - 1)) * (tl₂.prod * (tl₁.map (· - 1)).prod) := by ring
        _ ≤ (a₁ * (a₂ - 1)) * (tl₁.prod * (tl₂.map (· - 1)).prod) := h_bound
        _ = (a₁ * tl₁.prod) * ((a₂ - 1) * (tl₂.map (· - 1)).prod) := by ring

/-! ### 4f. Pigeonhole on sorted lists -/

private lemma sorted_ge_cubec (l : List ℕ) (h_sorted : l.Pairwise (· < ·))
    (h_ge7 : ∀ x ∈ l, x ≥ 7) (h_prime : ∀ x ∈ l, Nat.Prime x)
    (h_nodup : l.Nodup) (h_len : l.length ≤ 14) (i : Fin l.length) :
    l.get i ≥ nthCubeCPrime ⟨i.val, by omega⟩ := by
  by_contra h_lt; push_neg at h_lt
  have hi_bound : i.val < 14 := by omega
  let idx : Fin 14 := ⟨i.val, hi_bound⟩
  set ci := nthCubeCPrime idx
  have h_count : (Finset.filter Nat.Prime (Finset.Ico 7 ci)).card = i.val :=
    cubeCPrimes_minimal idx
  suffices i.val + 1 ≤ (Finset.filter Nat.Prime (Finset.Ico 7 ci)).card by omega
  have h_sub : (Finset.image (fun (j : Fin (i.val + 1)) =>
      l.get ⟨j.val, by omega⟩) Finset.univ) ⊆
      (Finset.filter Nat.Prime (Finset.Ico 7 ci)) := by
    intro x hx
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨j, rfl⟩ := hx
    simp only [Finset.mem_filter, Finset.mem_Ico]
    have hj_mem : l.get ⟨j.val, by omega⟩ ∈ l := List.mem_iff_get.mpr ⟨⟨j.val, by omega⟩, rfl⟩
    refine ⟨⟨h_ge7 _ hj_mem, ?_⟩, h_prime _ hj_mem⟩
    calc l.get ⟨j.val, by omega⟩
        ≤ l.get i := by
          rcases eq_or_lt_of_le (show j.val ≤ i.val by omega) with h_eq | h_lt_j
          · apply le_of_eq; congr 1; exact Fin.ext h_eq
          · apply le_of_lt
            have h_lt_fin : (⟨j.val, by omega⟩ : Fin l.length) < i := h_lt_j
            exact List.pairwise_iff_get.mp h_sorted ⟨j.val, by omega⟩ i h_lt_fin
      _ < ci := h_lt
  calc i.val + 1
      = (Finset.univ : Finset (Fin (i.val + 1))).card := by simp
    _ = (Finset.image (fun j : Fin (i.val + 1) => l.get ⟨j.val, by omega⟩) Finset.univ).card := by
        symm
        have h_inj : Function.Injective (fun j : Fin (i.val + 1) => l.get ⟨j.val, by omega⟩) := by
          intro a b hab
          have h_eq_fin : (⟨a.val, by omega⟩ : Fin l.length) = ⟨b.val, by omega⟩ :=
            (List.Nodup.get_inj_iff h_nodup).mp hab
          have h_val : a.val = b.val := congrArg (fun (x : Fin l.length) => x.val) h_eq_fin
          exact Fin.ext h_val
        rw [Finset.card_image_of_injective Finset.univ h_inj]
    _ ≤ (Finset.filter Nat.Prime (Finset.Ico 7 ci)).card := Finset.card_le_card h_sub

/-! ### 4g. Sorted list cross bound (main squeeze on lists) -/

private lemma list_prod_pos {L : List ℕ} (h : ∀ x ∈ L, 0 < x) : 0 < L.prod := by
  induction L with
  | nil => decide
  | cons a L' ih =>
    have ha : 0 < a := h a (by simp)
    have hL' : 0 < L'.prod := ih (fun x hx => h x (by simp [hx]))
    exact Nat.mul_pos ha hL'

private lemma sorted_list_cross_bound (l : List ℕ) (h_sorted : l.Pairwise (· < ·))
    (h_ge7 : ∀ x ∈ l, x ≥ 7) (h_prime : ∀ x ∈ l, Nat.Prime x)
    (h_nodup : l.Nodup) (h_len : l.length ≤ 14) :
    l.prod ≤ 2 * (l.map (· - 1)).prod := by
  let k := l.length
  let C := cubeCPrimes.take k
  have hC_len : C.length = k := by
    dsimp [C, k]
    rw [List.length_take, length_eq]
    exact Nat.min_eq_left h_len

  have h_ew : ∀ i : Fin C.length, C.get i ≤ l.get ⟨i.val, by omega⟩ := by
    intro i
    have hi_l : i.val < l.length := by omega
    have hC_get : C.get i = cube_take_get k h_len i
    rw [hC_get]
    exact sorted_ge_cubec l h_sorted h_ge7 h_prime h_nodup h_len ⟨i.val, hi_l⟩

  have hC_ge2 : ∀ i : Fin C.length, C.get i ≥ 2 := by
    intro i
    have hC_get : C.get i = cube_take_get k h_len i
    rw [hC_get]
    have H : ∀ j : Fin 14, nthCubeCPrime j ≥ 2 := by decide
    exact H ⟨i.val, by omega⟩

  have h_anti := list_cross_antitone C l (by omega) h_ew hC_ge2
  have h_cubec := cubec_take_cross_bound k h_len

  have hC_pred_pos : 0 < (C.map (· - 1)).prod := by
    dsimp [C, k]
    have hk_le : l.length ≤ 14 := h_len
    generalize l.length = len at hk_le ⊢
    interval_cases len <;> decide

  have h_chain2 : l.prod * (C.map (· - 1)).prod ≤ 2 * (l.map (· - 1)).prod * (C.map (· - 1)).prod := by
    calc l.prod * (C.map (· - 1)).prod
      _ ≤ C.prod * (l.map (· - 1)).prod := h_anti
      _ ≤ (2 * (C.map (· - 1)).prod) * (l.map (· - 1)).prod := Nat.mul_le_mul_right _ h_cubec
      _ = 2 * (l.map (· - 1)).prod * (C.map (· - 1)).prod := by ring

  exact Nat.le_of_mul_le_mul_right h_chain2 hC_pred_pos

/-! ### 4h. Finset version (bridge from sorted list) -/

lemma finset_euler_bound (S : Finset ℕ)
    (h_prime : ∀ p ∈ S, Nat.Prime p) (h_ge7 : ∀ p ∈ S, p ≥ 7)
    (h_card : S.card ≤ 14) :
    ∏ p ∈ S, p ≤ 2 * ∏ p ∈ S, (p - 1) := by
  let l := S.sort (· ≤ ·)
  have h_val : (l : Multiset ℕ) = S.val := by
    first
    | exact (Finset.sort_val (· ≤ ·) S).symm
    | exact (Finset.sort_val (· ≤ ·)).symm

  have h_nodup : l.Nodup := by
    have H : (l : Multiset ℕ).Nodup := by
      rw [h_val]
      exact S.nodup
    exact H

  have h_sorted_le : l.Pairwise (· ≤ ·) := by
    first
    | exact Finset.sort_sorted (· ≤ ·) S
    | exact Finset.sort_sorted (· ≤ ·)
    | exact Finset.pairwise_sort (· ≤ ·) S
    | exact Finset.pairwise_sort (· ≤ ·)

  have h_sorted : l.Pairwise (· < ·) := by
    rw [List.pairwise_iff_get]
    intro i j hij
    have h_le := List.pairwise_iff_get.mp h_sorted_le i j hij
    have h_neq : l.get i ≠ l.get j := by
      intro heq
      have hab2 : (⟨i.val, i.isLt⟩ : Fin l.length) = ⟨j.val, j.isLt⟩ :=
        (List.Nodup.get_inj_iff h_nodup).mp heq
      have h_val_eq : i.val = j.val := by
        calc i.val = (⟨i.val, i.isLt⟩ : Fin l.length).val := rfl
          _ = (⟨j.val, j.isLt⟩ : Fin l.length).val := by rw [hab2]
          _ = j.val := rfl
      omega
    omega

  have h_len : l.length ≤ 14 := by
    have h_len_eq : l.length = Multiset.card (l : Multiset ℕ) := rfl
    have h_card_eq : Multiset.card (l : Multiset ℕ) = Multiset.card S.val := by rw [h_val]
    have h_S_card : Multiset.card S.val = S.card := rfl
    omega

  have h_ge7_l : ∀ x ∈ l, x ≥ 7 := by
    intro x hx
    have H_mem : x ∈ (l : Multiset ℕ) := hx
    rw [h_val] at H_mem
    exact h_ge7 x H_mem

  have h_prime_l : ∀ x ∈ l, Nat.Prime x := by
    intro x hx
    have H_mem : x ∈ (l : Multiset ℕ) := hx
    rw [h_val] at H_mem
    exact h_prime x H_mem

  have h_list_bound := sorted_list_cross_bound l h_sorted h_ge7_l h_prime_l h_nodup h_len

  have h_prod_eq : ∏ p ∈ S, p = l.prod := by
    have H1 : ∏ p ∈ S, p = Multiset.prod (Multiset.map (fun x => x) S.val) := rfl
    rw [H1, ← h_val]
    change (l.map (fun x => x)).prod = l.prod
    have h_map : l.map (fun x => x) = l := by
      induction l with
      | nil => rfl
      | cons hd tl ih => simp [ih]
    rw [h_map]

  have h_prod_pred_eq : ∏ p ∈ S, (p - 1) = (l.map (· - 1)).prod := by
    have H1 : ∏ p ∈ S, (p - 1) = Multiset.prod (Multiset.map (fun x => x - 1) S.val) := rfl
    rw [H1, ← h_val]
    change (l.map (fun x => x - 1)).prod = (l.map (· - 1)).prod
    rfl

  rw [h_prod_eq, h_prod_pred_eq]
  exact h_list_bound

-- ════════════════════════════════════════════════════════════════════
-- § 5. The Main Theorem
-- ════════════════════════════════════════════════════════════════════

theorem qpn_coprime_15_omega_15 {N : ℕ} (h_qpn : IsQuasiperfect N)
    (h_coprime : N.gcd 15 = 1) :
    N.primeFactors.card ≥ 15 := by
  by_contra h_not; push_neg at h_not
  have h_card : N.primeFactors.card ≤ 14 := by omega
  have h_sigma_gt := qpn_sigma_gt_two_n h_qpn
  have hN_gt1 : N > 1 := by
    by_contra hle; push_neg at hle
    have hp_cases : N = 0 ∨ N = 1 := by omega
    rcases hp_cases with rfl | rfl
    · have h_eq : IsQuasiperfect 0 := h_qpn
      unfold IsQuasiperfect sigma at h_eq
      revert h_eq; decide
    · have h_eq : IsQuasiperfect 1 := h_qpn
      unfold IsQuasiperfect sigma at h_eq
      revert h_eq; decide

  have h_cross := abundancy_cross_bound hN_gt1
  have h_prod_pred_pos : 0 < ∏ p ∈ N.primeFactors, (p - 1) := by
    apply Finset.prod_pos
    intro p hp; have := (Nat.prime_of_mem_primeFactors hp).two_le; omega

  have h_ineq1 : 2 * N * ∏ p ∈ N.primeFactors, (p - 1) < sigma N * ∏ p ∈ N.primeFactors, (p - 1) :=
    Nat.mul_lt_mul_of_pos_right h_sigma_gt h_prod_pred_pos

  have h_ineq2 : 2 * N * ∏ p ∈ N.primeFactors, (p - 1) < N * ∏ p ∈ N.primeFactors, p :=
    lt_trans h_ineq1 h_cross

  have h_ineq : 2 * ∏ p ∈ N.primeFactors, (p - 1) < ∏ p ∈ N.primeFactors, p := by
    have h_cancel : N * (2 * ∏ p ∈ N.primeFactors, (p - 1)) < N * ∏ p ∈ N.primeFactors, p := by
      calc N * (2 * ∏ p ∈ N.primeFactors, (p - 1))
        _ = 2 * N * ∏ p ∈ N.primeFactors, (p - 1) := by ring
        _ < N * ∏ p ∈ N.primeFactors, p := h_ineq2
    exact Nat.lt_of_mul_lt_mul_left h_cancel

  have h_ge7 := qpn_coprime_15_primes_ge_7 h_qpn h_coprime
  have h_prime : ∀ p ∈ N.primeFactors, p.Prime :=
    fun p hp => Nat.prime_of_mem_primeFactors hp
  have h_opposite := finset_euler_bound N.primeFactors h_prime h_ge7 h_card

  omega

end UALBF.SpecialFactors
