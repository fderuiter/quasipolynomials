import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import UALBF.Basic

/-!
# SpecialFactors: The Prasad-Sunitha ω(N) ≥ 15 Bound (UALBF-301)

Proof that any Quasiperfect number N with gcd(N, 15) = 1 must have ω(N) ≥ 15.

## Proof Architecture

By contradiction: assume ω(N) ≤ 14.

1. **QPN bound**: σ(N) = 2N + 1 > 2N.
2. **Abundancy bound**: σ(N) · ∏(p-1) < N · ∏ p. (Multiplicativity of σ.)
3. Combining: 2·∏(p-1) < ∏ p.
4. **Squeeze**: For ≤ 14 primes ≥ 7, ∏ p/(p-1) ≤ maxAbundancy cubeCPrimes < 2.
   Equivalently in ℕ: ∏ p ≤ 2·∏(p-1). Contradiction with step 3.

The squeeze is proven via:
- Pigeonhole: the i-th smallest prime ≥ 7 in any set ≥ cubeCPrimes[i].
- Anti-monotonicity of p/(p-1): larger primes contribute less.
- Element-wise comparison ⟹ product comparison ≤ cubeCPrimes product < 2.
-/

namespace UALBF.SpecialFactors

open Finset Nat

-- ════════════════════════════════════════════════════════════════════
-- § 0. Definitions & Computational Facts
-- ════════════════════════════════════════════════════════════════════

def cubeCPrimes : List ℕ :=
  [7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59]

def maxAbundancy (primes : List ℕ) : ℚ :=
  primes.foldl (fun acc p => acc * (p : ℚ) / ((p - 1) : ℚ)) 1

theorem abundancy_cube_c_lt_two : maxAbundancy cubeCPrimes < 2 := by
  native_decide

-- ════════════════════════════════════════════════════════════════════
-- § 1. σ(N) > 2N for QPNs
-- ════════════════════════════════════════════════════════════════════

lemma qpn_sigma_gt_two_n {N : ℕ} (h : IsQuasiperfect N) :
    sigma N > 2 * N := by
  have := h.2; omega

-- ════════════════════════════════════════════════════════════════════
-- § 2. σ(N) · ∏(p-1) < N · ∏ p  (cross-multiplied abundancy bound)
-- ════════════════════════════════════════════════════════════════════

lemma sigma_prime_pow_mul_pred {p e : ℕ} (hp : p.Prime) :
    sigma (p ^ e) * (p - 1) = p ^ (e + 1) - 1 := by
  unfold sigma; rw [Nat.sum_divisors_prime_pow hp]
  have hp_ge : p ≥ 2 := hp.two_le
  induction e with
  | zero => simp; omega
  | succ e ih =>
    rw [sum_range_succ, add_mul, ih]
    have : p ^ (e + 1) ≥ 1 := Nat.one_le_pow' e (p - 1)
    have : p ^ (e + 1 + 1) = p * p ^ (e + 1) := by ring
    rw [this]; omega

lemma abundancy_cross_bound {N : ℕ} (hN : N > 1) :
    sigma N * ∏ p ∈ N.primeFactors, (p - 1) <
    N * ∏ p ∈ N.primeFactors, p := by
  have hN_ne : N ≠ 0 := by omega
  unfold sigma; rw [Nat.sum_divisors hN_ne, ← Finset.prod_mul_distrib]
  rw [(Nat.factorization_prod_pow_eq_self hN_ne).symm, ← Finset.prod_mul_distrib]
  apply Finset.prod_lt_prod_of_nonempty
  · exact Nat.primeFactors_nonempty.mpr (by omega)
  · intro p hp
    have hp_prime := Nat.prime_of_mem_primeFactors hp
    have hv_pos : N.factorization p ≥ 1 := by
      rwa [Nat.Prime.one_le_factorization_iff hp_prime hN_ne] at hp
    have h_geom : ∑ k ∈ Finset.range (N.factorization p + 1), p ^ k =
        sigma (p ^ N.factorization p) := by
      unfold sigma; rw [Nat.sum_divisors_prime_pow hp_prime]
    rw [h_geom, sigma_prime_pow_mul_pred hp_prime]
    have : p ^ N.factorization p * p = p ^ (N.factorization p + 1) := by ring
    rw [this]
    have : p ^ (N.factorization p + 1) ≥ 1 :=
      Nat.one_le_pow' (N.factorization p) (p - 1)
    omega

-- ════════════════════════════════════════════════════════════════════
-- § 3. Prime Pool: gcd(N,15) = 1 ∧ QPN ⟹ all prime factors ≥ 7
-- ════════════════════════════════════════════════════════════════════

lemma coprime_15_not_dvd_3 {N : ℕ} (h : N.gcd 15 = 1) : ¬ (3 ∣ N) := by
  intro h3; have : 3 ∣ N.gcd 15 := Nat.dvd_gcd h3 (by norm_num); omega

lemma coprime_15_not_dvd_5 {N : ℕ} (h : N.gcd 15 = 1) : ¬ (5 ∣ N) := by
  intro h5; have : 5 ∣ N.gcd 15 := Nat.dvd_gcd h5 (by norm_num); omega

lemma qpn_coprime_15_primes_ge_7 {N : ℕ} (h_qpn : IsQuasiperfect N)
    (h_coprime : N.gcd 15 = 1) (p : ℕ) (hp : p ∈ N.primeFactors) :
    p ≥ 7 := by
  have hp_prime := Nat.prime_of_mem_primeFactors hp
  have hp_dvd := Nat.dvd_of_mem_primeFactors hp
  have ⟨h_odd, _⟩ := qpn_is_odd_square h_qpn
  have hp_ne_2 : p ≠ 2 := by
    intro heq; subst heq
    exact (Nat.odd_iff.mp h_odd).2 (even_iff_two_dvd.mpr hp_dvd)
  have hp_ne_3 : p ≠ 3 := by
    intro heq; subst heq; exact coprime_15_not_dvd_3 h_coprime hp_dvd
  have hp_ne_5 : p ≠ 5 := by
    intro heq; subst heq; exact coprime_15_not_dvd_5 h_coprime hp_dvd
  interval_cases p <;> simp_all

-- ════════════════════════════════════════════════════════════════════
-- § 4. The Squeeze: ∏ p/(p-1) ≤ maxAbundancy cubeCPrimes < 2
-- ════════════════════════════════════════════════════════════════════

/-! ### 4a. Anti-monotonicity of Euler factors -/

private lemma cross_antitone {a b : ℕ} (ha : a ≥ 2) (hab : a ≤ b) :
    b * (a - 1) ≤ a * (b - 1) := by nlinarith

/-! ### 4b. Pigeonhole: cubeCPrimes are the first 14 primes ≥ 7 -/

private theorem cubeCPrimes_length : cubeCPrimes.length = 14 := by native_decide

private theorem cubeCPrimes_minimal (i : Fin 14) :
    (Finset.Ico 7 (cubeCPrimes.get ⟨i.val, by simp [cubeCPrimes]; omega⟩)
      |>.filter Nat.Prime).card = i.val := by native_decide

/-! ### 4c. Cross-multiplied cubeCPrimes bound for truncated prefixes -/

private theorem cubec_take_cross_bound (k : ℕ) (hk : k ≤ 14) :
    (cubeCPrimes.take k).prod ≤ 2 * ((cubeCPrimes.take k).map (· - 1)).prod := by
  interval_cases k <;> native_decide

/-! ### 4d. Anti-monotone list product comparison -/

private lemma list_cross_antitone :
    ∀ (L₁ L₂ : List ℕ),
      L₁.length = L₂.length →
      (∀ i : Fin L₁.length, L₁.get i ≤ L₂.get i) →
      (∀ i : Fin L₁.length, L₁.get i ≥ 2) →
      L₂.prod * (L₁.map (· - 1)).prod ≤
      L₁.prod * (L₂.map (· - 1)).prod := by
  intro L₁ L₂ h_len h_le h_ge
  induction L₁ with
  | nil =>
    have : L₂ = [] := List.length_eq_zero.mp h_len.symm; subst this; simp
  | cons a₁ tl₁ ih =>
    match L₂, h_len with
    | a₂ :: tl₂, h_len =>
      simp only [List.prod_cons, List.map_cons, List.length_cons] at *
      have ha_le : a₁ ≤ a₂ := by have := h_le ⟨0, by simp⟩; simp at this; exact this
      have ha_ge : a₁ ≥ 2 := by have := h_ge ⟨0, by simp⟩; simp at this; exact this
      have h_cross := cross_antitone ha_ge ha_le
      have ih_tl := ih tl₂ (by omega)
        (fun ⟨i, hi⟩ => by have := h_le ⟨i + 1, by omega⟩; simp at this; exact this)
        (fun ⟨i, hi⟩ => by have := h_ge ⟨i + 1, by omega⟩; simp at this; exact this)
      nlinarith [
        Nat.zero_le (tl₂.prod * (tl₁.map (· - 1)).prod),
        Nat.zero_le (tl₁.prod * (tl₂.map (· - 1)).prod)]

/-! ### 4e. Pigeonhole on sorted lists -/

private lemma sorted_ge_cubec (l : List ℕ) (h_sorted : l.Sorted (· < ·))
    (h_ge7 : ∀ x ∈ l, x ≥ 7) (h_prime : ∀ x ∈ l, x.Prime)
    (h_nodup : l.Nodup) (h_len : l.length ≤ 14) (i : Fin l.length) :
    l.get i ≥ cubeCPrimes.get ⟨i.val, by rw [cubeCPrimes_length]; omega⟩ := by
  by_contra h_lt; push_neg at h_lt
  set ci := cubeCPrimes.get ⟨i.val, by rw [cubeCPrimes_length]; omega⟩
  have h_count := cubeCPrimes_minimal ⟨i.val, by omega⟩
  suffices i.val + 1 ≤ (Finset.Ico 7 ci |>.filter Nat.Prime).card by omega
  have h_sub : (Finset.image (fun (j : Fin (i.val + 1)) =>
      l.get ⟨j.val, by omega⟩) Finset.univ) ⊆
      (Finset.Ico 7 ci |>.filter Nat.Prime) := by
    intro x hx
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨j, rfl⟩ := hx
    simp only [Finset.mem_filter, Finset.mem_Ico]
    refine ⟨⟨h_ge7 _ (List.get_mem l j.val (by omega)), ?_⟩,
            h_prime _ (List.get_mem l j.val (by omega))⟩
    calc l.get ⟨j.val, by omega⟩
        ≤ l.get i := by
          rcases eq_or_lt_of_le (show j.val ≤ i.val by omega) with h_eq | h_lt_j
          · exact le_of_eq (by congr 1; exact Fin.ext h_eq)
          · exact le_of_lt (List.Sorted.get_strictMono h_sorted
              (Fin.mk_lt_mk.mpr h_lt_j))
      _ < ci := h_lt
  calc i.val + 1
      = (Finset.univ : Finset (Fin (i.val + 1))).card := by simp
    _ = (Finset.image (fun j : Fin (i.val + 1) => l.get ⟨j.val, by omega⟩)
          Finset.univ).card := by
        rw [Finset.card_image_of_injective]; intro a b hab; simp at hab
        exact Fin.ext ((List.Nodup.get_inj_iff h_nodup
          ⟨a.val, by omega⟩ ⟨b.val, by omega⟩).mp hab)
    _ ≤ (Finset.Ico 7 ci |>.filter Nat.Prime).card := Finset.card_le_card h_sub

/-! ### 4f. Sorted list cross bound (main squeeze on lists) -/

private lemma sorted_list_cross_bound (l : List ℕ) (h_sorted : l.Sorted (· < ·))
    (h_ge7 : ∀ x ∈ l, x ≥ 7) (h_prime : ∀ x ∈ l, x.Prime)
    (h_nodup : l.Nodup) (h_len : l.length ≤ 14) :
    l.prod ≤ 2 * (l.map (· - 1)).prod := by
  set k := l.length
  set C := cubeCPrimes.take k
  have hC_len : C.length = k := by
    simp [C]; exact Nat.min_eq_left (by rw [cubeCPrimes_length]; omega)
  -- Element-wise: C[i] ≤ l[i]
  have h_ew : ∀ i : Fin C.length, C.get i ≤
      l.get ⟨i.val, by rw [← hC_len]; exact i.isLt⟩ := by
    intro ⟨i, hi⟩; rw [hC_len] at hi
    simp only [C, List.get_take']
    exact sorted_ge_cubec l h_sorted h_ge7 h_prime h_nodup h_len ⟨i, hi⟩
  -- C elements ≥ 2
  have hC_ge2 : ∀ i : Fin C.length, C.get i ≥ 2 := by
    intro ⟨i, hi⟩; simp only [C, List.get_take']
    rw [hC_len] at hi
    have hmem : cubeCPrimes.get ⟨i, by rw [cubeCPrimes_length]; omega⟩ ∈ cubeCPrimes :=
      List.get_mem cubeCPrimes i (by rw [cubeCPrimes_length]; omega)
    have := (by decide : ∀ p ∈ cubeCPrimes, p ≥ 7) _ hmem; omega
  -- Anti-monotone product
  have h_anti := list_cross_antitone C l hC_len h_ew hC_ge2
  -- cubec_take bound
  have h_cubec := cubec_take_cross_bound k h_len
  -- Positive products
  have hC_pred_pos : (C.map (· - 1)).prod > 0 := by
    apply List.prod_pos; intro x hx
    simp [List.mem_map] at hx; obtain ⟨p, hp_mem, rfl⟩ := hx
    have : p ∈ cubeCPrimes := List.mem_of_mem_take hp_mem
    have := (by decide : ∀ p ∈ cubeCPrimes, p ≥ 7) _ this; omega
  have hl_pred_pos : (l.map (· - 1)).prod > 0 := by
    apply List.prod_pos; intro x hx
    simp [List.mem_map] at hx; obtain ⟨p, hp_mem, rfl⟩ := hx
    have := h_ge7 p hp_mem; omega
  -- Chain: l.prod · C_pred.prod ≤ C.prod · l_pred.prod ≤ 2 · C_pred.prod · l_pred.prod
  nlinarith

/-! ### 4g. Finset version (bridge from sorted list) -/

lemma finset_euler_bound (S : Finset ℕ)
    (h_prime : ∀ p ∈ S, p.Prime) (h_ge7 : ∀ p ∈ S, p ≥ 7)
    (h_card : S.card ≤ 14) :
    ∏ p ∈ S, p ≤ 2 * ∏ p ∈ S, (p - 1) := by
  -- 1. Convert the Finset to a sorted List
  let l := S.sort (· < ·)
  
  -- 2. Extract the properties of the sorted list
  have h_sorted : l.Sorted (· < ·) := Finset.sort_sorted (· < ·) S
  have h_nodup : l.Nodup := Finset.sort_nodup (· < ·) S
  have h_len : l.length ≤ 14 := by 
    rw [Finset.length_sort]
    exact h_card
    
  have h_ge7_l : ∀ x ∈ l, x ≥ 7 := by
    intro x hx
    rw [Finset.mem_sort (· < ·)] at hx
    exact h_ge7 x hx
    
  have h_prime_l : ∀ x ∈ l, x.Prime := by
    intro x hx
    rw [Finset.mem_sort (· < ·)] at hx
    exact h_prime x hx

  -- 3. Apply your main list bound
  have h_list_bound := sorted_list_cross_bound l h_sorted h_ge7_l h_prime_l h_nodup h_len
  
  -- 4. Rewrite the Finset products to List products
  have h_prod_eq : ∏ p ∈ S, p = l.prod := by
    exact (Finset.prod_sort (· < ·) S id).symm
    
  have h_prod_pred_eq : ∏ p ∈ S, (p - 1) = (l.map (· - 1)).prod := by
    rw [← List.prod_map]
    exact (Finset.prod_sort (· < ·) S (· - 1)).symm

  -- 5. Substitute and conclude
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
    by_contra hle; have : N ≤ 1 := by omega
    interval_cases N
    · omega
    · unfold sigma at h_sigma_gt; simp at h_sigma_gt
  have h_cross := abundancy_cross_bound hN_gt1
  have h_prod_pred_pos : ∏ p ∈ N.primeFactors, (p - 1) > 0 := by
    apply Finset.prod_pos
    intro p hp; have := (Nat.prime_of_mem_primeFactors hp).two_le; omega
  -- From σ(N) > 2N and σ(N)·∏(p-1) < N·∏p:
  have h_ineq : 2 * ∏ p ∈ N.primeFactors, (p - 1) <
      ∏ p ∈ N.primeFactors, p := by nlinarith
  -- But squeeze gives: ∏p ≤ 2·∏(p-1)
  have h_ge7 := qpn_coprime_15_primes_ge_7 h_qpn h_coprime
  have h_prime : ∀ p ∈ N.primeFactors, p.Prime :=
    fun p hp => Nat.prime_of_mem_primeFactors hp
  have h_opposite := finset_euler_bound N.primeFactors h_prime h_ge7 h_card
  omega

end UALBF.SpecialFactors
