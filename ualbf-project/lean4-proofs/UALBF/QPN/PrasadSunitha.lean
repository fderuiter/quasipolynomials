import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.IntervalCases
import UALBF.QPN.BasicProperties


/-!
# Prasad-Sunitha Bound: ω(N) ≥ 14

Proof that any quasiperfect number N with gcd(N, 15) = 1 must have at least
14 distinct factors. Uses a cross-multiplied abundancy bound combined
with a pigeonhole squeeze against the first 13 odd factors ≥ 7.
-/

namespace UALBF.QPN.PrasadSunitha

open UALBF UALBF.QPN.BasicProperties

open Finset Nat

/-! ### Definitions and Computational Facts -/

def cubeCNumbers : List ℕ :=
  [7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 49]

private lemma length_eq : cubeCNumbers.length = 13 := rfl

def nthCubeCNumber (i : Fin 13) : ℕ :=
  cubeCNumbers.get (i.cast length_eq.symm)


/-! ### σ(N) > 2N for QPNs -/

lemma qpn_sigma_gt_two_n {N : ℕ} (h : IsQuasiperfect N) :
    sigma N > 2 * N := sorry

/-! ### Cross-Multiplied Abundancy Bound -/

/-- Geometric sum times `(p - 1)` in the Nat-subtraction form `= p^(e+1) - 1`.
    Thin wrapper around Mathlib's `geom_sum_mul_of_one_le`; kept because
    `abundancy_cross_bound` rewrites with this RHS shape. -/
lemma sum_range_prime_pow_mul_pred {p e : ℕ} (hp : p.Prime) :
    (∑ k ∈ Finset.range (e + 1), p ^ k) * (p - 1) = p ^ (e + 1) - 1 :=
  geom_sum_mul_of_one_le (by have := hp.two_le; omega) (e + 1)

lemma abundancy_cross_bound {N : ℕ} (hN : N > 1) :
    (sigma N * ∏ p ∈ N.primeFactors, (p - 1)) <
    (N * ∏ p ∈ N.primeFactors, p) := sorry

/-! ### Prime Pool: gcd(N,15) = 1 Implies All Primes ≥ 7 -/

lemma coprime_15_not_dvd_3 {N : ℕ}  : ¬ (3 ∣ N) := sorry

lemma coprime_15_not_dvd_5 {N : ℕ}  : ¬ (5 ∣ N) := sorry

lemma qpn_coprime_15_primes_ge_7 {N : ℕ} (h_qpn : IsQuasiperfect N)
     (p : ℕ) (hp : p ∈ N.primeFactors) :
    p ≥ 7 := sorry

/-! ### The Euler Factor Squeeze -/

/-! #### Anti-Monotonicity of Euler Factors -/

private lemma cross_antitone {a b : ℕ} (_ha : a ≥ 2) (hab : a ≤ b) :
    b * (a - 1) ≤ a * (b - 1) := sorry

/-! #### Pigeonhole: First 13 Factors ≥ 7 -/

private theorem cubeCNumbers_minimal (i : Fin 13) :
    (Finset.filter (fun x => x % 2 = 1 ∧ x % 3 ≠ 0 ∧ x % 5 ≠ 0) (Finset.Ico 7 (nthCubeCNumber i))).card = i.val := sorry

/-! #### Cross-Multiplied Bound for Truncated Prefixes -/

private theorem cubec_take_cross_bound (k : ℕ) (hk : k ≤ 13) :
    (cubeCNumbers.take k).prod ≤ 2 * ((cubeCNumbers.take k).map (fun x => x - 1)).prod := sorry

/-! #### Explicit Bounds Bridging -/

private lemma cube_take_get (k : ℕ) (hk : k ≤ 13)
    (i : Fin (cubeCNumbers.take k).length)
    (hi : i.val < 13) :
    (cubeCNumbers.take k).get i = nthCubeCNumber (Fin.mk i.val hi) := sorry

/-! #### Anti-Monotone List Product Comparison -/

private lemma list_cross_antitone :
    ∀ (L₁ L₂ : List ℕ) (h_len : L₁.length = L₂.length),
      (∀ i : Fin L₁.length, L₁.get i ≤ L₂.get (Fin.mk i.val (by omega))) →
      (∀ i : Fin L₁.length, L₁.get i ≥ 2) →
      L₂.prod * (L₁.map (fun x => x - 1)).prod ≤
      L₁.prod * (L₂.map (fun x => x - 1)).prod := sorry

/-! #### Pigeonhole on Sorted Prime Lists -/

private lemma sorted_ge_cubec (l : List ℕ) (h_sorted : l.Pairwise (· < ·))
    (h_ge7 : ∀ x ∈ l, x ≥ 7) (h_prime : ∀ x ∈ l, x % 2 = 1 ∧ x % 3 ≠ 0 ∧ x % 5 ≠ 0)
    (h_nodup : l.Nodup) (h_len : l.length ≤ 13) (i : Fin l.length) :
    l.get i ≥ nthCubeCNumber (Fin.mk i.val (by omega)) := sorry

/-! #### Sorted List Cross Bound -/

private lemma list_prod_pos {L : List ℕ} (h : ∀ x ∈ L, 0 < x) : 0 < L.prod := sorry

private lemma sorted_list_cross_bound (l : List ℕ) (h_sorted : l.Pairwise (· < ·))
    (h_ge7 : ∀ x ∈ l, x ≥ 7) (h_prime : ∀ x ∈ l, x % 2 = 1 ∧ x % 3 ≠ 0 ∧ x % 5 ≠ 0)
    (h_nodup : l.Nodup) (h_len : l.length ≤ 13) :
    l.prod ≤ 2 * (l.map (fun x => x - 1)).prod := sorry

/-! #### Finset Bridge from Sorted Lists -/

lemma finset_euler_bound (S : Finset ℕ)
    (h_prime : ∀ p ∈ S, p % 2 = 1 ∧ p % 3 ≠ 0 ∧ p % 5 ≠ 0) (h_ge7 : ∀ p ∈ S, p ≥ 7)
    (h_card : S.card ≤ 13) :
    (∏ p ∈ S, p) ≤ 2 * (∏ p ∈ S, (p - 1)) := sorry

/-! ### Main Theorem: ω(N) ≥ 14 -/

theorem qpn_coprime_15_omega_14 {N : ℕ} (h_qpn : IsQuasiperfect N)
     :
    N.primeFactors.card ≥ 14 := sorry

end UALBF.QPN.PrasadSunitha
