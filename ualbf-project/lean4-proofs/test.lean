import Mathlib.NumberTheory.Divisors

open Finset
open Nat

noncomputable def sigma (n : ℕ) : ℕ :=
  ∑ d ∈ n.divisors, d

lemma odd_sigma_iff_odd_card_odd_divisors (n : ℕ) : 
  Odd (sigma n) ↔ Odd (n.divisors.filter Odd).card := by
  unfold sigma
  rw [Nat.odd_sum_iff]

lemma odd_sigma_iff_square_or_double_square (n : ℕ) : 
  Odd (sigma n) ↔ (∃ m : ℕ, n = m ^ 2) ∨ (∃ m : ℕ, n = 2 * m ^ 2) := by
  sorry
