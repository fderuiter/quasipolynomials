import Mathlib.NumberTheory.Divisors

open Finset
open Nat

lemma odd_card_divisors_iff_square {n : ℕ} (hn : n > 0) : 
  Odd n.divisors.card ↔ ∃ m, n = m ^ 2 := by
  apply?

lemma filter_odd_divisors {n : ℕ} (m : ℕ) (h1 : Odd m) (h2 : ∃ k, n = 2^k * m) : 
  (n.divisors.filter Odd).card = m.divisors.card := by
  sorry
