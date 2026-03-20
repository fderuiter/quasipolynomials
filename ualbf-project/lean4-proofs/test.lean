import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Data.Nat.Parity
import Mathlib

open Finset
open Nat

lemma odd_card_divisors_iff (n : ℕ) (hn : n ≠ 0) : 
  Odd n.divisors.card ↔ ∃ m, n = m ^ 2 := by
  apply?

lemma odd_card_divisors_iff2 (n : ℕ) (hn : n ≠ 0) : 
  Odd n.divisors.card ↔ IsSquare n := by
  apply?
