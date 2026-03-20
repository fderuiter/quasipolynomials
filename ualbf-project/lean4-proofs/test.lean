import Mathlib.NumberTheory.Divisors
import Mathlib

open Nat

lemma my_lemma1 (n : ℕ) : Odd n.divisors.card ↔ ∃ m, n = m ^ 2 := by
  apply?

lemma my_lemma2 (n : ℕ) : Odd (∑ d ∈ n.divisors, d) ↔ (∃ m : ℕ, n = m ^ 2) ∨ (∃ m : ℕ, n = 2 * m ^ 2) := by
  apply?
