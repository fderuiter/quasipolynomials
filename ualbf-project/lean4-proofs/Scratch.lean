import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Parity

open Nat

lemma odd_iff_coprime_two (d : ℕ) : Odd d ↔ Coprime d 2 := by
  apply?
