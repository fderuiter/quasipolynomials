import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Data.Nat.Parity
import Mathlib

open Finset
open Nat

lemma odd_divisors_eq_odd_part_divisors {n m k : ℕ} (h0 : n ≠ 0) (h : n = 2^k * m) (hm : Odd m) : 
  n.divisors.filter Odd = m.divisors := by
  ext d
  simp only [mem_filter, mem_divisors, ne_eq, h0, not_false_eq_true, and_true]
  constructor
  · rintro ⟨⟨c, rfl⟩, hd⟩
    have hm0 : m ≠ 0 := by rintro rfl; simp at hm
    refine ⟨?_, hm0⟩
    -- d * c = 2^k * m
    apply?
  · rintro ⟨⟨c, rfl⟩, hm0⟩
    -- d * c = m
    apply?
