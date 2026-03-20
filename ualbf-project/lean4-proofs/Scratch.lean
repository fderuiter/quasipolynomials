import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Data.Nat.GCD.Basic

open Finset
open Nat

lemma odd_coprime_two {d : ℕ} (h : Odd d) : Coprime d 2 := by
  apply?

lemma odd_coprime_two_pow {d k : ℕ} (h : Odd d) : Coprime d (2^k) := by
  apply?

lemma odd_dvd_of_odd_dvd_mul_two_pow {d m k : ℕ} (hd_odd : Odd d) (h_dvd : d ∣ 2^k * m) : d ∣ m := by
  apply?
