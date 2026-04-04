import Mathlib.Data.Nat.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Rat.Defs

/-!
# UALBF Core Definitions

Foundational definitions shared across all layers of the proof library:
`sigma`, `IsQuasiperfect`, `abundancy_index`, `ExactValuation`, and
the `Bipartition` structure used by the Rust search engine.
-/

namespace UALBF

open Finset
open Nat

/-- The sum of divisors function σ(n). -/
noncomputable def sigma (n : ℕ) : ℕ :=
  ∑ d ∈ n.divisors, d

/-- A number is quasiperfect if σ(n) = 2n + 1. -/
def IsQuasiperfect (n : ℕ) : Prop :=
  n > 0 ∧ sigma n = 2 * n + 1

/--
  The Abundancy Index H(N) = sigma(N) / N.
  For quasiperfect numbers, this will be strictly > 2, approaching 2 from above.
-/
noncomputable def abundancy_index (n : ℕ) : ℚ :=
  (sigma n : ℚ) / (n : ℚ)

/--
  Definition of Exact Valuation (p^e || n).
  p^e divides n, but p^{e+1} does not.
-/
def ExactValuation (p e n : ℕ) : Prop :=
  p^e ∣ n ∧ ¬(p^(e+1) ∣ n)

/-- Structure representing the Prefix-Suffix bipartition of the search space.
    This is purely algebraic: it captures that N factors as N_L * N_R with coprime,
    positive components. No QPN assumption is required — the Rust engine constructs
    these speculatively during DFS before any QPN check occurs. The QPN hypothesis
    is supplied separately to theorems that need it.

    Corresponds to the Rust engine's `Prefix` struct, which carries `n_l`, `s_l`,
    `factors`, and `sigma_factors` without any number-theoretic precondition. -/
structure Bipartition where
  N : ℕ
  N_L : ℕ
  N_R : ℕ
  h_mul : N = N_L * N_R
  h_pos : N_L > 0 ∧ N_R > 0
  h_coprime : N_L.Coprime N_R

end UALBF
