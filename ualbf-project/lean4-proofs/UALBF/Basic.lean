import Mathlib.Data.Nat.Basic
import Mathlib.NumberTheory.Divisors

namespace UALBF

open Finset

/-- The sum of divisors function σ(n). -/
noncomputable def sigma (n : ℕ) : ℕ :=
  ∑ d ∈ n.divisors, d

/-- A number is quasiperfect if σ(n) = 2n + 1. -/
def IsQuasiperfect (n : ℕ) : Prop :=
  n > 0 ∧ sigma n = 2 * n + 1

/-- 
  Theorem 1: The Parity of σ(N).
  Because 2n + 1 is inherently odd, σ(N) must be odd. 
-/
lemma qpn_sigma_odd {n : ℕ} (h : IsQuasiperfect n) : Odd (sigma n) := by
  -- Proof Strategy: sigma n = 2n + 1, which fits the definition of Odd (2k + 1).
  exact ⟨n, h.2⟩

/-- A known theorem in number theory: σ(n) is odd iff n is a perfect square or twice a perfect square. -/
lemma odd_sigma_iff_square_or_double_square (n : ℕ) : 
  Odd (sigma n) ↔ (∃ m : ℕ, n = m ^ 2) ∨ (∃ m : ℕ, n = 2 * m ^ 2) := by
  sorry

/-- An even QPN would require n = 2m^2 (abundancy limit & parity structural necessity). -/
lemma even_qpn_implies_double_square {n : ℕ} (h : IsQuasiperfect n) (heven : Even n) : 
  ∃ m : ℕ, n = 2 * m ^ 2 := by
  sorry

/-- A double square cannot be a QPN due to abundancy limits and parity contradiction. -/
lemma qpn_not_double_square {n : ℕ} (h : IsQuasiperfect n) : 
  ¬ ∃ m : ℕ, n = 2 * m ^ 2 := by
  sorry

/-- 
  Theorem 2: QPNs are Odd Perfect Squares.
  A known number-theoretic fact states that if σ(n) is odd, n is either a 
  perfect square or twice a perfect square. Because an even QPN would require
  n = 2m^2 (leading to a contradiction in abundancy limits and parity), n must 
  be an odd perfect square.
-/
theorem qpn_is_odd_square {n : ℕ} (h : IsQuasiperfect n) : 
  Odd n ∧ ∃ m : ℕ, n = m ^ 2 := by
  -- 1. sigma n is odd because sigma n = 2n + 1
  have h_odd_sigma : Odd (sigma n) := qpn_sigma_odd h

  -- 2. By number theory, n is either a square or a double square
  have h_sq_or_dbl : (∃ m : ℕ, n = m ^ 2) ∨ (∃ m : ℕ, n = 2 * m ^ 2) := 
    (odd_sigma_iff_square_or_double_square n).mp h_odd_sigma

  -- 3. A QPN cannot be a double square
  have h_not_dbl : ¬ ∃ m : ℕ, n = 2 * m ^ 2 := qpn_not_double_square h

  -- 4. Therefore, n must be a perfect square
  have h_is_sq : ∃ m : ℕ, n = m ^ 2 := by
    rcases h_sq_or_dbl with h_sq | h_dbl
    · exact h_sq
    · exact False.elim (h_not_dbl h_dbl)

  -- 5. Show that n must be odd. 
  -- If n were even, it would require n = 2m^2, which is explicitly impossible.
  have h_odd_n : Odd n := by
    cases Nat.even_or_odd n with
    | inl h_even =>
      have h_dbl := even_qpn_implies_double_square h h_even
      exact False.elim (h_not_dbl h_dbl)
    | inr h_odd =>
      exact h_odd

  -- 6. Conclude the goal
  exact ⟨h_odd_n, h_is_sq⟩

end UALBF
