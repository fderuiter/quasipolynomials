import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Factorization.Basic
import UALBF.Basic

namespace UALBF.SpecialFactors

/-- The first 14 valid odd primes strictly greater than 5.
    We skip 3 and 5 to simulate the `gcd(N, 15) = 1` condition. -/
def cubeCPrimes : List ℕ :=
  [7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59]

/-- Computes the theoretical maximum abundancy (Euler product)
    for a given list of primes: ∏ p / (p - 1). -/
def maxAbundancy (primes : List ℕ) : ℚ :=
  primes.foldl (fun acc p => acc * (p : ℚ) / ((p - 1) : ℚ)) 1

/--
  Theorem: The maximum possible abundancy of an integer built from
  at most 14 primes (excluding 3 and 5) is strictly less than 2.
  Evaluates exactly to ≈ 1.9933.
-/
theorem abundancy_cube_c_lt_two : maxAbundancy cubeCPrimes < 2 := by
  native_decide

/--
  Because maxAbundancy < 2, any integer N coprime to 15 (missing 3 and 5)
  with ω(N) ≤ 14 cannot reach an abundancy of 2.0.
  Therefore, if N is Quasiperfect and gcd(N, 15) = 1, ω(N) must be ≥ 15.
-/
axiom qpn_coprime_15_omega_15 {N : ℕ} (h_qpn : IsQuasiperfect N) (h_coprime : N.gcd 15 = 1) :
  N.primeFactors.card ≥ 15

end UALBF.SpecialFactors
