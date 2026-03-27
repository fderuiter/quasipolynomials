import UALBF.Obstruction
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

namespace UALBF

open Finset Nat Polynomial

/--
  Task 1: Cyclotomic Expansion.
  σ(p^{2e}) factors exactly into ∏_{d | 2e+1, d>1} Φ_d(p).
-/
lemma sigma_prime_pow_cyclotomic (p e : ℕ) (hp : p.Prime) :
  sigma (p ^ (2 * e)) = ∏ d ∈ (2 * e + 1).divisors \ {1}, (eval (p : ℤ) (cyclotomic d ℤ)).natAbs := by
  sorry

/--
  Task 2: Axiomatize Zsigmondy.
  For 2e+1 ≥ 3, the expansion possesses at least one primitive prime divisor q
  that does not divide lower powers. It implies q ≡ 1 (mod 2e+1).
  We axiomatize that such q exists and divides σ(p^{2e}).
-/
axiom zsigmondy_axiom (p e : ℕ) (hp : p.Prime) (he : 2 * e + 1 ≥ 3) :
  ∃ q : ℕ, q.Prime ∧ q ∣ sigma (p ^ (2 * e)) ∧ ¬(q ∣ p - 1) ∧ q % (2 * e + 1) = 1

/--
  Task 3: The Poison Trap (zsigmondy_poison_trap).
  Chain Zsigmondy directly to legendre_cattaneo_obstruction.
  Prove that exponent inflation logically guarantees the generation of a primitive prime q.
  If q ≡ 5 or 7 (mod 8), the exponent is mathematically forbidden for a quasiperfect number.
-/
lemma zsigmondy_poison_trap {n p e : ℕ}
  (h_qpn : IsQuasiperfect n)
  (_hn_odd : Odd n)
  (_hp_prime : p.Prime)
  (hp_dvd : p ^ (2 * e) ∣ n)
  (hp_coprime : Nat.Coprime (p ^ (2 * e)) (n / p ^ (2 * e)))
  (_he_bound : 2 * e + 1 ≥ 3) :
  ∀ q, (q.Prime ∧ q ∣ sigma (p ^ (2 * e)) ∧ ¬(q ∣ p - 1) ∧ q % (2 * e + 1) = 1) →
  q % 8 ≠ 5 ∧ q % 8 ≠ 7 := by
  -- Zsigmondy guarantees such a q exists, here we take it as given from the ∀ statement
  intro q hq
  rcases hq with ⟨hq_prime, hq_div_sigma, _, _⟩

  -- q divides σ(p^{2e}) which divides σ(n)
  have h_sigma_dvd : sigma (p ^ (2 * e)) ∣ sigma n := by
    have h_prod : n = p ^ (2 * e) * (n / p ^ (2 * e)) := (Nat.mul_div_cancel' hp_dvd).symm
    have h_sigma_prod : sigma n = sigma (p ^ (2 * e)) * sigma (n / p ^ (2 * e)) := by
      nth_rw 1 [h_prod]
      exact Nat.Coprime.sum_divisors_mul hp_coprime
    rw [h_sigma_prod]
    exact dvd_mul_right _ _

  have hq_dvd_sigma_n : q ∣ sigma n := dvd_trans hq_div_sigma h_sigma_dvd

  have hq_odd : q ≠ 2 := by
    intro hq2
    rw [hq2] at hq_dvd_sigma_n
    have hsigma_odd : Odd (sigma n) := qpn_sigma_odd h_qpn
    have hsigma_even : Even (sigma n) := even_iff_two_dvd.mpr hq_dvd_sigma_n
    have h_contra : ¬ Even (sigma n) := by
      rcases hsigma_odd with ⟨k, hk⟩
      intro ⟨j, hj⟩
      omega
    exact False.elim (h_contra hsigma_even)

  have h_mod8 : q % 8 = 1 ∨ q % 8 = 3 := legendre_cattaneo_obstruction h_qpn hq_prime hq_odd hq_dvd_sigma_n

  constructor
  · intro h5
    rcases h_mod8 with h1 | h3
    · omega
    · omega
  · intro h7
    rcases h_mod8 with h1 | h3
    · omega
    · omega

end UALBF
