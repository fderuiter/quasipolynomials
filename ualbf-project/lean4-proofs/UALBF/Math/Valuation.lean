import Mathlib.Data.Nat.Factorization.Basic
import UALBF.Basic
import UALBF.Math.Bipartition
import UALBF.Math.Obstruction

namespace UALBF.Math.Valuation

open UALBF UALBF.Math.Obstruction UALBF.Math.Bipartition

/--
  Definition of Exact Valuation (p^e || n).
  p^e divides n, but p^{e+1} does not.
-/
def ExactValuation (p e n : ℕ) : Prop :=
  p^e ∣ n ∧ ¬(p^(e+1) ∣ n)

/--
  Theorem 7: Exact Divisibility implies Sigma Divisibility.
-/
lemma exact_val_sigma_dvd {n p e : ℕ}
  (hp_prime : p.Prime)
  (h_exact : ExactValuation p (2*e) n) :
  sigma (p^(2*e)) ∣ sigma n := by
  have h_dvd : p^(2*e) ∣ n := h_exact.1
  rcases h_dvd with ⟨k, hk⟩

  have hk_not_dvd : ¬ (p ∣ k) := by
    intro h_p_dvd_k
    rcases h_p_dvd_k with ⟨m, hm⟩
    have h_contra : p^(2*e+1) ∣ n := by
      rw [hk, hm, pow_add, pow_one]
      exact ⟨m, by rw [Nat.mul_assoc]⟩
    exact h_exact.2 h_contra

  have h_coprime_p_k : Nat.Coprime p k := (Nat.Prime.coprime_iff_not_dvd hp_prime).mpr hk_not_dvd
  have h_coprime : Nat.Coprime (p^(2*e)) k := Nat.Coprime.pow_left (2*e) h_coprime_p_k

  have h_sigma_mul : sigma n = sigma (p^(2*e)) * sigma k := by
    rw [hk]
    unfold sigma
    exact Nat.Coprime.sum_divisors_mul h_coprime

  rw [h_sigma_mul]
  exact dvd_mul_right (sigma (p ^ (2 * e))) (sigma k)

/--
  Theorem 8: The Soundness of the Rust Engine's Valuation Sieve.
  If sigma(p^(2e)) contains a prime factor q ≡ 5 or 7 (mod 8),
  then p^(2e) CANNOT exactly divide a Quasiperfect Number N.
-/
theorem rust_sieve_soundness {N p e q : ℕ}
  (h_qpn : IsQuasiperfect N)
  (hp_prime : p.Prime)
  (hq_prime : q.Prime)
  (hq_odd : q ≠ 2)
  (h_bad_mod : q % 8 = 5 ∨ q % 8 = 7)
  (h_q_div : q ∣ sigma (p^(2*e))) :
  ¬ ExactValuation p (2*e) N := by

  -- Proof by Contradiction Strategy:
  -- 1. Assume `ExactValuation p (2*e) N` is true.
  -- 2. By Theorem 7 (`exact_val_sigma_dvd`), `sigma(p^(2e)) ∣ sigma(N)`.
  -- 3. Since `q ∣ sigma(p^(2e))`, transitivity means `q ∣ sigma(N)`.
  -- 4. Apply Theorem 6 (`legendre_cattaneo_obstruction`):
  --    Any odd prime q dividing sigma(N) MUST satisfy `q % 8 = 1` or `3`.
  -- 5. This directly contradicts `h_bad_mod` (which says q is 5 or 7 mod 8).
  -- 6. Therefore, the exact valuation assumption is mathematically false.
  intro h_exact
  have h_sigma_dvd := exact_val_sigma_dvd hp_prime h_exact
  have h_q_div_sigma_N := dvd_trans h_q_div h_sigma_dvd
  have h_obstruction := legendre_cattaneo_obstruction h_qpn hq_prime hq_odd h_q_div_sigma_N
  omega

end UALBF.Math.Valuation
