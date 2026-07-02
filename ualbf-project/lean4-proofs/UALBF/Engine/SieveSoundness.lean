import Mathlib.Data.Nat.Factorization.Basic
import UALBF.Basic
import UALBF.Engine.Bipartition
import UALBF.QPN.Obstruction
import UALBF.Engine.Obstruction

/-!
# Engine: Sieve Soundness

Exact valuation theorems that prove the Rust engine's valuation sieve
is mathematically sound. The ExactValuation definition lives in Basic.lean.
-/

namespace UALBF.Engine.SieveSoundness

open UALBF UALBF.QPN.Obstruction UALBF.Engine.Bipartition UALBF.Engine.Obstruction

/--
  Exact Divisibility implies Sigma Divisibility.
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
  Soundness of the Rust Engine's Valuation Sieve.
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
  intro h_exact
  have h_sigma_dvd := exact_val_sigma_dvd hp_prime h_exact
  have h_q_div_sigma_N := dvd_trans h_q_div h_sigma_dvd
  have h_obstruction := legendre_cattaneo_obstruction h_qpn hq_prime hq_odd h_q_div_sigma_N
  omega

/--
  Soundness of the Rust Engine's Modulo-3 Sieve.
  If N is a QPN and N ≡ 0 (mod 3), then sigma(p^(2e)) CANNOT be a multiple of 3.
-/
theorem rust_sieve_soundness_mod_3 {N p e : ℕ}
  (h_qpn : IsQuasiperfect N)
  (h_mod3 : N % 3 = 0)
  (hp_prime : p.Prime)
  (h_bad_mod : sigma (p^(2*e)) % 3 = 0) :
  ¬ ExactValuation p (2*e) N := by
  intro h_exact
  have h_dvd := exact_val_sigma_dvd hp_prime h_exact
  have h_3_dvd : 3 ∣ sigma (p^(2*e)) := Nat.dvd_of_mod_eq_zero h_bad_mod
  have h_3_dvd_sigma : 3 ∣ sigma N := dvd_trans h_3_dvd h_dvd
  have h_not_dvd := qpn_sigma_mod_3 h_qpn (Nat.dvd_of_mod_eq_zero h_mod3)
  have h_mod_zero : sigma N % 3 = 0 := Nat.mod_eq_zero_of_dvd h_3_dvd_sigma
  exact h_not_dvd h_mod_zero

/--
  Soundness of the Rust Engine's Modulo-9 Sieve.
  If N is a QPN and N ≡ 0 (mod 9), then sigma(p^(2e)) CANNOT be a multiple of 3 (i.e. 0, 3, 6 mod 9).
-/
theorem rust_sieve_soundness_mod_9 {N p e : ℕ}
  (h_qpn : IsQuasiperfect N)
  (h_mod9 : N % 9 = 0)
  (hp_prime : p.Prime)
  (h_bad_mod : sigma (p^(2*e)) % 9 = 0 ∨ sigma (p^(2*e)) % 9 = 3 ∨ sigma (p^(2*e)) % 9 = 6) :
  ¬ ExactValuation p (2*e) N := by
  intro h_exact
  have h_dvd := exact_val_sigma_dvd hp_prime h_exact
  have h_3_dvd : 3 ∣ sigma (p^(2*e)) := by omega
  have h_3_dvd_sigma : 3 ∣ sigma N := dvd_trans h_3_dvd h_dvd
  have h_9_dvd_N : 9 ∣ N := Nat.dvd_of_mod_eq_zero h_mod9
  have h_3_dvd_N : 3 ∣ N := dvd_trans (by decide : 3 ∣ 9) h_9_dvd_N
  have h_not_dvd := qpn_sigma_mod_9 h_qpn h_3_dvd_N
  have h_mod : sigma N % 9 = 0 ∨ sigma N % 9 = 3 ∨ sigma N % 9 = 6 := by
    have h_mod_3 : sigma N % 3 = 0 := by
      have h3 : 3 ∣ sigma N := h_3_dvd_sigma
      exact Nat.mod_eq_zero_of_dvd h3
    omega
  omega

end UALBF.Engine.SieveSoundness
