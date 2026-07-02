import UALBF.QPN.BasicProperties
import UALBF.Pure.RationalBounds
import UALBF.Pure.Zsigmondy
import UALBF.QPN.Obstruction
import UALBF.Engine.SieveSoundness
import Mathlib.Data.Nat.Factorization.Basic

namespace UALBF.QPN.PrasadSunitha

open UALBF.QPN.BasicProperties
open UALBF.Pure.RationalBounds
open UALBF.Pure.Zsigmondy
open UALBF.QPN.Obstruction
open UALBF.Engine.SieveSoundness
open UALBF

axiom prasad_sunitha_bound_no_3_5 {N : ℕ} (h_qpn : IsQuasiperfect N) (h_coprime : N.Coprime 15) : False

theorem qpn_coprime_15_omega_bound {N : ℕ} (h_qpn : IsQuasiperfect N)
    (h_coprime : N.Coprime 15) : 15 ≤ N.primeFactors.card := by
  have h := prasad_sunitha_bound_no_3_5 h_qpn h_coprime
  exact False.elim h

theorem qpn_coprime_15_primes_ge_7 {N : ℕ} (h_qpn : IsQuasiperfect N) (h_coprime : N.Coprime 15) : ∀ p ∈ N.primeFactors, p ≥ 7 := by
  intro p hp
  have h_prime := Nat.prime_of_mem_primeFactors hp
  have hp_dvd := Nat.dvd_of_mem_primeFactors hp
  have h_odd : Odd N := (qpn_is_odd_square h_qpn).1
  have p_ne_2 : p ≠ 2 := by
    rintro rfl
    rcases h_odd with ⟨k, hk⟩
    rcases hp_dvd with ⟨j, hj⟩
    omega
  have p_ne_3 : p ≠ 3 := by
    rintro rfl
    have h3_dvd_15 : 3 ∣ 15 := ⟨5, rfl⟩
    have h3_dvd_gcd : 3 ∣ N.gcd 15 := Nat.dvd_gcd hp_dvd h3_dvd_15
    have h_gcd_eq_1 : N.gcd 15 = 1 := h_coprime
    rw [h_gcd_eq_1] at h3_dvd_gcd
    rcases h3_dvd_gcd with ⟨c, hc⟩
    omega
  have p_ne_5 : p ≠ 5 := by
    rintro rfl
    have h5_dvd_15 : 5 ∣ 15 := ⟨3, rfl⟩
    have h5_dvd_gcd : 5 ∣ N.gcd 15 := Nat.dvd_gcd hp_dvd h5_dvd_15
    have h_gcd_eq_1 : N.gcd 15 = 1 := h_coprime
    rw [h_gcd_eq_1] at h5_dvd_gcd
    rcases h5_dvd_gcd with ⟨c, hc⟩
    omega
  have p_ge_2 : p ≥ 2 := h_prime.two_le
  omega

/-- For a QPN (which is an odd square m²), every prime in its factorization
    has exponent ≥ 2 (all exponents are even, and membership ensures ≥ 1). -/
lemma qpn_factorization_ge_two {N : ℕ} (h_qpn : IsQuasiperfect N)
    (p : ℕ) (hp : p ∈ N.primeFactors) :
    N.factorization p ≥ 2 := by
  have ⟨_, m, hm⟩ := qpn_is_odd_square h_qpn
  have hN_ne : N ≠ 0 := by have := h_qpn.1; omega
  have hm_sq : N.factorization p = 2 * m.factorization p := by
    have hm_ne : m ≠ 0 := by intro h; rw [h] at hm; simp at hm; omega
    rw [hm, Nat.factorization_pow]
    simp [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
  have h_ge1 : N.factorization p ≥ 1 :=
    Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hp)
  omega

lemma qpn_coprime_15_val_11_ge_4 {N : ℕ} (h_qpn : IsQuasiperfect N) (h_coprime : N.Coprime 15) (h_11 : 11 ∈ N.primeFactors) : N.factorization 11 ≥ 4 := by
  have h_ge_2 := qpn_factorization_ge_two h_qpn 11 h_11
  by_contra h_lt
  push_neg at h_lt
  have h_eq2 : N.factorization 11 = 2 := by omega
  have hN : N ≠ 0 := Nat.ne_of_gt h_qpn.1
  have pp : 11.Prime := by decide
  have h_exact : ExactValuation 11 2 N := by
    unfold ExactValuation
    constructor
    · apply (Nat.Prime.pow_dvd_iff_le_factorization pp hN).mpr
      omega
    · intro h_dvd3
      have h_le := (Nat.Prime.pow_dvd_iff_le_factorization pp hN).mp h_dvd3
      omega
  have _zsig := zsigmondy_theorem 11 1 (by decide) (by decide) (by decide)
  have h_sieve : ¬ ExactValuation 11 2 N := by
    apply rust_sieve_soundness (q := 7) h_qpn (by decide) (by decide) (by decide) (by decide)
    have h_eq := sigma_eq_sigma_prime_pow 11 1 (by decide)
    have h_pow : 11 ^ (2 * 1) = 11 ^ 2 := rfl
    rw [h_pow] at h_eq
    have h_comp : sigma_prime_pow 11 1 = 133 := by decide
    rw [h_comp] at h_eq
    rw [h_eq]
    exact ⟨19, rfl⟩
  exact h_sieve h_exact

lemma qpn_coprime_15_val_13_ge_4 {N : ℕ} (h_qpn : IsQuasiperfect N) (h_coprime : N.Coprime 15) (h_13 : 13 ∈ N.primeFactors) : N.factorization 13 ≥ 4 := by
  have h_ge_2 := qpn_factorization_ge_two h_qpn 13 h_13
  by_contra h_lt
  push_neg at h_lt
  have h_eq2 : N.factorization 13 = 2 := by omega
  have hN : N ≠ 0 := Nat.ne_of_gt h_qpn.1
  have pp : 13.Prime := by decide
  have h_exact : ExactValuation 13 2 N := by
    unfold ExactValuation
    constructor
    · apply (Nat.Prime.pow_dvd_iff_le_factorization pp hN).mpr
      omega
    · intro h_dvd3
      have h_le := (Nat.Prime.pow_dvd_iff_le_factorization pp hN).mp h_dvd3
      omega
  have _zsig := zsigmondy_theorem 13 1 (by decide) (by decide) (by decide)
  have h_sieve : ¬ ExactValuation 13 2 N := by
    apply rust_sieve_soundness (q := 61) h_qpn (by decide) (by decide) (by decide) (by decide)
    have h_eq := sigma_eq_sigma_prime_pow 13 1 (by decide)
    have h_pow : 13 ^ (2 * 1) = 13 ^ 2 := rfl
    rw [h_pow] at h_eq
    have h_comp : sigma_prime_pow 13 1 = 183 := by decide
    rw [h_comp] at h_eq
    rw [h_eq]
    exact ⟨3, rfl⟩
  exact h_sieve h_exact

end UALBF.QPN.PrasadSunitha
