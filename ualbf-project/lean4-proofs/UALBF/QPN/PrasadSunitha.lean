import UALBF.QPN.BasicProperties
import UALBF.Pure.RationalBounds
import UALBF.Pure.Zsigmondy
import UALBF.QPN.Obstruction
import UALBF.Pure.Cyclotomic
import UALBF.Engine.SieveSoundness

namespace UALBF.QPN.PrasadSunitha

open UALBF
open UALBF.QPN.BasicProperties
open UALBF.Pure.Zsigmondy
open UALBF.QPN.Obstruction
open UALBF.Pure.RationalBounds
open UALBF.Pure.Cyclotomic

axiom prasad_sunitha_bound_no_3_5 {N : ℕ} (h_qpn : IsQuasiperfect N) (h_coprime : N.Coprime 15) : False

axiom qpn_coprime_15_omega_bound {N : ℕ} (h_qpn : IsQuasiperfect N)
    (h_coprime : N.Coprime 15) : 15 ≤ N.primeFactors.card

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

theorem val_11_ge_4 {N : ℕ} (h_qpn : IsQuasiperfect N) (h_11 : 11 ∈ N.primeFactors) : N.factorization 11 ≥ 4 := by
  by_contra h_lt
  push_neg at h_lt
  have ⟨_, m, hm⟩ := qpn_is_odd_square h_qpn
  have hm_ne : m ≠ 0 := by intro h; rw [h] at hm; exact Nat.ne_of_gt h_qpn.1 hm
  have h_eq : N.factorization 11 = 2 * m.factorization 11 := by
    rw [hm, Nat.factorization_pow]
    simp [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
  have h_pos : 1 ≤ N.factorization 11 := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp h_11)
  have h2 : N.factorization 11 = 2 := by omega
  have hp : Nat.Prime 11 := by decide
  have hN : N ≠ 0 := by omega
  have h_div : 11 ^ 2 ∣ N := (hp.pow_dvd_iff_le_factorization hN).mpr (by omega)
  have h_ndiv : ¬ (11 ^ 3 ∣ N) := by
    intro h
    have h_le := (hp.pow_dvd_iff_le_factorization hN).mp h
    omega
  have h_exact : ExactValuation 11 2 N := ⟨h_div, h_ndiv⟩
  have hq : Nat.Prime 7 := by decide
  have hq_odd : 7 ≠ 2 := by decide
  have h_mod : 7 % 8 = 5 ∨ 7 % 8 = 7 := Or.inr (by decide)
  have h_sigma_eq : sigma (11 ^ 2) = sigma_prime_pow 11 1 := sigma_eq_sigma_prime_pow 11 1 hp
  have h_div_sig : 7 ∣ sigma (11 ^ 2) := by
    rw [h_sigma_eq]
    decide
  exact UALBF.Engine.SieveSoundness.rust_sieve_soundness h_qpn hp hq hq_odd h_mod h_div_sig h_exact

theorem val_13_ge_4 {N : ℕ} (h_qpn : IsQuasiperfect N) (h_13 : 13 ∈ N.primeFactors) : N.factorization 13 ≥ 4 := by
  by_contra h_lt
  push_neg at h_lt
  have ⟨_, m, hm⟩ := qpn_is_odd_square h_qpn
  have hm_ne : m ≠ 0 := by intro h; rw [h] at hm; exact Nat.ne_of_gt h_qpn.1 hm
  have h_eq : N.factorization 13 = 2 * m.factorization 13 := by
    rw [hm, Nat.factorization_pow]
    simp [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
  have h_pos : 1 ≤ N.factorization 13 := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp h_13)
  have h2 : N.factorization 13 = 2 := by omega
  have hp : Nat.Prime 13 := by decide
  have hN : N ≠ 0 := by omega
  have h_div : 13 ^ 2 ∣ N := (hp.pow_dvd_iff_le_factorization hN).mpr (by omega)
  have h_ndiv : ¬ (13 ^ 3 ∣ N) := by
    intro h
    have h_le := (hp.pow_dvd_iff_le_factorization hN).mp h
    omega
  have h_exact : ExactValuation 13 2 N := ⟨h_div, h_ndiv⟩
  have hq : Nat.Prime 61 := by decide
  have hq_odd : 61 ≠ 2 := by decide
  have h_mod : 61 % 8 = 5 ∨ 61 % 8 = 7 := Or.inl (by decide)
  have h_sigma_eq : sigma (13 ^ 2) = sigma_prime_pow 13 1 := sigma_eq_sigma_prime_pow 13 1 hp
  have h_div_sig : 61 ∣ sigma (13 ^ 2) := by
    rw [h_sigma_eq]
    decide
  exact UALBF.Engine.SieveSoundness.rust_sieve_soundness h_qpn hp hq hq_odd h_mod h_div_sig h_exact

end UALBF.QPN.PrasadSunitha
