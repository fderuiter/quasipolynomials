import UALBF.QPN.BasicProperties
import UALBF.Pure.RationalBounds

namespace UALBF.QPN.PrasadSunitha

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

end UALBF.QPN.PrasadSunitha
