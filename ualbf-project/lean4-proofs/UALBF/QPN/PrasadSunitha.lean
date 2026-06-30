import UALBF.QPN.BasicProperties
import UALBF.Pure.RationalBounds

namespace UALBF.QPN.PrasadSunitha

theorem prasad_sunitha_bound_no_3_5 {N : ℕ} (h_qpn : IsQuasiperfect N) (h_coprime : N.Coprime 15) : False := sorry

theorem qpn_coprime_15_omega_bound {N : ℕ} (h_qpn : IsQuasiperfect N)
    (h_coprime : N.Coprime 15) : False := sorry

theorem qpn_coprime_15_primes_ge_7 {N : ℕ} (h_qpn : IsQuasiperfect N) (h_coprime : N.Coprime 15) : ∀ p ∈ N.primeFactors, p ≥ 7 := sorry

end UALBF.QPN.PrasadSunitha
