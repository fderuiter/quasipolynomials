import UALBF.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Factorization.Basic
import UALBF.FFI
import UALBF.ManifestConstants

namespace UALBF.Engine.CrtTensorBridge

open UALBF

-- --- Modulo 3 Bridge ---

theorem sigma_p_mod_3 (p e : ℕ) (hp : p.Prime) (hp1 : p % 3 = 1) :
  (sigma (p ^ (2 * e)) : ZMod 3) = (2 * e + 1 : ℕ) := by
  have h_sum : sigma (p ^ (2 * e)) = ∑ x ∈ Finset.range (2 * e + 1), p ^ x := by
    exact (Nat.sum_divisors_prime_pow hp)
  rw [h_sum]
  push_cast
  have h_p_zmod : (p : ZMod 3) = 1 := by
    have h1 : ((p % 3 : ℕ) : ZMod 3) = (1 : ZMod 3) := by rw [hp1]; rfl
    have h2 : ((p % 3 : ℕ) : ZMod 3) = (p : ZMod 3) := by exact ZMod.natCast_mod p 3
    rw [←h2]
    exact h1
  have h_pow : ∀ x, (p : ZMod 3) ^ x = 1 := by
    intro x
    rw [h_p_zmod, one_pow]
  have h_sum_zmod : ∑ x ∈ Finset.range (2 * e + 1), (p : ZMod 3) ^ x = ∑ x ∈ Finset.range (2 * e + 1), (1 : ZMod 3) := by
    apply Finset.sum_congr rfl
    intro x _
    exact h_pow x
  rw [h_sum_zmod, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  push_cast
  rfl

theorem mod3_bridge (p e : ℕ) (hp : p.Prime)
  (h_p : p % 3 = 1) (h_e : e % 3 = 1) :
  sigma (p ^ (2 * e)) % 3 = 0 := by
  have h1 := sigma_p_mod_3 p e hp h_p
  have h_e_zmod : (e : ZMod 3) = 1 := by
    have ha : ((e % 3 : ℕ) : ZMod 3) = (1 : ZMod 3) := by rw [h_e]; rfl
    have hb : ((e % 3 : ℕ) : ZMod 3) = (e : ZMod 3) := by exact ZMod.natCast_mod e 3
    rw [←hb]
    exact ha
  have h2 : ((2 * e + 1 : ℕ) : ZMod 3) = 0 := by
    push_cast
    rw [h_e_zmod]
    decide
  rw [h2] at h1
  have h3 : ((sigma (p ^ (2 * e))) : ZMod 3).val = (0 : ZMod 3).val := by rw [h1]
  rw [ZMod.val_natCast, ZMod.val_zero] at h3
  exact h3


-- --- Modulo 5 Bridge ---

theorem sigma_p_mod_5 (p e : ℕ) (hp : p.Prime) (hp1 : p % 5 = 1) :
  (sigma (p ^ (2 * e)) : ZMod 5) = (2 * e + 1 : ℕ) := by
  have h_sum : sigma (p ^ (2 * e)) = ∑ x ∈ Finset.range (2 * e + 1), p ^ x := by
    exact (Nat.sum_divisors_prime_pow hp)
  rw [h_sum]
  push_cast
  have h_p_zmod : (p : ZMod 5) = 1 := by
    have h1 : ((p % 5 : ℕ) : ZMod 5) = (1 : ZMod 5) := by rw [hp1]; rfl
    have h2 : ((p % 5 : ℕ) : ZMod 5) = (p : ZMod 5) := by exact ZMod.natCast_mod p 5
    rw [←h2]
    exact h1
  have h_pow : ∀ x, (p : ZMod 5) ^ x = 1 := by
    intro x
    rw [h_p_zmod, one_pow]
  have h_sum_zmod : ∑ x ∈ Finset.range (2 * e + 1), (p : ZMod 5) ^ x = ∑ x ∈ Finset.range (2 * e + 1), (1 : ZMod 5) := by
    apply Finset.sum_congr rfl
    intro x _
    exact h_pow x
  rw [h_sum_zmod, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  push_cast
  rfl

theorem mod5_bridge (p e : ℕ) (hp : p.Prime)
  (h_p : p % 5 = 1) (h_e : e % 5 = 2) :
  sigma (p ^ (2 * e)) % 5 = 0 := by
  have h1 := sigma_p_mod_5 p e hp h_p
  have h_e_zmod : (e : ZMod 5) = 2 := by
    have ha : ((e % 5 : ℕ) : ZMod 5) = (2 : ZMod 5) := by rw [h_e]; rfl
    have hb : ((e % 5 : ℕ) : ZMod 5) = (e : ZMod 5) := by exact ZMod.natCast_mod e 5
    rw [←hb]
    exact ha
  have h2 : ((2 * e + 1 : ℕ) : ZMod 5) = 0 := by
    push_cast
    rw [h_e_zmod]
    decide
  rw [h2] at h1
  have h3 : ((sigma (p ^ (2 * e))) : ZMod 5).val = (0 : ZMod 5).val := by rw [h1]
  rw [ZMod.val_natCast, ZMod.val_zero] at h3
  exact h3


-- --- Modulo 7 Bridge ---

theorem sigma_p_mod_7 (p e : ℕ) (hp : p.Prime) (hp1 : p % 7 = 1) :
  (sigma (p ^ (2 * e)) : ZMod 7) = (2 * e + 1 : ℕ) := by
  have h_sum : sigma (p ^ (2 * e)) = ∑ x ∈ Finset.range (2 * e + 1), p ^ x := by
    exact (Nat.sum_divisors_prime_pow hp)
  rw [h_sum]
  push_cast
  have h_p_zmod : (p : ZMod 7) = 1 := by
    have h1 : ((p % 7 : ℕ) : ZMod 7) = (1 : ZMod 7) := by rw [hp1]; rfl
    have h2 : ((p % 7 : ℕ) : ZMod 7) = (p : ZMod 7) := by exact ZMod.natCast_mod p 7
    rw [←h2]
    exact h1
  have h_pow : ∀ x, (p : ZMod 7) ^ x = 1 := by
    intro x
    rw [h_p_zmod, one_pow]
  have h_sum_zmod : ∑ x ∈ Finset.range (2 * e + 1), (p : ZMod 7) ^ x = ∑ x ∈ Finset.range (2 * e + 1), (1 : ZMod 7) := by
    apply Finset.sum_congr rfl
    intro x _
    exact h_pow x
  rw [h_sum_zmod, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  push_cast
  rfl

theorem mod7_bridge (p e : ℕ) (hp : p.Prime)
  (h_p : p % 7 = 1) (h_e : e % 7 = 3) :
  sigma (p ^ (2 * e)) % 7 = 0 := by
  have h1 := sigma_p_mod_7 p e hp h_p
  have h_e_zmod : (e : ZMod 7) = 3 := by
    have ha : ((e % 7 : ℕ) : ZMod 7) = (3 : ZMod 7) := by rw [h_e]; rfl
    have hb : ((e % 7 : ℕ) : ZMod 7) = (e : ZMod 7) := by exact ZMod.natCast_mod e 7
    rw [←hb]
    exact ha
  have h2 : ((2 * e + 1 : ℕ) : ZMod 7) = 0 := by
    push_cast
    rw [h_e_zmod]
    decide
  rw [h2] at h1
  have h3 : ((sigma (p ^ (2 * e))) : ZMod 7).val = (0 : ZMod 7).val := by rw [h1]
  rw [ZMod.val_natCast, ZMod.val_zero] at h3
  exact h3


-- --- Modulo 11 Bridge ---

theorem sigma_p_mod_11 (p e : ℕ) (hp : p.Prime) (hp1 : p % 11 = 1) :
  (sigma (p ^ (2 * e)) : ZMod 11) = (2 * e + 1 : ℕ) := by
  have h_sum : sigma (p ^ (2 * e)) = ∑ x ∈ Finset.range (2 * e + 1), p ^ x := by
    exact (Nat.sum_divisors_prime_pow hp)
  rw [h_sum]
  push_cast
  have h_p_zmod : (p : ZMod 11) = 1 := by
    have h1 : ((p % 11 : ℕ) : ZMod 11) = (1 : ZMod 11) := by rw [hp1]; rfl
    have h2 : ((p % 11 : ℕ) : ZMod 11) = (p : ZMod 11) := by exact ZMod.natCast_mod p 11
    rw [←h2]
    exact h1
  have h_pow : ∀ x, (p : ZMod 11) ^ x = 1 := by
    intro x
    rw [h_p_zmod, one_pow]
  have h_sum_zmod : ∑ x ∈ Finset.range (2 * e + 1), (p : ZMod 11) ^ x = ∑ x ∈ Finset.range (2 * e + 1), (1 : ZMod 11) := by
    apply Finset.sum_congr rfl
    intro x _
    exact h_pow x
  rw [h_sum_zmod, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  push_cast
  rfl

theorem mod11_bridge (p e : ℕ) (hp : p.Prime)
  (h_p : p % 11 = 1) (h_e : e % 11 = 5) :
  sigma (p ^ (2 * e)) % 11 = 0 := by
  have h1 := sigma_p_mod_11 p e hp h_p
  have h_e_zmod : (e : ZMod 11) = 5 := by
    have ha : ((e % 11 : ℕ) : ZMod 11) = (5 : ZMod 11) := by rw [h_e]; rfl
    have hb : ((e % 11 : ℕ) : ZMod 11) = (e : ZMod 11) := by exact ZMod.natCast_mod e 11
    rw [←hb]
    exact ha
  have h2 : ((2 * e + 1 : ℕ) : ZMod 11) = 0 := by
    push_cast
    rw [h_e_zmod]
    decide
  rw [h2] at h1
  have h3 : ((sigma (p ^ (2 * e))) : ZMod 11).val = (0 : ZMod 11).val := by rw [h1]
  rw [ZMod.val_natCast, ZMod.val_zero] at h3
  exact h3


-- --- Combined CRT Obstruction Theorem ---

theorem crt_bridge (p e : ℕ) (hp : p.Prime)
  (h_p3 : p % 3 = 1) (h_e3 : e % 3 = 1)
  (h_p5 : p % 5 = 1) (h_e5 : e % 5 = 2)
  (h_p7 : p % 7 = 1) (h_e7 : e % 7 = 3)
  (h_p11 : p % 11 = 1) (h_e11 : e % 11 = 5) :
  sigma (p ^ (2 * e)) % UALBF.Manifest.CRT_MODULUS_PRODUCT = 0 := by
  have h3 : 3 ∣ sigma (p ^ (2 * e)) := Nat.dvd_of_mod_eq_zero (mod3_bridge p e hp h_p3 h_e3)
  have h5 : 5 ∣ sigma (p ^ (2 * e)) := Nat.dvd_of_mod_eq_zero (mod5_bridge p e hp h_p5 h_e5)
  have h7 : 7 ∣ sigma (p ^ (2 * e)) := Nat.dvd_of_mod_eq_zero (mod7_bridge p e hp h_p7 h_e7)
  have h11 : 11 ∣ sigma (p ^ (2 * e)) := Nat.dvd_of_mod_eq_zero (mod11_bridge p e hp h_p11 h_e11)

  have hc15 : Nat.Coprime 3 5 := by decide
  have h15 : 15 ∣ sigma (p ^ (2 * e)) := hc15.mul_dvd_of_dvd_of_dvd h3 h5

  have hc105 : Nat.Coprime 15 7 := by decide
  have h105 : 105 ∣ sigma (p ^ (2 * e)) := hc105.mul_dvd_of_dvd_of_dvd h15 h7

  have hc1155 : Nat.Coprime 105 11 := by decide
  have h1155 : 1155 ∣ sigma (p ^ (2 * e)) := hc1155.mul_dvd_of_dvd_of_dvd h105 h11

  have h_prod_eq : UALBF.Manifest.CRT_MODULUS_PRODUCT = 1155 := rfl
  rw [h_prod_eq]
  exact Nat.mod_eq_zero_of_dvd h1155


-- --- FFI Soundness Theorem ---

theorem ualbf_check_crt_soundness_ffi (p : UInt64) (two_e : UInt32) (hp : p.toNat.Prime)
  (_h_even : two_e.toNat % 2 = 0)
  (h_ffi : UALBF.FFI.ualbf_check_crt_impl p two_e = true) :
  sigma (p.toNat ^ (two_e.toNat)) % UALBF.Manifest.CRT_MODULUS_PRODUCT = 0 := by
  unfold UALBF.FFI.ualbf_check_crt_impl at h_ffi
  simp only [Bool.and_eq_true, beq_iff_eq] at h_ffi
  rcases h_ffi with ⟨⟨⟨h_p3_mod, h_e3_mod⟩, ⟨h_p5_mod, h_e5_mod⟩⟩, ⟨⟨h_p7_mod, h_e7_mod⟩, ⟨h_p11_mod, h_e11_mod⟩⟩⟩

  have h_p3 : p.toNat % 3 = 1 := by
    have h_mod_eq : (p % 3).toNat = p.toNat % 3 := rfl
    have h_val : (p % 3).toNat = 1 := by rw [h_p3_mod]; rfl
    rw [←h_mod_eq]
    exact h_val
  have h_e3 : (two_e.toNat / 2) % 3 = 1 := by
    have h_mod_eq : ((two_e / 2) % 3).toNat = (two_e.toNat / 2) % 3 := rfl
    have h_val : ((two_e / 2) % 3).toNat = 1 := by rw [h_e3_mod]; rfl
    rw [←h_mod_eq]
    exact h_val

  have h_p5 : p.toNat % 5 = 1 := by
    have h_mod_eq : (p % 5).toNat = p.toNat % 5 := rfl
    have h_val : (p % 5).toNat = 1 := by rw [h_p5_mod]; rfl
    rw [←h_mod_eq]
    exact h_val
  have h_e5 : (two_e.toNat / 2) % 5 = 2 := by
    have h_mod_eq : ((two_e / 2) % 5).toNat = (two_e.toNat / 2) % 5 := rfl
    have h_val : ((two_e / 2) % 5).toNat = 2 := by rw [h_e5_mod]; rfl
    rw [←h_mod_eq]
    exact h_val

  have h_p7 : p.toNat % 7 = 1 := by
    have h_mod_eq : (p % 7).toNat = p.toNat % 7 := rfl
    have h_val : (p % 7).toNat = 1 := by rw [h_p7_mod]; rfl
    rw [←h_mod_eq]
    exact h_val
  have h_e7 : (two_e.toNat / 2) % 7 = 3 := by
    have h_mod_eq : ((two_e / 2) % 7).toNat = (two_e.toNat / 2) % 7 := rfl
    have h_val : ((two_e / 2) % 7).toNat = 3 := by rw [h_e7_mod]; rfl
    rw [←h_mod_eq]
    exact h_val

  have h_p11 : p.toNat % 11 = 1 := by
    have h_mod_eq : (p % 11).toNat = p.toNat % 11 := rfl
    have h_val : (p % 11).toNat = 1 := by rw [h_p11_mod]; rfl
    rw [←h_mod_eq]
    exact h_val
  have h_e11 : (two_e.toNat / 2) % 11 = 5 := by
    have h_mod_eq : ((two_e / 2) % 11).toNat = (two_e.toNat / 2) % 11 := rfl
    have h_val : ((two_e / 2) % 11).toNat = 5 := by rw [h_e11_mod]; rfl
    rw [←h_mod_eq]
    exact h_val

  have h_pow_eq : two_e.toNat = 2 * (two_e.toNat / 2) := by omega
  rw [h_pow_eq]
  exact crt_bridge p.toNat (two_e.toNat / 2) hp h_p3 h_e3 h_p5 h_e5 h_p7 h_e7 h_p11 h_e11

end UALBF.Engine.CrtTensorBridge
