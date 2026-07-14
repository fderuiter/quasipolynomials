import UALBF.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Factorization.Basic
import UALBF.FFI

namespace UALBF.Engine.Mod5Bridge

open UALBF

theorem sigma_p_mod_5 (p e : ℕ) (hp : p.Prime) (hp1 : p % 5 = 1) :
  (sigma (p ^ (2 * e)) : ZMod 5) = (2 * e + 1 : ℕ) := sorry

theorem mod5_bridge (p e : ℕ) (hp : p.Prime)
  (h_p : p % 5 = 1) (h_e : e % 5 = 2) :
  sigma (p ^ (2 * e)) % 5 = 0 := sorry

theorem ualbf_check_mod_5_soundness_ffi (p : UInt64) (two_e : UInt32) (hp : p.toNat.Prime)
  (_h_even : two_e.toNat % 2 = 0)
  (h_ffi : UALBF.FFI.ualbf_check_mod_5_impl p two_e = true) :
  sigma (p.toNat ^ (two_e.toNat)) % 5 = 0 := by
  unfold UALBF.FFI.ualbf_check_mod_5_impl at h_ffi
  simp only [Bool.and_eq_true, beq_iff_eq] at h_ffi
  rcases h_ffi with ⟨h_p_mod, h_e_mod⟩
  have h_p : p.toNat % 5 = 1 := by
    have h_mod_eq : (p % 5).toNat = p.toNat % 5 := rfl
    have h_val : (p % 5).toNat = 1 := by rw [h_p_mod]; rfl
    rw [←h_mod_eq]
    exact h_val
  have h_e : (two_e.toNat / 2) % 5 = 2 := by
    have h_mod_eq : ((two_e / 2) % 5).toNat = (two_e.toNat / 2) % 5 := rfl
    have h_val : ((two_e / 2) % 5).toNat = 2 := by rw [h_e_mod]; rfl
    rw [←h_mod_eq]
    exact h_val
  have h_pow_eq : two_e.toNat = 2 * (two_e.toNat / 2) := by omega
  rw [h_pow_eq]
  exact mod5_bridge p.toNat (two_e.toNat / 2) hp h_p h_e

end UALBF.Engine.Mod5Bridge
