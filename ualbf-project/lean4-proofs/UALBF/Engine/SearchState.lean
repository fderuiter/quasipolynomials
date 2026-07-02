-- AUTO-GENERATED from schema_manifest.json. DO NOT EDIT.

import Mathlib.Data.Nat.Basic
import Lean.Data.Json
import UALBF.FFI

namespace UALBF.Engine

structure SearchState where
  n_l : Nat
  s_l : Nat
  last_idx : Nat
  factors : Array UInt64
  sigma_factors : Array Nat
  sigma_factors_u64 : Array UInt64
  active_mask : Array UInt64
deriving Inhabited, Repr, Lean.FromJson, Lean.ToJson

structure SearchStateTransport where
  n_l : UALBF.FFI.U512
  s_l : UALBF.FFI.U512
  last_idx : Nat
  factors : Array UInt64
  sigma_factors : Array UALBF.FFI.U512
  sigma_factors_u64 : Array UInt64
  active_mask : Array UInt64

noncomputable instance : Inhabited SearchStateTransport where
  default := {
    n_l := default,
    s_l := default,
    last_idx := default,
    factors := default,
    sigma_factors := default,
    sigma_factors_u64 := default,
    active_mask := default
  }

noncomputable def SearchStateTransport.toNative (t : SearchStateTransport) : SearchState := {
  n_l := UALBF.FFI.fromU512 t.n_l,
  s_l := UALBF.FFI.fromU512 t.s_l,
  last_idx := t.last_idx,
  factors := t.factors,
  sigma_factors := t.sigma_factors.map UALBF.FFI.fromU512,
  sigma_factors_u64 := t.sigma_factors_u64,
  active_mask := t.active_mask,
}

end UALBF.Engine
