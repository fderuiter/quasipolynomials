-- AUTO-GENERATED from schema_manifest.json. DO NOT EDIT.

import Mathlib.Data.Nat.Basic
import Lean.Data.Json

namespace UALBF.Engine

structure SearchState where
  n_l : Nat
  s_l : Nat
  last_idx : Nat
  factors : Array UInt64
  sigma_factors : Array Nat
  sigma_factors_u64 : Array UInt64
  active_mask : Array UInt64
deriving Inhabited, Repr, FromJson, ToJson

end UALBF.Engine
