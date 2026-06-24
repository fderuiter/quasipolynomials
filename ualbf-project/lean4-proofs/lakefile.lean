import Lake
open Lake DSL

package ualbf {
  -- Link the pre-built Rust FFI static library.
  -- The Rust engine must be compiled first via `cargo build --release`
  -- in the rust-engine/ directory before running `lake build`.
}

require mathlib from git "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib UALBF { }

lean_exe validator {
  root := `Validator
}
