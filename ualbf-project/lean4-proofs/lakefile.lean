import Lake
open Lake DSL

package ualbf { }

require mathlib from git "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib UALBF {
  -- Compile all modules to native .o files so we can link them from Rust
  precompileModules := true
}
