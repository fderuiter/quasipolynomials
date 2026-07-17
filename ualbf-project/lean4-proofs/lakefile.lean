import Lake
open System Lake DSL

package ualbf where
  moreLinkArgs := #["-L../verification-lib/target/release", "-lverification_lib"]

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.30.0"
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"

input_file ffi.c where
  path := "ffi.c"
  text := true

target ffi.o pkg : FilePath := do
  let oFile := pkg.buildDir / "c" / "ffi.o"
  let srcJob ← ffi.c.fetch
  let flags := #["-I", (← getLeanIncludeDir).toString, "-fPIC"]
  buildO oFile srcJob flags #[] "cc"

target libleanffi pkg : FilePath := do
  let name := nameToStaticLib "leanffi"
  let ffiO ← ffi.o.fetch
  buildStaticLib (pkg.staticLibDir / name) #[ffiO]

lean_lib UALBF where
  moreLinkObjs := #[libleanffi]

lean_exe validator where
  root := `Validator
  moreLinkObjs := #[libleanffi]
