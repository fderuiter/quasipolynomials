import Lake
open Lake DSL

package ualbf {
  moreLinkArgs := #["-L../verification-lib/target/release", "-lverification_lib"]
}

require mathlib from git "https://github.com/leanprover-community/mathlib4.git"

target ffi.o pkg : System.FilePath := do
  let oFile := pkg.buildDir / "c" / "ffi.o"
  let srcJob ← inputFile (pkg.dir / "ffi.c") true
  let flags := #["-I", (← getLeanIncludeDir).toString, "-fPIC"]
  buildO oFile srcJob flags #[] "cc"

extern_lib libleanffi pkg := do
  let name := nameToStaticLib "leanffi"
  let ffiO ← fetch <| pkg.target ``ffi.o
  buildStaticLib (pkg.staticLibDir / name) #[ffiO]

lean_lib UALBF { }

lean_exe validator {
  root := `Validator
}
