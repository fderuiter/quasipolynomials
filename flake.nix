{
  description = "UALBF Nix-Based Reproducibility Suite";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };

        leanPkg = pkgs.stdenv.mkDerivation {
          pname = "ualbf-lean4-proofs";
          version = "0.1.0";
          src = ./ualbf-project/lean4-proofs;

          nativeBuildInputs = [ pkgs.lean4 ];

          buildPhase = ''
            lake build
          '';

          installPhase = ''
            mkdir -p $out
            cp -r .lake $out/
          '';
        };

        ualbfEngine = pkgs.rustPlatform.buildRustPackage {
          pname = "ualbf-engine";
          version = "0.1.0";
          src = ./ualbf-project;

          sourceRoot = "ualbf-project/rust-engine";

          cargoLock = {
            lockFile = ./ualbf-project/rust-engine/Cargo.lock;
          };

          nativeBuildInputs = [
            pkgs.pkg-config
            pkgs.lean4
            pkgs.llvmPackages.libclang
          ];

          buildInputs = [
            pkgs.pkgsStatic.gmp
            pkgs.pkgsStatic.libuv
            pkgs.z3
          ] ++ pkgs.lib.optionals pkgs.stdenv.isDarwin [
            pkgs.darwin.apple_sdk.frameworks.Security
            pkgs.darwin.apple_sdk.frameworks.CoreFoundation
            pkgs.darwin.apple_sdk.frameworks.SystemConfiguration
          ];

          # Symlink the built Lean objects so build.rs can find them.
          preBuild = ''
            chmod -R +w ../lean4-proofs
            ln -s ${leanPkg}/.lake ../lean4-proofs/.lake
            export LEAN_SYSROOT="${pkgs.lean4}"
            export LIBCLANG_PATH="${pkgs.llvmPackages.libclang.lib}/lib"
          '';
        };

      in
      {
        packages = {
          default = ualbfEngine;
          engine = ualbfEngine;
          lean = leanPkg;
        };

        checks = {
          rust-literals = pkgs.stdenv.mkDerivation {
            pname = "rust-literals-check";
            version = "0.1.0";
            src = ./ualbf-project;

            nativeBuildInputs = [ pkgs.python3 ];

            buildPhase = ''
              echo "Running Rust literal validation..."
              python3 scripts/check_literals.py
            '';

            installPhase = ''
              mkdir -p $out
              touch $out/success
            '';
          };

          latex-paper = pkgs.stdenv.mkDerivation {
            pname = "latex-paper-check";
            version = "0.1.0";
            src = ./ualbf-project;

            nativeBuildInputs = [ 
              pkgs.python3 
              pkgs.python3Packages.pygments 
              (if pkgs ? texliveFull then pkgs.texliveFull else pkgs.texlive.combined.scheme-full)
              pkgs.gnumake pkgs.which 
            ];

            buildPhase = ''
              echo "Compiling LaTeX paper..."
              cd paper
              make all
            '';

            installPhase = ''
              mkdir -p $out
              cp paper/main.pdf $out/ || true
              touch $out/success
            '';
          };

          formatting = pkgs.stdenv.mkDerivation {
            pname = "lean-formatting-check";
            version = "0.1.0";
            src = ./ualbf-project/lean4-proofs;
            
            nativeBuildInputs = [ pkgs.gawk pkgs.diffutils pkgs.coreutils ];
            
            buildPhase = ''
              echo "Checking for trailing whitespace, tabs, and missing newlines..."
              BAD_FILES=0
              
              while IFS= read -r file; do
                # Process the file to fix trailing spaces, convert tabs to spaces, and ensure a trailing newline
                awk '
                  { 
                    sub(/[ \t]+$/, "");  # Remove trailing whitespace
                    gsub(/\t/, "    ");  # Replace tabs with 4 spaces
                    print
                  }
                ' "$file" > "$file.fmt"
                
                # Check for differences
                if ! diff -u "$file" "$file.fmt"; then
                  echo "Formatting error in $file"
                  BAD_FILES=1
                fi
              done < <(find . -type f -name "*.lean")
              
              if [ $BAD_FILES -ne 0 ]; then
                echo "Formatting checks failed. Please fix the files listed above."
                exit 1
              fi
              
              echo "All files formatted correctly!"
            '';
            
            installPhase = ''
              mkdir -p $out
              touch $out/success
            '';
          };

          warnings = pkgs.stdenv.mkDerivation {
            pname = "ualbf-lean4-warnings-check";
            version = "0.1.0";
            src = ./ualbf-project/lean4-proofs;

            nativeBuildInputs = [ pkgs.lean4 ];

            buildPhase = ''
              echo "Building Lean project with warnings treated as errors..."
              # Pass -DwarningAsError=true to treat compiler warnings as fatal errors
              lake build -- -DwarningAsError=true
            '';

            installPhase = ''
              mkdir -p $out
              touch $out/success
            '';
          };
        };

        devShells.default = pkgs.mkShell {
          buildInputs = [
            pkgs.lean4
            pkgs.rustc
            pkgs.cargo
            pkgs.pkgsStatic.gmp
            pkgs.pkgsStatic.libuv
            pkgs.z3
            pkgs.pkg-config
            pkgs.llvmPackages.libclang
          ] ++ pkgs.lib.optionals pkgs.stdenv.isDarwin [
            pkgs.darwin.apple_sdk.frameworks.Security
            pkgs.darwin.apple_sdk.frameworks.CoreFoundation
            pkgs.darwin.apple_sdk.frameworks.SystemConfiguration
          ];

          LEAN_SYSROOT = "${pkgs.lean4}";
          LIBCLANG_PATH = "${pkgs.llvmPackages.libclang.lib}/lib";

          shellHook = ''
            export LEAN_SYSROOT="${pkgs.lean4}"
            export LIBCLANG_PATH="${pkgs.llvmPackages.libclang.lib}/lib"
          '';
        };
      }
    );
}
