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

          nativeBuildInputs = [ pkgs.lean4 pkgs.git pkgs.cacert ];

          buildPhase = ''
            lake build
          '';

          installPhase = ''
            mkdir -p $out
            cp -r .lake $out/
          '';
        };


        verificationLib = pkgs.rustPlatform.buildRustPackage {
          pname = "verification-lib";
          version = "0.1.0";
          src = ./ualbf-project;
          sourceRoot = "ualbf-project/verification-lib";

          cargoLock = {
            lockFile = ./ualbf-project/Cargo.lock;
          };

          postPatch = ''
            cp ../Cargo.lock .
          '';

          nativeBuildInputs = [ pkgs.python3 ];
          buildFeatures = [ "python" ];
          
          preBuild = ''
            chmod +w ..
          '';

          installPhase = ''
            mkdir -p $out/lib
            find target -name "libverification_lib.*" -exec cp {} $out/lib/ \; || true
            find ../target -name "libverification_lib.*" -exec cp {} $out/lib/ \; || true
          '';
        };

        ualbfEngine = pkgs.rustPlatform.buildRustPackage {
          pname = "ualbf-engine";
          version = "0.1.0";
          src = ./ualbf-project;

          sourceRoot = "ualbf-project/rust-engine";

          cargoLock = {
            lockFile = ./ualbf-project/Cargo.lock;
          };

          postPatch = ''
            cp ../Cargo.lock .
          '';

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
            chmod +w ..
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
            src = ./.;

            nativeBuildInputs = [ pkgs.python3 ];

            buildPhase = ''
              echo "Running Rust literal validation..."
              cd ualbf-project
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
              pkgs.gnumake 
              pkgs.which
            ];

            buildPhase = ''
              echo "Setting up verification-lib..."
              cp ${verificationLib}/lib/libverification_lib.so ./verification_lib.so || cp ${verificationLib}/lib/libverification_lib.dylib ./verification_lib.so || cp ${verificationLib}/lib/libverification_lib.* ./verification_lib.so
              
              echo "Generating dummy certificate..."
              python3 -c '
import json, hashlib
with open("proof_manifest.json", "rb") as f:
    manifest_hash = hashlib.sha256(f.read()).hexdigest()
with open("bounds_manifest.json", "r") as f:
    bounds = json.load(f)
cert = {
    "manifest_hash": manifest_hash,
    "verified_logic_hash": "dummy",
    "telemetry": {
        "phase2_execution_time_ms": 1000,
        "total_branches_searched": 10,
        "abundance_pruned": 0,
        "raycast_pruned": 0,
        "target_min_log10": bounds["search_bounds"]["target_min_log10"]["value"],
        "target_max_log10": bounds["search_bounds"]["target_max_log10"]["value"],
        "phase1_pruned": 0
    },
    "engine_version": "dummy",
    "commit_hash": "dummy"
}
with open("dummy_cert.json", "w") as f:
    json.dump(cert, f)
'
              export UALBF_CERT_PATH=$PWD/dummy_cert.json
              export UALBF_SKIP_VALIDATION=1
              
              echo "Compiling LaTeX paper..."
              cd paper
              make all
              cd ..
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

            nativeBuildInputs = [ pkgs.lean4 pkgs.git pkgs.cacert ];

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
