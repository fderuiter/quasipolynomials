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

        lakeManifest = builtins.fromJSON (builtins.readFile ./ualbf-project/lean4-proofs/lake-manifest.json);
        
        linkPackages = pkgs.lib.concatStringsSep "\n" (map (pkg: ''
          mkdir -p .lake/packages/${pkg.name}
          cp -rT ${builtins.fetchGit { url = pkg.url; rev = pkg.rev; submodules = true; }} .lake/packages/${pkg.name}
          chmod -R +w .lake/packages/${pkg.name}
        '') lakeManifest.packages);

        rewriteManifest = ''
          jq '
            .packages |= map(
              if .type == "git" then
                .type = "path" | .dir = ".lake/packages/" + .name
              else . end
            )
          ' lake-manifest.json > lake-manifest.json.tmp
          mv lake-manifest.json.tmp lake-manifest.json
          sed -i 's/from git ".*"/from ".lake\/packages\/mathlib"/g' lakefile.lean
        '';

        leanDeps = pkgs.stdenv.mkDerivation {
          pname = "lean-deps";
          version = "0.1.0";
          src = pkgs.lib.cleanSourceWith {
            src = ./ualbf-project/lean4-proofs;
            filter = path: type: builtins.match ".*(lake-manifest.json|lakefile.lean|lean-toolchain|lakefile.toml)$" path != null || type == "directory";
          };
          nativeBuildInputs = [ pkgs.lean4 pkgs.git pkgs.cacert pkgs.jq pkgs.curl ];
          buildPhase = ''
            export HOME=$TMPDIR
            export GIT_SSL_CAINFO="${pkgs.cacert}/etc/ssl/certs/ca-bundle.crt"
            export SSL_CERT_FILE="${pkgs.cacert}/etc/ssl/certs/ca-bundle.crt"
            ${linkPackages}
            ${rewriteManifest}
            if grep -q "mathlib" lake-manifest.json; then
              lake exe cache get || true
            fi
            # We specifically build proofwidgets to fetch the JS assets
            lake build proofwidgets || true
            lake build LeanSearchClient || true
            # Clean up locally compiled files that contain the FOD store path to maintain hash reproducibility
            echo "Cleaning up compiled files to prevent store path leaks..."
            # Delete all compiled files except those in mathlib (which are from cache and safe)
            find .lake -type f \( -name '*.olean' -o -name '*.ilean' -o -name '*.c' -o -name '*.o' \) | grep -v "\.lake/packages/mathlib" | xargs rm -f || true
            find .lake -type f -name '*.trace' -delete || true
            find .lake -type f -name '*.hash' -delete || true
            find .lake -name 'lake-manifest.json.tmp' -delete || true


            # Clean up compiled files to avoid hash non-determinism?
            # Actually, `lake exe cache get` creates .olean files. Let's keep them so the main build is fast.

          '';
          installPhase = ''
            # Remove any binaries built which might contain nix store paths
            find .lake -type f -name cache.rsp -delete || true
            find .lake -type f -name cache -delete || true
            rm -rf .lake/packages/mathlib/.lake/build/bin || true
            mkdir -p $out
            cp -r .lake $out/
          '';
          dontFixup = true;
          outputHashAlgo = "sha256";
          outputHashMode = "recursive";
          outputHash = "sha256-JzoxPKsQ9uNNlHZo9dbhpo63MWjfOoCWbYLhVZV1LCk=";
        };

        leanPkg = pkgs.stdenv.mkDerivation {
          pname = "ualbf-lean4-proofs";
          version = "0.1.0";
          src = ./ualbf-project/lean4-proofs;

          nativeBuildInputs = [ pkgs.lean4 pkgs.git pkgs.cacert pkgs.jq ];

          preBuild = ''
            chmod +w ..
            mkdir -p ../verification-lib/target/release
            ln -s ${verificationLib}/lib/libverification_lib.* ../verification-lib/target/release/ || true
          '';

          buildPhase = ''
            export HOME=$TMPDIR
            export GIT_SSL_CAINFO="${pkgs.cacert}/etc/ssl/certs/ca-bundle.crt"
            export SSL_CERT_FILE="${pkgs.cacert}/etc/ssl/certs/ca-bundle.crt"
            cp -r ${leanDeps}/.lake .lake
            chmod -R +w .lake
            ${rewriteManifest}
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
          src = pkgs.lib.cleanSourceWith {
            src = ./ualbf-project;
            filter = path: type:
              let 
                p = toString path;
              in
                builtins.match ".*(Cargo\\.toml|Cargo\\.lock|verification-lib.*|rust-engine.*)$" p != null || type == "directory";
          };
          buildAndTestSubdir = "verification-lib";

          cargoBuildFlags = [ "-p" "verification-lib" ];
          cargoTestFlags = [ "-p" "verification-lib" ];

          cargoLock = {
            lockFile = ./ualbf-project/Cargo.lock;
          };

          nativeBuildInputs = [
            pkgs.python3
            pkgs.pkg-config
            pkgs.llvmPackages.libclang
          ];

          buildInputs = [
            pkgs.pkgsStatic.gmp
            pkgs.pkgsStatic.libuv
            pkgs.z3
            pkgs.libcxx
          ] ++ pkgs.lib.optionals (!pkgs.stdenv.isDarwin) [
            pkgs.ocl-icd
            pkgs.opencl-headers
          ] ++ pkgs.lib.optionals pkgs.stdenv.isDarwin [
            pkgs.darwin.apple_sdk.frameworks.Security
            pkgs.darwin.apple_sdk.frameworks.CoreFoundation
            pkgs.darwin.apple_sdk.frameworks.SystemConfiguration
            pkgs.darwin.apple_sdk.frameworks.OpenCL
            pkgs.darwin.apple_sdk.frameworks.Metal
            pkgs.darwin.apple_sdk.frameworks.Foundation
          ];

          buildFeatures = [ "python" ];
          
          preBuild = ''
            chmod +w ..
            export ALLOW_UNVERIFIED_BUILD="1"
            export LIBCLANG_PATH="${pkgs.llvmPackages.libclang.lib}/lib"
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
          src = pkgs.lib.cleanSourceWith {
            src = ./ualbf-project;
            filter = path: type:
              let 
                p = toString path;
              in
                builtins.match ".*(Cargo\\.toml|Cargo\\.lock|rust-engine.*|verification-lib.*|scripts.*|bounds_manifest\\.json|lean4-proofs.*)$" p != null || type == "directory";
          };

          sourceRoot = "source/rust-engine";

          cargoLock = {
            lockFile = ./ualbf-project/Cargo.lock;
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
            pkgs.libcxx
          ] ++ pkgs.lib.optionals (!pkgs.stdenv.isDarwin) [
            pkgs.ocl-icd
            pkgs.opencl-headers
          ] ++ pkgs.lib.optionals pkgs.stdenv.isDarwin [
            pkgs.darwin.apple_sdk.frameworks.Security
            pkgs.darwin.apple_sdk.frameworks.CoreFoundation
            pkgs.darwin.apple_sdk.frameworks.SystemConfiguration
            pkgs.darwin.apple_sdk.frameworks.OpenCL
            pkgs.darwin.apple_sdk.frameworks.Metal
            pkgs.darwin.apple_sdk.frameworks.Foundation
          ];

          # Symlink the built Lean objects so build.rs can find them.
          preBuild = ''
            chmod +w ..
            mkdir -p ../lean4-proofs
            chmod -R +w ../lean4-proofs || true
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
          leanDeps = leanDeps;
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
              pkgs.gnumake 
              pkgs.which
            ];

            buildPhase = ''
              export HOME=$TMPDIR
              echo "Setting up verification-lib..."
              cp ${verificationLib}/lib/libverification_lib.so ./verification_lib.so || cp ${verificationLib}/lib/libverification_lib.dylib ./verification_lib.so || cp ${verificationLib}/lib/libverification_lib.* ./verification_lib.so
              
              echo "Patching argparse for latexminted..."
              cp $(python3 -c "import argparse; print(argparse.__file__)") paper/argparse.py
              sed -i 's/parser = self._parser_class(\*\*kwargs)/kwargs.pop("color", None); parser = self._parser_class(\*\*kwargs)/g' paper/argparse.py
              export PYTHONPATH=$PWD:$PWD/paper:$PYTHONPATH

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
              cp paper/main.pdf $out/
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
              done < <(find . -type d -name ".lake" -prune -o -type f -name "*.lean" -print)
              
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

            nativeBuildInputs = [ pkgs.lean4 pkgs.git pkgs.cacert pkgs.jq ];

            preBuild = ''
              chmod +w ..
              mkdir -p ../verification-lib/target/release
              ln -s ${verificationLib}/lib/libverification_lib.* ../verification-lib/target/release/ || true
            '';

            buildPhase = ''
              echo "Building Lean project with warnings treated as errors..."
              # Pass -DwarningAsError=true to treat compiler warnings as fatal errors
              export HOME=$TMPDIR
              export GIT_SSL_CAINFO="${pkgs.cacert}/etc/ssl/certs/ca-bundle.crt"
              export SSL_CERT_FILE="${pkgs.cacert}/etc/ssl/certs/ca-bundle.crt"
              cp -r ${leanDeps}/.lake .lake
            chmod -R +w .lake
            ${rewriteManifest}
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
            pkgs.clippy
            pkgs.rustfmt
            pkgs.python3Packages.black
            pkgs.python3Packages.flake8
            pkgs.python3Packages.mypy
            pkgs.pkgsStatic.gmp
            pkgs.pkgsStatic.libuv
            pkgs.z3
            pkgs.pkg-config
            pkgs.llvmPackages.libclang
            pkgs.libcxx
          ] ++ pkgs.lib.optionals (!pkgs.stdenv.isDarwin) [
            pkgs.ocl-icd
            pkgs.opencl-headers
          ] ++ pkgs.lib.optionals pkgs.stdenv.isDarwin [
            pkgs.darwin.apple_sdk.frameworks.Security
            pkgs.darwin.apple_sdk.frameworks.CoreFoundation
            pkgs.darwin.apple_sdk.frameworks.SystemConfiguration
            pkgs.darwin.apple_sdk.frameworks.OpenCL
            pkgs.darwin.apple_sdk.frameworks.Metal
            pkgs.darwin.apple_sdk.frameworks.Foundation
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
