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

        isM4 = system == "aarch64-darwin";

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

          env = pkgs.lib.optionalAttrs isM4 {
            RUSTFLAGS = "-C target-cpu=apple-m4";
            CFLAGS = "-mcpu=m4 -mtune=m4";
          };

          nativeBuildInputs = [
            pkgs.pkg-config
            pkgs.lean4
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
          '';
        };

      in
      {
        packages = {
          default = ualbfEngine;
          engine = ualbfEngine;
          lean = leanPkg;
        };

        devShells.default = pkgs.mkShell (pkgs.lib.optionalAttrs isM4 {
          RUSTFLAGS = "-C target-cpu=apple-m4";
          CFLAGS = "-mcpu=m4 -mtune=m4";
        } // {
          buildInputs = [
            pkgs.lean4
            pkgs.rustc
            pkgs.cargo
            pkgs.pkgsStatic.gmp
            pkgs.pkgsStatic.libuv
            pkgs.z3
            pkgs.pkg-config
          ] ++ pkgs.lib.optionals pkgs.stdenv.isDarwin [
            pkgs.darwin.apple_sdk.frameworks.Security
            pkgs.darwin.apple_sdk.frameworks.CoreFoundation
            pkgs.darwin.apple_sdk.frameworks.SystemConfiguration
          ];

          shellHook = ''
            export LEAN_SYSROOT="${pkgs.lean4}"
          '';
        });
      }
    );
}
