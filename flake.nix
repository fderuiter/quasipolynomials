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
