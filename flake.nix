{
  description = "Host-packed TransWarp weight model";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/c1cb7d097cb250f6e1904aacd5f2ba5ffd8a49ce";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs =
    {
      flake-utils,
      nixpkgs,
      ...
    }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        version = "4.32.2";
        release =
          {
            x86_64-linux = {
              platform = "linux";
              hash = "sha256-XyBp5vXbc3gPN0zLSc6OpkmqIKDOvwEWgWdEyZnOcqo=";
            };
            aarch64-linux = {
              platform = "linux_aarch64";
              hash = "sha256-ea7n7JD3IXV9Q/dddf4uZZ3tB/C05fFWnpKsmhg+P4E=";
            };
            x86_64-darwin = {
              platform = "darwin";
              hash = "sha256-LOZGzKnKtZiGMDp0oS46UwZfhRuqx9yGcngswMLTtAg=";
            };
            aarch64-darwin = {
              platform = "darwin_aarch64";
              hash = "sha256-6pnq2WmQG5/kx+e/NQuBKgJJ6aXOogR0pzfAzGR0a8A=";
            };
          }
          .${system};
        leanOverlay = _final: prev: {
          lean4 = prev.stdenv.mkDerivation {
            pname = "lean4";
            inherit version;
            src = prev.fetchurl {
              url = "https://github.com/leanprover/lean4/releases/download/v${version}/lean-${version}-${release.platform}.tar.zst";
              inherit (release) hash;
            };
            nativeBuildInputs = [
              prev.makeWrapper
              prev.zstd
            ]
            ++ prev.lib.optionals prev.stdenv.isLinux [ prev.autoPatchelfHook ]
            ++ prev.lib.optionals prev.stdenv.isDarwin [ prev.fixDarwinDylibNames ];
            buildInputs = prev.lib.optionals prev.stdenv.isLinux [
              prev.stdenv.cc.cc.lib
              prev.gmp
              prev.libuv
              prev.openssl
            ];
            dontConfigure = true;
            dontBuild = true;
            installPhase = ''
              rm -f bin/{clang,ld.lld,llvm-ar}
              ln -s ${prev.clang}/bin/clang bin/clang
              rm -rf include/clang lib/clang
              ln -s ${prev.clang}/resource-root/include include/clang
              mkdir -p "$out"
              cp -R . "$out"
              for executable in lean leanmake leanc lake; do
                if [ -x "$out/bin/$executable" ]; then
                  wrapProgram "$out/bin/$executable" \
                    --prefix PATH : ${prev.lib.makeBinPath [ prev.lld ]}
                fi
              done
            '';
          };
        };
        pkgs = import nixpkgs {
          inherit system;
          overlays = [ leanOverlay ];
        };
      in
      {
        devShells.default = pkgs.mkShell {
          name = "asimov-weights";
          packages = [
            pkgs.lean4
            pkgs.git
          ];
        };
      }
    );
}
