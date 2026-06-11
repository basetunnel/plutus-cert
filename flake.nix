{
  # pin to 24.11
  inputs.nixpkgs.url = "github:nixos/nixpkgs/5b35d248e9206c1f3baf8de6a7683fee126364aa";

  outputs = inputs : {
    devShells.x86_64-linux.default =
      let pkgs = inputs.nixpkgs.legacyPackages.x86_64-linux;
      in
      pkgs.mkShell {
        buildInputs = with pkgs; [
          coq
          coqPackages.mathcomp
          coqPackages.ExtLib
          coqPackages.QuickChick
          coqPackages.equations
          coqPackages.coq-lsp
          python3 # for coqtail plugin in vim
          ];
      };
  };
}
