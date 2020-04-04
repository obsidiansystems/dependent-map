{ pkgs ? import (builtins.fetchTarball {
    url = https://releases.nixos.org/nixos/20.03/nixos-20.03beta1064.4dc8447c55f/nixexprs.tar.xz;
    sha256 = "1ni9xfslaq09kh2xzkbz1hv1bfzcvdc6jz5pnsq61cgis8r4fwr8";
  }) {}
}:
let
  haskellPkgs = pkgs.haskellPackages.extend (self: super: {
    dependent-map = self.callCabal2nix "dependent-map" ./. {};
    dependent-sum = self.callHackageDirect {
      pkg = "dependent-sum";
      ver = "0.7.1.0";
      sha256 = "0jjdjhkhny8hiz9q17bqdgncca8gb0nqdnqz3xpwa3g2g0qisrp0";
    } {};
  });
in {
  inherit (haskellPkgs) dependent-map;
}
