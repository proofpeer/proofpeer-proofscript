{ pkgs ? (import <nixpkgs> {}).pkgs }:

let
  myemacs =
    with pkgs.emacsPackages; with pkgs.emacsPackagesNg; pkgs.emacsWithPackages
      [ helm-projectile ensime magit paredit tuaregMode ];
in with pkgs;
  pkgs.stdenv.mkDerivation {
    name = "Metis";
    buildInputs = [ myemacs sbt scala hol_light ];
    JAVA_HOME = jdk8;
    JDK_HOME = ''${jdk8}/lib/openjdk'';
    HOLLIGHT_DIR = "${hol_light}";
  }
