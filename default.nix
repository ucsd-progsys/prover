{ fetchgitLocal }:
{ mkDerivation, base, liquid-fixpoint, parsec, stdenv }:
mkDerivation {
  pname = "prover";
  version = "9.9.9.9";
  src = fetchgitLocal ./.;
  isLibrary = true;
  isExecutable = true;
  libraryHaskellDepends = [ base liquid-fixpoint parsec ];
  executableHaskellDepends = [ base liquid-fixpoint parsec ];
  description = "Automatic Prover of Logical Predicates";
  license = stdenv.lib.licenses.gpl2;
}
