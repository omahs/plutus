# This file is part of the IOGX template and is documented at the link below:
# https://www.github.com/input-output-hk/iogx#32-nixhaskellnix

{ system, ... }:

{
  supportedCompilers = [ "ghc8107" "ghc927" "ghc961" ];


  defaultCompiler = "ghc927";


  enableCombinedHaddock = system == "x86_64-linux";


  projectPackagesWithHaddock = [ ];


  combinedHaddockPrologue = ''
    = Combined documentation for all the public Plutus libraries

    == Handy module entrypoints

      * "PlutusTx": Compiling Haskell to PLC (Plutus Core; on-chain code).
      * "PlutusTx.Prelude": Haskell prelude replacement compatible with PLC.
      * "PlutusCore": Programming language in which scripts on the Cardano blockchain are written.
      * "UntypedPlutusCore": On-chain Plutus code.
  '';
}
