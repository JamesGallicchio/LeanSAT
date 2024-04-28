import Lake
open Lake DSL

package «lean-sat»

@[default_target]
lean_lib LeanSAT {
  globs := #[.andSubmodules `LeanSAT]
}

lean_lib Examples {
  globs := #[.submodules `Examples]
}

lean_lib Experiments {
  globs := #[.submodules `Experiments]
}

lean_exe «SRParser» {
  root := `Experiments.ProofChecking.SRParserExe
}

lean_exe «SRChecker» {
  root := `Experiments.ProofChecking.SRCheckerExe
}

lean_exe «FormulaParser» {
  root := `Experiments.ProofChecking.SRParser
}

lean_exe «SRCheckerEfficient» {
  root := `Experiments.ProofChecking.SRParserEfficient
}

lean_exe «StatefulChecker» {
  root := `Experiments.ProofChecking.SRParserStateful
}

lean_exe «BasicChecker» {
  root := `Experiments.ProofChecking.SRCheckerBasic
}


-- Note: `mathlib` and `std` are obtained transitively so that the versions all match up
require leancolls from git "https://github.com/JamesGallicchio/LeanColls.git" @ "main"
