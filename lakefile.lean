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

-- Note: `mathlib` and `std` are obtained transitively so that the versions all match up
require leancolls from git "https://github.com/JamesGallicchio/LeanColls.git" @ "main"
