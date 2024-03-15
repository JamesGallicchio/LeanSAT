import Experiments.OldExamples.Encoding.Akari
import Experiments.OldExamples.Encoding.NumberLink
import Experiments.OldExamples.Encoding.Yajilin

open LeanSAT Examples

/-
The encoding examples require at least one solver present,
which is configured here. If you want to use a different solver,
change the instance declaration here and recompile.
-/

instance : Solver IO := Solver.Impl.DimacsCommand "cadical"

def mains :=
  [ ("Akari", Akari.main)
  , ("NumberLink", NumberLink.main)
  , ("Yajilin", Yajilin.main)
  ]

def main (args : List String) : IO UInt32 := do
  IO.println "Example:"
  for (i, name, _) in mains.enum do
    IO.println s!"({i}) {name}"
  IO.print "Select example: "
  let selection ← (←IO.getStdin).getLine
  let selection ← IO.ofExcept <|
    selection.trim.toNat?.expectSome fun () => s!"Expected a number, got {selection}"
  if _h : selection < mains.length then
    mains[selection].2

  return 0
