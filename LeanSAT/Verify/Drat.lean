import LeanSAT.CNF

namespace LeanSAT

inductive DratStep
| Add (c : Clause)
| Delete (c : Clause)

def DratProof := List DratStep

def validateProof (f : Formula) (pf : DratProof) : Bool :=
  sorry