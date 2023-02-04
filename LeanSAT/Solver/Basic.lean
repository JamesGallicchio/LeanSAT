import Std.Data.HashMap
import LeanSAT.CNF

open Std

namespace LeanSAT.Solver

inductive Res
| sat (assn : Assn)
| unsat
| error

instance : ToString Res where
  toString  | .error => "error"
            | .unsat => "unsat"
            | .sat assn => "sat: " ++ toString assn

def Res.isSat : Res → Bool
| .sat _  => true
| _       => false

def Res.getAssn? : Res → Option Assn
| .sat assn => some assn
| _         => none

end Solver

class Solver (m : Type → Type v) [outParam (Monad m)] where
  solve : Formula → m Solver.Res

namespace Solver

class IpasirSolver (S : Type) (m : Type → Type v) [outParam (Monad m)] where
  new : m S
  addClause : Clause → S → m S
  solve : S → m SolveRes

instance [Monad m] [IpasirSolver S m] : Solver m where
  solve f := do
    let s : S ← IpasirSolver.new
    let s ← f.clauses.foldlM (fun s c => IpasirSolver.addClause c s) s
    IpasirSolver.solve s

class ModelCount (m : Type → Type v) [outParam (Monad m)] where
  modelCount : Formula → List Var → m Nat

structure ApproxModelCount.Res where
  mult : Nat
  base : Nat
  pow  : Nat
deriving Inhabited

instance : ToString ApproxModelCount.Res where
  toString | ⟨mult,base,pow⟩ => s!"{mult} * {base}^{pow}"

class ApproxModelCount (m : Type → Type v) [outParam (Monad m)] where
  approxModelCount : Formula → List Var → m ApproxModelCount.Res
