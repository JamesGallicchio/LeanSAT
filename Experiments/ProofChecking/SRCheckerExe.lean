/-

A runner for `SRChecker.lean`.

Command-line tool for checking LSR files.

Author: Cayden Codel
Carnegie Mellon University

-/

import Experiments.ProofChecking.SRParser
import Experiments.ProofChecking.SRChecker
import Experiments.ProofChecking.RangeArray

import LeanSAT.Data.Cnf
import LeanSAT.Data.ICnf
import LeanSAT.Data.Literal

open LeanSAT LeanSAT.Model

def printUsage : IO Unit := do
  IO.println "Usage: ./SRChecker <cnf> <lsr> [c]"
  IO.println ""
  IO.println "where"
  IO.println ""
  IO.println "   [c] is an optional argument specifying that <lsr> is in binary compressed format."
  IO.println ""
  IO.println "If no command-line arguments are given, prints this help message."
  IO.println "Reads the CNF and LSR files and checks the LSR proof."

def interpretResult : Except Bool SRState → IO Unit
  | .ok _ => do
    IO.println "c Proof is valid, but did not derive the empty clause."
    IO.println "s VALID"
  | .error true => do
    IO.println "c Proof derived the empty clause"
    IO.println "s VERIFIED UNSAT"
  | .error false => do
    IO.println "c Error or invalid proof"
    IO.println "s INVALID"

partial def main : List String → IO Unit
  | [] => printUsage
  | [_] => printUsage
  | [cnfFile, lsrFile] => do
    let cnfContents ← IO.FS.withFile cnfFile .read (·.readToEnd)
    let (F, nvars) ← IO.ofExcept <| SRParser.parseFormula cnfContents (RangeArray.empty : RangeArray ILit)

    let lsrContents ← IO.FS.withFile lsrFile .read (·.readToEnd)
    let lines := lsrContents.splitOn "\n"
    interpretResult <| lines.foldlM (init := SR.SRState.mk F (PPA.new (nvars * 2)) (PS.new (nvars * 2))) (fun ⟨F, τ, σ⟩ line =>
      match SRParser.parseLSRLine F line with
      | .error _ =>
        -- dbg_trace s!"Error: {str}"
        .error false
      | .ok (_, F, pl) =>
        -- dbg_trace s!"Parsed line with id {id}"
        match pl with
        | .inl addLine =>
          SR.checkLine ⟨F, τ, σ⟩ addLine
        | .inr delLine =>
          match SR.consumeDeletionLine F delLine with
          | .ok F => .ok ⟨F, τ, σ⟩
          | .error b => .error b)
  | [cnfFile, lsrFile, "c"] => do
    let cnfContents ← IO.FS.withFile cnfFile .read (·.readToEnd)
    let (F, nvars) ← IO.ofExcept <| SRParser.parseFormula cnfContents (RangeArray.empty : RangeArray ILit)

    let bytes ← IO.FS.withFile lsrFile .read (·.readBinToEnd)
    let b_size := bytes.size
    let rec loop (index : Nat) : SR.SRState → Except Bool SR.SRState
    | ⟨F, τ, σ⟩ => do
      if index < b_size then
        match SRParser.parseLSRLineBinary F bytes index with
        | .error _ =>
          -- dbg_trace s!"Error: {str}"
          .error false
        | .ok (index, _, F, pl) =>
          -- dbg_trace s!"Parsed line with id {id}"
          --let F := F.commitUntil (id - 1)
          match pl with
          | .inl addLine =>
            match SR.checkLine ⟨F, τ, σ⟩ addLine with
            | .ok st => loop index st
            | .error b => .error b
          | .inr delLine =>
            match SR.consumeDeletionLine F delLine with
            | .ok F => loop index ⟨F, τ, σ⟩
            | .error b => .error b
      else .error false
    interpretResult <| loop 0 (SR.SRState.mk F (PPA.new (nvars * 2)) (PS.new (nvars * 2)))

  | _ => printUsage
