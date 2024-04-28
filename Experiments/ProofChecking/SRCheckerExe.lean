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
    interpretResult <| lines.foldlM (init := SR.SRState.mk F (PPA.new (nvars * 2)) (PS.new (nvars * 2))) (fun st line =>
      match SRParser.parseLSRLine st.F line with
      | .error str =>
        dbg_trace s!"Error: {str}"
        .error false
      | .ok (id, F, pl) =>
        let st := { st with F := F.commitUntil (id - 1) }
        match pl with
        | .inl addLine =>
          SR.checkLine st addLine
        | .inr delLine =>
          delLine.clauses.foldlM (fun st clauseId =>
            if hc : clauseId < st.F.size then
              if st.F.isDeletedFin ⟨clauseId, hc⟩ then
                .error false
              else
                .ok { st with F := st.F.deleteFin ⟨clauseId, hc⟩ }
            else .error false) st)
  | [cnfFile, lsrFile, "c"] => do
    let cnfContents ← IO.FS.withFile cnfFile .read (·.readToEnd)
    let (F, nvars) ← IO.ofExcept <| SRParser.parseFormula cnfContents (RangeArray.empty : RangeArray ILit)

    let bytes ← IO.FS.withFile lsrFile .read (·.readBinToEnd)
    let b_size := bytes.size
    let rec loop (index : Nat) (st : SR.SRState) : Except Bool SR.SRState :=
      if index < b_size then
        match SRParser.parseLSRLineBinary st.F bytes index with
        | .error str =>
          dbg_trace s!"Error: {str}"
          .error false
        | .ok (index, id, F, pl) =>
          let st := { st with F := F.commitUntil (id - 1) }
          match pl with
          | .inl addLine =>
            match SR.checkLine st addLine with
            | .ok st => loop index st
            | .error b => .error b
          | .inr delLine =>
            delLine.clauses.foldlM (fun st clauseId =>
              if hc : clauseId < st.F.size then
                if st.F.isDeletedFin ⟨clauseId, hc⟩ then
                  .error false
                else
                  .ok { st with F := st.F.deleteFin ⟨clauseId, hc⟩ }
              else .error false) st
      else .error false
    interpretResult <| loop 0 (SR.SRState.mk F (PPA.new (nvars * 2)) (PS.new (nvars * 2)))

  | _ => printUsage
