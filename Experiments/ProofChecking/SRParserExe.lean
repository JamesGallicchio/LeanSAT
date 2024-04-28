/-

An executable for `SRParser.lean`.

A simple command-line tool for reading in CNF/LSR files.
What's read is echoed back to `stdout`.

Author: Cayden Codel
Carnegie Mellon University

-/

import Experiments.ProofChecking.SRParser
import Experiments.ProofChecking.RangeArray

import LeanSAT.Data.Cnf
import LeanSAT.Data.ICnf
import LeanSAT.Data.Literal

open LeanSAT LeanSAT.Model

def printUsage : IO Unit := do
  IO.println "Usage: ./SRParserExe <file-path> [cnf | lsr | clsr]"
  IO.println ""
  IO.println "where"
  IO.println ""
  IO.println "  cnf: parses a CNF file."
  IO.println "  lsr: parses an LSR file (default behavior)."
  IO.println "  clsr: parses a compressed binary LSR file."
  IO.println ""
  IO.println "If no command-line arguments are given, prints this help message."
  IO.println "Parses the CNF/LSR file and echoes it to stdout."
  IO.println "Note that the output will be in text format, even if the input is binary."

def echoCnf (filePath : String) : IO Unit := do
  let contents ← IO.FS.withFile filePath .read (·.readToEnd)
  match SRParser.parseFormula contents (RangeArray.empty : RangeArray ILit) with
  | .error str => IO.println str
  | .ok (F, nvars) =>
    IO.println s!"p cnf {nvars} {F.size}"
    let rec loop (i : Nat) : IO Unit := do
      if i < F.size then
        IO.print <| F.foldl_index (fun str lit => str ++ s!"{lit} ") "" i
        IO.println "0"
        loop (i + 1)
    termination_by F.size - i
    loop 0

@[specialize]
def echoLSRLine (F : RangeArray ILit) (id : Nat) (line : SR.SRAdditionLine) : IO Unit := do
  let usize := F.usize
  let F := F.commit

  -- Print the line back
  if usize > 0 then
    IO.print <| F.foldl_index (fun str lit => str ++ s!"{lit} ") "" (F.size - 1)

  if line.witnessLits.size > 1 ∨ line.witnessMaps.size > 0 then
    --IO.print s!"WEVE DETERMINED THAT {line.witnessLits.size} and {line.witnessMaps.size} "
    IO.print <| line.witnessLits.foldl (fun str lit => str ++ s!"{lit} ") ""

    if line.witnessMaps.size > 0 then
      IO.print s!"{line.witnessLits[0]!} "
      IO.print <| line.witnessMaps.foldl (fun str lit => str ++ s!"{lit} ") ""

  IO.print "0 "

  if line.upHints.size > 0 then
    IO.print <| line.upHints.foldl (fun str hint => str ++ s!"{hint + 1} ") ""

  if line.ratHintIndexes.size > 0 then
    IO.print <| Fin.foldl line.ratHintIndexes.size (init := "") (fun str idx =>
      let str := str ++ s!"-{line.ratHintIndexes.get idx + 1} "
      (line.ratHints.get ⟨idx.val, by
        rcases idx with ⟨idx, hlt⟩
        rwa [line.ratSizesEq] at hlt⟩).foldl (fun str hint =>
        str ++ s!"{hint + 1} ") str)
  IO.println "0"

def echoLSR (filePath : String) : IO Unit := do
  let contents ← IO.FS.withFile filePath .read (·.readToEnd)
  let lines := contents.splitOn "\n"
  lines.foldlM (fun _ line => do
    -- Skip empty lines
    if line.length > 0 then
      match SRParser.parseLSRLine (RangeArray.empty : RangeArray ILit) line with
      | .error str =>
        IO.println s!"Error encountered: {str}"
      | .ok ⟨id, F, pl⟩ =>
        IO.print s!"{id} "
        match pl with
        | .inl addLine => echoLSRLine F id addLine
        | .inr delLine =>
          IO.print "d "
          IO.print <| delLine.clauses.foldl (fun str clause => str ++ s!"{clause + 1} ") ""
          IO.println "0") ()

partial def echoLSRBinary (filePath : String) : IO Unit := do
  let contents ← IO.FS.withFile filePath .read (·.readBinToEnd)
  let rec loop (index : Nat) : IO Unit :=
    if index < contents.size then
      match SRParser.parseLSRLineBinary (RangeArray.empty : RangeArray ILit) contents index with
      | .error str => IO.println str
      | .ok (index, id, F, pl) => do
        IO.print s!"{id} "
        match pl with
        | .inl addLine => echoLSRLine F id addLine
        | .inr delLine =>
          IO.print "d "
          IO.print <| delLine.clauses.foldl (fun str clause => str ++ s!"{clause + 1} ") ""
          IO.println "0"
        loop index
    else
      return
  loop 0

partial def main : List String → IO Unit
  | [] => printUsage
  | filePath :: args => do
    match args with
    | [] => echoLSR filePath
    | ["cnf"] => echoCnf filePath
    | ["lsr"] => echoLSR filePath
    | ["clsr"] => echoLSRBinary filePath
    | _ => printUsage
