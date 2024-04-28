/-

A parser for the LSR proof format.

Authors: Cayden Codel
Carnegie Mellon University

-/

import LeanSAT.Solver.Dimacs
import Experiments.ProofChecking.RangeArray
import Experiments.ProofChecking.SRCheckerEfficient

import Std

open Std
open LeanSAT.Solver.Dimacs
open LeanSAT LeanSAT.Model ILit

namespace SRParser

open Except
open SR

universe u

/-- The type `L` is a representation of literals over variables of type `ν`. -/
class Formula (F : Type u) where
  empty : F
  addClause : F → IClause → F
  size : F → Nat

instance : Formula (RangeArray ILit) where
  empty := (RangeArray.empty : RangeArray ILit)
  addClause := RangeArray.add
  size := RangeArray.size

instance : Formula (ICnf) where
  empty := #[]
  addClause := (fun F C => Cnf.addClause C F)
  size := Array.size

structure ArrayParseRes where
  vars : Nat
  clauses : ICnf

structure RAPraseRes where
  vars : Nat
  formula : RangeArray ILit

def parseLit (maxVar : Nat) (C : IClause) (s : String) : Except (Except String IClause) IClause := do
  match s.toInt? with
  | none => throw (throw s!"Literal is not a number: {s}")
  | some n =>
    if hn : n = 0 then
      throw (return C)
    else
      if n.natAbs > maxVar then
        throw (throw s!"Literal {n} is greater than the maximum variable {maxVar}")
      else
        if n < 0 then
          return C.push ⟨n, hn⟩
        else
          return C.push ⟨n, hn⟩

def parseClause {α : Type} [Formula α] (maxVar : Nat) (F : α) (s : String) : Except String α :=
  match s.splitOn " " |>.foldlM (parseLit maxVar) #[] with
  | ok _ => throw "Zero not encountered on this line"
  | error e => return Formula.addClause F (← e)

-- Parses the CNF given a string and an empty formula to read the clauses into
def parseFormula {α : Type} [Formula α] (s : String) (F : α) : Except String α := do
  let ⟨pLine, clauseLines⟩ ←
    s.splitOn "\n"
    |>.filter (fun line => !line.startsWith "c" && line.any (!·.isWhitespace))
    |>.expectNonempty fun () => "All lines are empty or comments"
  let (nvars, ncls) ← parseHeader pLine
  let F ← clauseLines.foldlM (parseClause nvars) F
  if Formula.size F != ncls then
    throw s!"Expected {ncls} clauses, but found {Formula.size F}"
  else
    return F

inductive LPRCheckingMode
| Clause   : LPRCheckingMode
| Witness  : LPRCheckingMode
| Reducing : LPRCheckingMode
| DoneWithLine : LPRCheckingMode
deriving BEq

inductive SRParsingMode
| clause
| witness_tf
| witness_mapped_ready
| witness_mapped_halfway : IVar → SRParsingMode
| up_hints
| rat_hints : Nat × Array Nat → SRParsingMode
| done_with_line -- Could be removed, in favor of Except (Except String SRLine), but this is arguably more elegant
deriving BEq

open SRParsingMode

structure SRDeletionLine where
  clauses : Array Nat

def parseSRAtom (pivot : Option ILit) (p : SRLine × SRParsingMode) (s : String) : Except String (SRLine × SRParsingMode) :=
  let ⟨line, mode⟩ := p
  -- No matter what, the string should be a number, so parse it as an int
  match s.toInt? with
  | none => throw s!"Atom {s} didn't parse to a number"
  | some n =>
    if hn : n = 0 then
      match mode with
      | .clause =>
        -- We don't have a witness, so we insert the pivot into the witness and continue, if the clause isn't empty
        match pivot with
        | none => return ⟨line, .up_hints⟩
        | some pivot => return ⟨{ line with witness_lits := line.witness_lits.push pivot }, .up_hints⟩
      | .witness_tf => return ⟨line, .up_hints⟩
      | .witness_mapped_ready => return ⟨line, .up_hints⟩
      | .witness_mapped_halfway _ => throw s!"Only got half a substitution mapping when ending a witness"
      | .up_hints => return ⟨line, .done_with_line⟩
      | .rat_hints hints => return ⟨{ line with rat_hints := line.rat_hints.push hints }, .done_with_line⟩
      | .done_with_line => throw s!"Addition line continued after last ending 0"
    else
      match mode with
      | .clause =>
        match pivot with
        | none => throw "No pivot provided for the clause"
        | some pivot =>
          if n = pivot.val then
            -- Seeing the pivot again means we're parsing a witness
            return ⟨{ line with witness_lits := line.witness_lits.push ⟨n, hn⟩ }, .witness_tf⟩
          else
            -- It's not the pivot (and it's not 0), so add it to the clause
            return ⟨{ line with clause := line.clause.push ⟨n, hn⟩ }, .clause⟩
      | .witness_tf =>
        match pivot with
        | none => throw "No pivot provided for the witness"
        | some pivot =>
          if n = pivot.val then
            -- Seeing the pivot again means we're parsing the substitution mappings
            return ⟨line, .witness_mapped_ready⟩
          else
            return ⟨{ line with witness_lits := line.witness_lits.push ⟨n, hn⟩ }, .witness_tf⟩
      | .witness_mapped_ready =>
        match pivot with
        | none => throw "No pivot provided for the witness"
        | some pivot =>
          if n = pivot.val then
            throw s!"Saw pivot again in substitution mapping"
          else
            if n < 0 then
              throw s!"First of a substitution mapping must be positive"
            else
              return ⟨line, .witness_mapped_halfway ⟨n.natAbs, Int.natAbs_pos.mpr hn⟩⟩
      | .witness_mapped_halfway v =>
        return ⟨{line with witness_maps := line.witness_maps.push ⟨v, ⟨n, hn⟩⟩ }, .witness_mapped_ready⟩
      | .up_hints =>
        if n < 0 then
          match pivot with
          | none => throw "Can't have RAT hints for empty clauses"
          | _ =>
            -- This is our first RAT hint - start building it
            return ⟨line, .rat_hints ⟨n.natAbs - 1, #[]⟩⟩
        else
          return ⟨{ line with up_hints := line.up_hints.push (n.natAbs - 1) }, .up_hints⟩
      | .rat_hints ⟨h, hints⟩ =>
        if n < 0 then
          -- This is a new RAT hint - add the old one
          return ⟨{ line with rat_hints := line.rat_hints.push ⟨h, hints⟩ }, .rat_hints ⟨n.natAbs - 1, #[]⟩⟩
        else
          return ⟨line, .rat_hints ⟨h, hints.push (n.natAbs - 1)⟩⟩
      | .done_with_line => throw s!"Addition line continued after last ending 0"

/-def parseLSRLine (p : Nat × Array (SRLine ⊕ SRDeletionLine)) (s : String) : Except String (Nat × Array (SRLine ⊕ SRDeletionLine)) :=
  let ⟨maxId, lines⟩ := p
  match s.splitOn " " with
  | [] => throw "Empty line"
  | [_] => throw s!"Single atom line: {s}, with id {maxId}"
  | (id :: hd :: tls) =>
    match hd with
    | "d" =>
      -- Check to make sure the maxId is (non-strictly) monotonically increasing
      match id.toNat? with
      | none => throw "Line ID is not a number"
      | some id =>
        if id < maxId then
          throw "Deletion line id is not increasing"
        else
          match tls.foldlM (fun arr str =>
            match str.toNat? with
            | none => throw (throw s!"{str} was not a number")
            | some 0 => throw (return arr)
            | some (n + 1) => return arr.push n) #[] with
          | ok _ => throw "Zero not found on deletion line"
          | error e => return ⟨max id maxId, lines.push (.inr (SRDeletionLine.mk (← e)))⟩
    | _ =>
      -- We have an addition line, so the maxId should strictly increase
      match id.toNat? with
      | none => throw "Line ID is not a number"
      | some id =>
        if id ≤ maxId then
          throw s!"Addition line id is not increasing: parsed {id}, max {maxId}"
        else
          match hd.toInt? with
          | none => throw "Pivot is not a number"
          | some n =>
            let line : SRLine := ⟨#[], #[], #[], #[], #[]⟩
            if hn : n = 0 then
              match tls.foldlM (parseSRAtom none) ⟨line, .up_hints⟩ with
              | error str => throw str
              | ok ⟨line, mode⟩ =>
                if mode != .done_with_line then
                  throw "Addition line for empty clause didn't end with 0"
                else
                  return ⟨id, lines.push (.inl line)⟩
            else
              match tls.foldlM (parseSRAtom (some ⟨n, hn⟩)) ⟨{ line with clause := line.clause.push ⟨n, hn⟩ }, .clause⟩ with
              | error str => throw str
              | ok ⟨line, mode⟩ =>
                if mode != .done_with_line then
                  throw "Addition line didn't end with 0"
                else
                  return ⟨id, lines.push (.inl line)⟩ -/

def parseLSRLine (maxId : Nat) (s : String) : Except String (Nat × (SRLine ⊕ SRDeletionLine)) :=
  match s.splitOn " " with
  | [] => throw "Empty line"
  | [_] => throw s!"Single atom line: {s}, with id {maxId}"
  | (id :: hd :: tls) =>
    match hd with
    | "d" =>
      -- Check to make sure the maxId is (non-strictly) monotonically increasing
      match id.toNat? with
      | none => throw "Line ID is not a number"
      | some id =>
        if id < maxId then
          throw "Deletion line id is not increasing"
        else
          match tls.foldlM (fun arr str =>
            match str.toNat? with
            | none => throw (throw s!"{str} was not a number")
            | some 0 => throw (return arr)
            | some (n + 1) => return arr.push n) #[] with
          | ok _ => throw "Zero not found on deletion line"
          | error e => return ⟨max id maxId, .inr (SRDeletionLine.mk (← e))⟩
    | _ =>
      -- We have an addition line, so the maxId should strictly increase
      match id.toNat? with
      | none => throw "Line ID is not a number"
      | some id =>
        if id ≤ maxId then
          throw s!"Addition line id is not increasing: parsed {id}, max {maxId}"
        else
          match hd.toInt? with
          | none => throw "Pivot is not a number"
          | some n =>
            let line : SRLine := ⟨#[], #[], #[], #[], #[]⟩
            if hn : n = 0 then
              match tls.foldlM (parseSRAtom none) ⟨line, .up_hints⟩ with
              | error str => throw str
              | ok ⟨line, mode⟩ =>
                if mode != .done_with_line then
                  throw "Addition line for empty clause didn't end with 0"
                else
                  return ⟨id, .inl line⟩
            else
              match tls.foldlM (parseSRAtom (some ⟨n, hn⟩)) ⟨{ line with clause := line.clause.push ⟨n, hn⟩ }, .clause⟩ with
              | error str => throw str
              | ok ⟨line, mode⟩ =>
                if mode != .done_with_line then
                  throw "Addition line didn't end with 0"
                else
                  return ⟨id, .inl line⟩

/-
def parseLSRFile (formulaSize : Nat) (s : String) : Except String (Array (SRLine ⊕ SRDeletionLine)) :=
  match s.splitOn "\n"
    |>.filter (fun line => !line.startsWith "c" && line.any (!·.isWhitespace))
    |>.foldlM parseLSRLine ⟨formulaSize, #[]⟩ with
  | error e => throw e
  | ok ⟨_, lines⟩ => return lines -/


end SRParser

def main (args : List String) : IO Unit := do
  let cnfFile := args[0]!
  let lsrFile := args[1]!
  let contents ← IO.FS.withFile cnfFile .read (·.readToEnd)
  let F ← IO.ofExcept <| SRParser.parseFormula contents RangeArray.empty
  IO.println s!"Formula has {F.size} clauses"

  let lsrContents ← IO.FS.withFile lsrFile .read (·.readToEnd)
  let lines := lsrContents.splitOn "\n"
    |>.filter (fun line => !line.startsWith "c" && line.any (!·.isWhitespace))
  --let lines ← IO.ofExcept <| SRParser.parseLSRFile (F.size) lsrContents

  match lines.foldlM (init := ⟨F, PPA.new 100, PS.new 100⟩)
    (fun S line =>
      match SRParser.parseLSRLine F.size line with
      | .error _ => throw false
      | .ok ⟨_, Sum.inl l⟩ => SR.checkLineFlat S l
      | .ok (_, .inr l) =>
        let ⟨F, τ, σ⟩ := S
        return ⟨l.clauses.foldl RangeArray.delete F, τ, σ⟩) with
  | Except.ok _ => IO.println "c Flat Proof failed to derive the empty clause, but is otherwise valid"
  | Except.error false => IO.println "c Flat Proof failed"
  | Except.error true => IO.println "s VERIFIED UNSAT"
