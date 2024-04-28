/-

A combined LSR parser and checker.

Cayden Codel
Carnegie Mellon University

-/

import LeanSAT.Data.Cnf
import LeanSAT.Data.Literal
import LeanSAT.Data.ICnf

import LeanSAT.Model.PropFun

import Experiments.ProofChecking.PPA
import Experiments.ProofChecking.PS
import Experiments.ProofChecking.RangeArray

import LeanSAT.Solver.Dimacs

open LeanSAT LeanSAT.Model PropFun Except

namespace SR

@[specialize]
class Formula (F : Type _) where
  size : F → Nat
  empty : F
  addClause : F → IClause → F
  deleteClause : F → Nat → F
  isDeleted : F → Nat → Bool
  foldMOnClause : F → Nat →
    {β : Type v} → {m : Type v → Type w} → [Monad m] →
    (f : β → ILit → m β) → (init : β) → m β
  -- Technically, `toPropFun` can be defined in terms of foldMOnClause
  --toPropFun : F → PropFun IVar

open Formula in
class LawfulFormula (F : Type _) [Formula F] where
  size_empty : size (empty : F) = 0
  size_addClause (f : F) (c : IClause) : size (addClause f c) = size f + 1
  size_deleteClause (f : F) (i : Nat) : size (deleteClause f i) = size f
  /-- All clauses out-of-bounds are deleted. -/
  isDeleted_ge_size (f : F) (i : Nat) : i ≥ size f → isDeleted f i = false
  /-- If we delete a clause, it should actually be marked as deleted. -/
  isDeleted_deleteClause (f : F) (i j : Nat) : isDeleted (deleteClause f i) j =
    if i = j then true else isDeleted f j
  /-- Added clauses are, by default, not deleted. -/
  isDeleted_addClause (f : F) (c : IClause) (i : Nat) : isDeleted (addClause f c) (size f) = false
  /-- Folding across a just-deleted clause should give back init. -/
  foldlMOnClause_deleteClause (f : F) (i : Nat) {β : Type v} {m : Type v → Type w} [Monad m]
    (g : β → ILit → m β) (init : β) : foldMOnClause (deleteClause f i) i g init = pure init
  /-- If we fold after adding, it's the same as folding across either a clause in the formula,
      or the clause we just added. -/
  foldlMOnClause_addClause (f : F) (c : IClause) (i : Nat) {β : Type v} {m : Type v → Type w} [Monad m]
    (g : β → ILit → m β) (init : β) : foldMOnClause (addClause f c) i g init =
      if i = size f then c.foldlM g init else foldMOnClause f i g init

instance : Formula (RangeArray ILit) where
  size := RangeArray.size
  empty := RangeArray.empty
  addClause := RangeArray.add
  deleteClause := RangeArray.delete
  isDeleted := RangeArray.isDeleted
  foldMOnClause := fun F i _ _ _ f init => F.foldlM_index f init i

structure SRLine where
  clause : IClause
  witness_lits : Array ILit
  witness_maps : Array (IVar × ILit)
  up_hints : Array Nat                -- Already 0-indexed clause IDs into the accumulated formula
  rat_hints : Array (Nat × Array Nat) -- Already 0-indexed clause IDs into the accumulated formula

structure SRDeletionLine where
  clauses : Array Nat

-- TODO: Move to LeanSAT
-- CC: James claims that CPS is easier to reason about and is more performant,
--     and Mario claims that Except blobbies are expensive for Lean to constantly create.
--     Make a `call/cc` construct later?
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

-- CC: Move to LeanSAT/replace the existing `parseClause`
def parseClause {CNF : Type _} [Formula CNF] (maxVar : Nat) (F : CNF) (s : String) : Except String CNF :=
  match s.splitOn " " |>.foldlM (parseLit maxVar) #[] with
  | ok _ => throw "Zero not encountered on this line"
  | error e =>
    match e with
    | ok c => return Formula.addClause F c
    | error e => throw e

-- CC: Can be made into a state machine later, to consume tokens rather than whole lines
--     Otherwise, parsing can take up a lot of CPU time.
--     (Plus, streaming?)
-- Parses the CNF given a string and an empty formula to read the clauses into
def parseFormula {CNF : Type _} [Formula CNF] (s : String) (F : CNF) : Except String (Nat × CNF) := do
  -- CC: See SRParser.lean for a more idiomatic version. Had trouble with universe levels
  match s.splitOn "\n" |>.filter (fun line => !line.startsWith "c" && line.any (!·.isWhitespace)) with
  | [] => throw "Empty formula"
  | (pLine :: clauseLines) =>

  /-
  Doing (nvars, ncls) ← Solver.Dimacs.parseHeader pLine gives

  stuck at solving universe constraint
  u =?= max ?u.3706 ?u.3707
while trying to unify
  (?m.3712 s F pLine clauseLines × ?m.3713 s F pLine clauseLines) (?m.3712 s F pLine clauseLines)
    (?m.3713 s F pLine clauseLines)
with
  (?m.3712 s F pLine clauseLines × ?m.3713 s F pLine clauseLines) (?m.3712 s F pLine clauseLines)
    (?m.3713 s F pLine clauseLines)
  -/

    match Solver.Dimacs.parseHeader pLine with
    | error s => throw s
    | ok (nvars, ncls) =>
      let F ← clauseLines.foldlM (parseClause nvars) F
      if Formula.size F != ncls then
        throw s!"Expected {ncls} clauses, but found {Formula.size F}"
      else
        return (nvars, F)

-- CC: In some sense, the witness can be assumed right away (and maybe even the negation of the candidate clause)
--     But for a clean separation of parsing and checking, we store in an intermediate data structure.
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

--------------------------------------------------------------------------------

@[specialize]
def checkLine {CNF : Type _} [Formula CNF] (F : CNF) (τ : PPA) (σ : PS)
  (clause : IClause) (w_lits : Array ILit) (w_maps : Array (IVar × ILit))
  (up_hints : Array Nat) (rat_hints : Array (Nat × Array Nat)) : Except Bool (CNF × PPA × PS) :=
    --(success : CNF → PPA → PS → Except Bool )
    --(fail : String → α) : α :=
    error false

--------------------------------------------------------------------------------
end SR

open SR SR.Formula

inductive SRResult where
  | err   : SRResult -- Some kind of error
  | valid : SRResult -- Didn't derive the empty clause
  | unsat : SRResult

@[specialize]
def checkLines {CNF : Type _} [Formula CNF] (F : CNF) (τ : PPA) (σ : PS) : List String → SRResult
  | [] => SRResult.valid
  | line :: lines =>
    match SR.parseLSRLine (size F) line with
    | Except.error str =>
      dbg_trace str
      SRResult.err

    -- TODO: maxId logic
    | Except.ok (_, Sum.inl ⟨c, wl, wm, uh, rh⟩) =>
      match SR.checkLine F τ σ c wl wm uh rh with
      | Except.error true => SRResult.err
      | Except.error false => SRResult.err
      | Except.ok (F, τ, σ) => checkLines F τ σ lines
    | Except.ok (_, Sum.inr l) =>
      checkLines (l.clauses.foldl Formula.deleteClause F) τ σ lines

def main (args : List String) : IO Unit := do
  if args.length != 2 then
    IO.println "Usage: ./exe <cnf-file> <lsr-file>"
    return

  let cnfFile := args[0]!
  let lsrFile := args[1]!
  let contents ← IO.FS.withFile cnfFile .read (·.readToEnd)
  let (nvars, F) ← IO.ofExcept <| SR.parseFormula contents (RangeArray.empty : RangeArray ILit)
  let numClauses := F.size
  IO.println s!"c Formula has {numClauses} clauses and {nvars} variables"

  let lsrContents ← IO.FS.withFile lsrFile .read (·.readToEnd)
  let lsrLinesRaw := lsrContents.splitOn "\n"
      |>.filter (fun line => !line.startsWith "c" && line.any (!·.isWhitespace))

  let numLines := lsrLinesRaw.length
  --let lineFailed : String → IO Unit := fun str =>
  --  IO.println s!"c Line failed: {str}"

  match @checkLines (RangeArray ILit) _ F (PPA.new (nvars * 2)) (PS.new (nvars * 2)) lsrLinesRaw with
  | .valid =>
    IO.println "c Proof was valid, but did not derive the empty clause"
    IO.println "s VERIFIED"
  | .err =>
    IO.println "c Proof failed"
    IO.println "s INVALID"
  | .unsat =>
    IO.println "s VERIFIED UNSAT"
