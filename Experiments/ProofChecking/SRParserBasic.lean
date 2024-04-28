/-

A basic SR parser for general formulas.

Author: Cayden Codel
Carnegie Mellon University

-/

import LeanSAT.Solver.Dimacs
import Experiments.ProofChecking.RangeArray

open Std
open LeanSAT.Solver.Dimacs
open LeanSAT LeanSAT.Model ILit Except

namespace SR

structure SRAdditionLine where
  witnessLits : Array ILit
  witnessMaps : Array ILit     -- Maps literals to literals
  upHints : Array Nat          -- Already 0-indexed clause IDs into the accumulated formula
  ratHintIndexes : Array Nat   -- Already 0-indexed
  ratHints : Array (Array Nat) -- Already 0-indexed
  ratSizesEq : ratHintIndexes.size = ratHints.size
  witnessMapsMod : witnessMaps.size % 2 = 0
  -- CC: Technically, ratHints can be a RangeArray. Try later

def SRAdditionLine.new : SRAdditionLine := ⟨
  Array.mkEmpty 100,
  Array.mkEmpty 100,
  Array.mkEmpty 100,
  Array.mkEmpty 100,
  Array.mkEmpty 100,
  by simp, by simp⟩

instance : Inhabited SRAdditionLine := ⟨{
  witnessLits := #[],
  witnessMaps := #[],
  upHints := #[],
  ratHintIndexes := #[],
  ratHints := #[],
  ratSizesEq := by simp,
  witnessMapsMod := by simp
}⟩

structure SRDeletionLine where
  clauses : Array Nat
deriving Inhabited

end SR

namespace SRParser

protected class Formula (F : Type _) where
  empty : F
  addLiteral : F → ILit → F
  commitClause : F → F
  size : F → Nat

instance : SRParser.Formula (RangeArray ILit) where
  empty := (RangeArray.empty : RangeArray ILit)
  addLiteral := RangeArray.addElement
  commitClause := RangeArray.commit
  size := RangeArray.size

instance : SRParser.Formula (ICnf × IClause) where
  empty := (#[], #[])
  addLiteral := (fun ⟨F, C⟩ l => ⟨F, C.push l⟩)
  commitClause := (fun ⟨F, C⟩ => (F.push C, #[]))
  size := (fun ⟨F, _⟩ => F.size)

variable {CNF : Type _} [SRParser.Formula CNF]

-- Parses a single literal from a string.
-- CC: The double Except monad is used to stop folding across a list/array of atom strings
--     in case a 0 is encountered, since DIMACS doesn't require a clause to fit on a line.
@[inline, specialize]
def parseLit (maxVar : Nat) (F : CNF) (s : String) : Except (Except String CNF) CNF := do
  match s.toInt? with
  | none => throw (throw s!"Literal is not a number: {s}")
  | some n =>
    if hn : n = 0 then
      throw (return F)
    else
      if n.natAbs > maxVar then
        throw (throw s!"Literal {n} is greater than the maximum variable {maxVar}")
      else
        return Formula.addLiteral F ⟨n, hn⟩

@[specialize]
def parseClause (maxVar : Nat) (F : CNF) (s : String) : Except String CNF :=
  match s.splitOn " " |>.foldlM (parseLit maxVar) F with
  | ok _ => throw "Zero not encountered on this line"
  | error e => return Formula.commitClause (← e)

-- Parses the CNF given a string and an empty formula to read the clauses into
def parseFormula (s : String) (F : CNF) : Except String CNF := do
  match s.splitOn "\n" |>.filter (fun line => !line.startsWith "c" && line.any (!·.isWhitespace)) with
  | [] => throw "All lines are empty or comments"
  | (pLine :: clauseLines) =>
    let (nvars, ncls) ← parseHeader pLine
    let F ← clauseLines.foldlM (parseClause nvars) F
    if SRParser.Formula.size F != ncls then
      throw s!"Expected {ncls} clauses, but found {Formula.size F}"
    else
      return F

inductive SRParsingMode
| clause
| witnessLits
| witnessMappedReady
| witnessMappedHalfway : IVar → SRParsingMode
| upHints
| ratHints : Nat → Array Nat → SRParsingMode
| lineDone
| err : String → SRParsingMode
deriving BEq, Inhabited

open SR SRParsingMode

@[inline]
def processSRAtom (atom : Int) (pivot : Option ILit)
    (line : SRAdditionLine) (F : CNF) (mode : SRParsingMode) : SRAdditionLine × CNF × SRParsingMode :=
  if h_atom : atom = 0 then
    match mode with
    | .clause =>
      -- We don't have a witness, so we insert the pivot into the witness and continue, if the clause isn't empty
      match pivot with
      | none => ⟨line, F, .upHints⟩
      | some pivot => ⟨{ line with witnessLits := line.witnessLits.push pivot }, F, .upHints⟩
    | .witnessLits => ⟨line, F, .upHints⟩
    | .witnessMappedReady => ⟨line, F, .upHints⟩
    | .witnessMappedHalfway _ => ⟨line, F, .err "Only got half a substitution mapping when ending a witness"⟩
    | .upHints => ⟨line, F, .lineDone⟩
    | .ratHints index hints => ⟨{ line with
        ratHintIndexes := line.ratHintIndexes.push index,
        ratHints := line.ratHints.push hints,
        ratSizesEq := by simp [line.ratSizesEq] }, F, .lineDone⟩
    | .lineDone => ⟨line, F, .err "Addition line continued after last ending 0"⟩
    | .err str => ⟨line, F, .err str⟩
  else
    match mode with
    | .clause =>
      match pivot with
      | none => ⟨line, F, .err "No pivot provided for the clause"⟩
      | some pivot =>
        if atom = pivot.val then
          -- Seeing the pivot again means we're parsing a witness
          ⟨{ line with witnessLits := line.witnessLits.push ⟨atom, h_atom⟩ }, F, .witnessLits⟩
        else
          -- It's not the pivot (and it's not 0), so add it to the clause
          ⟨line, SRParser.Formula.addLiteral F ⟨atom, h_atom⟩, .clause⟩
    | .witnessLits =>
      match pivot with
      | none => ⟨line, F, .err "No pivot provided for the witness"⟩
      | some pivot =>
        if atom = pivot.val then
          -- Seeing the pivot again means we're parsing the substitution mappings
          ⟨line, F, .witnessMappedReady⟩
        else
          ⟨{ line with witnessLits := line.witnessLits.push ⟨atom, h_atom⟩ }, F, .witnessLits⟩
    | .witnessMappedReady =>
      match pivot with
      | none => ⟨line, F, .err "No pivot provided for the witness"⟩
      | some pivot =>
        if atom = pivot.val then
          ⟨line, F, .err "Saw pivot again in substitution mapping"⟩
        else
          if atom < 0 then
            ⟨line, F, .err "First of a substitution mapping must be positive"⟩
          else
            ⟨line, F, .witnessMappedHalfway ⟨atom.natAbs, Int.natAbs_pos.mpr h_atom⟩⟩
    | .witnessMappedHalfway v =>
      ⟨{line with
        witnessMaps := line.witnessMaps.push v |>.push ⟨atom, h_atom⟩,
        witnessMapsMod := by simp [add_assoc, Nat.add_mod_right, line.witnessMapsMod] }, F, .witnessMappedReady⟩
    | .upHints =>
      if atom < 0 then
        match pivot with
        | none => ⟨line, F, .err "Can't have RAT hints for empty clauses"⟩
        | _ =>
          -- This is our first RAT hint - start building it
          ⟨line, F, .ratHints (atom.natAbs - 1) #[]⟩
      else
        ⟨{ line with upHints := line.upHints.push (atom.natAbs - 1) }, F, .upHints⟩
    | .ratHints index hints =>
      if atom < 0 then
        -- This is a new RAT hint - add the old one
        ⟨{ line with
          ratHintIndexes := line.ratHintIndexes.push index,
          ratHints := line.ratHints.push hints,
          ratSizesEq := by simp [line.ratSizesEq] }, F, .ratHints (atom.natAbs - 1) #[]⟩
      else
        ⟨line, F, .ratHints index (hints.push (atom.natAbs - 1))⟩
    | .lineDone => ⟨line, F, .err "Addition line continued after last ending 0"⟩
    | .err str => ⟨line, F, .err str⟩

def parseSRAtom (pivot : Option ILit) (line : SRAdditionLine) (F : CNF) (mode : SRParsingMode) (s : String) : SRAdditionLine × CNF × SRParsingMode :=
  -- No matter what, the string should be a number, so parse it as an int
  match s.toInt? with
  | none => ⟨line, F, .err s!"Atom {s} didn't parse to a number"⟩
  | some n => processSRAtom n pivot line F mode

def parseLSRLine (F : CNF) (maxId : Nat) (s : String) : Except String (Nat × CNF × (SRAdditionLine ⊕ SRDeletionLine)) :=
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
          | error e => return ⟨max id maxId, F, .inr (SRDeletionLine.mk (← e))⟩
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
            let line := SRAdditionLine.new
            let res :=
              if hn : n = 0 then
                tls.foldlM (init := (⟨line, F, .upHints⟩ : SRAdditionLine × CNF × SRParsingMode))
                  (fun ⟨line, F, mode⟩ s => match mode with
                    | .err s => error s
                    | m => ok <| parseSRAtom none line F m s)
              else
                tls.foldlM (init := ⟨line, SRParser.Formula.addLiteral F ⟨n, hn⟩, .clause⟩)
                  (fun ⟨line, F, mode⟩ s => match mode with
                    | .err s => error s
                    | m => ok <| parseSRAtom (some ⟨n, hn⟩) line F m s)
            match res with
            | error str => throw str
            | ok ⟨line, F, mode⟩ =>
              if mode != .lineDone then
                throw "Addition line didn't end with 0"
              else
                return ⟨id, F, .inl line⟩

-- CC: An attempt to get parsing faster, given that the Except monad can be expensive
def parseLSRLine'_aux (pivot : Option ILit) (line : SRAdditionLine) (F : CNF) (mode : SRParsingMode) : List String → (SRAdditionLine × CNF × SRParsingMode)
  | [] => (line, F, mode)
  | atom :: atoms =>
  -- No matter what, the string should be a number, so parse it as an int
  match atom.toInt? with
  | none => ⟨line, F, .err s!"Atom {atom} didn't parse to a number"⟩
  | some n =>
    match processSRAtom n pivot line F mode with
    | ⟨line, F, .err str⟩ => ⟨line, F, .err str⟩
    | ⟨line, F, mode⟩ => parseLSRLine'_aux pivot line F mode atoms

def parseLSRLine' (F : CNF) (maxId : Nat) (s : String) : Except String (Nat × CNF × (SRAdditionLine ⊕ SRDeletionLine)) :=
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
          | error e => return ⟨max id maxId, F, .inr (SRDeletionLine.mk (← e))⟩
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
            let line := SRAdditionLine.new
            let res :=
              if hn : n = 0 then
                parseLSRLine'_aux none line F .upHints tls
              else
                parseLSRLine'_aux (some ⟨n, hn⟩) line (SRParser.Formula.addLiteral F ⟨n, hn⟩) .clause tls
            match res with
            | ⟨_, _, .err str⟩ => throw str
            | ⟨line, F, mode⟩ =>
              if mode != .lineDone then
                throw "Addition line didn't end with 0"
              else
                return ⟨id, F, .inl line⟩

--------------------------------------------------------------------------------

def undoBinaryMapping (x : UInt64) : Int :=
  if x &&& 1 = 1 then
    ((((x >>> 1).toNat) : Int) * -1)
  else
    (((x >>> 1).toNat) : Int)

/-
def readBinaryToken (A : ByteArray) (index : Nat) : Int × { i : Nat // i > index } :=
  let rec go (i : Nat) (acc : UInt64) (shift : UInt64) : Int × { idx : Nat // idx > i } :=
    if hi : i < A.size then
      let atom : UInt8 := A.get ⟨i, hi⟩
      let acc' : UInt64 := acc ||| ((atom &&& 127).toUInt64 <<< shift)
      if atom &&& 128 != 0 then
        match go (i + 1) acc' (shift + 7) with
        | ⟨a, ⟨b, hb⟩⟩ => ⟨a, ⟨b, Nat.le_of_succ_le hb⟩⟩
      else
        ⟨undoBinaryMapping acc', ⟨A.size, hi⟩⟩
    else
      ⟨undoBinaryMapping acc, ⟨i + 1, Nat.lt_succ_self _⟩⟩
  termination_by A.size - i
  go index 0 0
-/

-- Int is result, Nat is cached index into A
partial def readBinaryToken (A : ByteArray) (index : Nat) : Int × Nat :=
  let rec go (i : Nat) (acc : UInt64) (shift : UInt64) : Int × Nat :=
    if hi : i < A.size then
      let atom : UInt8 := A.get ⟨i, hi⟩
      let acc' : UInt64 := acc ||| ((atom &&& 127).toUInt64 <<< shift)
      if atom &&& 128 != 0 then
        go (i + 1) acc' (shift + 7)
      else
        ⟨undoBinaryMapping acc', i + 1⟩
    else
      ⟨undoBinaryMapping acc, A.size⟩
  let ⟨res, idx⟩ := go index 0 0
  -- dbg_trace s!"Pointer at index {index} moved to {idx}, parsed {res}"
  ⟨res, idx⟩

-- Bool: found a 0
-- Nat: updated index
partial def parseLSRDeletionLineBinary (A : ByteArray) (index : Nat) : Bool × Nat × SRDeletionLine :=
  let rec go (i : Nat) (acc : Array Nat) : Bool × Nat × SRDeletionLine :=
    if i < A.size then
      let (x, j) := readBinaryToken A i
      if x = 0 then
        ⟨true, j, SRDeletionLine.mk acc⟩
      else
        go j (acc.push (x.natAbs - 1))
    else
      ⟨false, A.size, SRDeletionLine.mk acc⟩
  go index #[]

instance [Inhabited CNF] : Inhabited (Nat × SRAdditionLine × CNF × SRParsingMode) := by infer_instance

/-
partial def parseLSRAdditionLineBinary [Inhabited CNF] (F : CNF) (A : ByteArray)
    (index : Nat) (pivot : Option ILit) : Nat × SRAdditionLine × CNF × SRParsingMode :=
  let rec go (i : Nat) (line : SRAdditionLine) (F : CNF) (mode : SRParsingMode) : Nat × SRAdditionLine × CNF × SRParsingMode :=
    if i < A.size then
      let (n, j) := readBinaryToken A i
      match processSRAtom n pivot line F mode with
      | ⟨line, F, .err str⟩ => ⟨j, line, F, .err str⟩
      | ⟨line, F, .lineDone⟩ => ⟨j, line, F, .lineDone⟩
      | ⟨line, F, mode⟩ => go j line F mode
    else
      ⟨A.size, line, F, mode⟩

  let newLine := SRAdditionLine.new
  match pivot with
  | none => go index newLine F .upHints
  | some p => go index newLine (SRParser.Formula.addLiteral F p) .clause -/


-- First nat is cached index into arr, second is ID of new clause to add
/-
partial def parseLSRLineBinary (A : ByteArray)
    (index : Nat) : Except String (Nat × Nat × (SRAdditionLine ⊕ SRDeletionLine)) :=
  if hi : index + 1 < A.size then
    -- Check if we have an addition line or a deletion line
    let lineStart : UInt8 := A.get ⟨index, Nat.lt_of_succ_lt hi⟩
    let ⟨lineId, index⟩ := readBinaryToken A (index + 1)
    if lineId < 0 then error "Negative line ID" else

    -- Addition line
    if lineStart = 1 then
      -- Check if we have a pivot
      if index < A.size then
        let ⟨pivot, index⟩ := readBinaryToken A index
        let res :=
          if hp : pivot = 0 then
            parseLSRAdditionLineBinary A index none
          else
            parseLSRAdditionLineBinary A index (some ⟨pivot, hp⟩)
        match res with
        | ⟨_, _, .err str⟩ => throw str
        | ⟨index, line, mode⟩ =>
          if mode != .lineDone then
            error "Addition line didn't end with 0"
          else
            ok (index, lineId.natAbs, .inl line)
      else
        error "Line ended early"
    else if lineStart = 2 then
      match parseLSRDeletionLineBinary A index with
      | ⟨true, index, line⟩ => ok (index, lineId.natAbs, .inr line)
      | ⟨false, _, _⟩ => error "Deletion line didn't end with 0"
    else
      error "Start of line wasn't addition (1) or deletion (2)"

  else
    error "No more string!" -/

end SRParser
