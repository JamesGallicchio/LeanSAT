/-

An LSR checker for the RangeArray data structure.

Author: Cayden Codel
Carnegie Mellon University

-/

import Experiments.ProofChecking.PPA
import Experiments.ProofChecking.PS
import Experiments.ProofChecking.RangeArray
import Experiments.ProofChecking.SRParserBasic

import LeanSAT.Data.Cnf
import LeanSAT.Data.ICnf
import LeanSAT.Model.PropFun
import LeanSAT.Model.Subst

open LeanSAT LeanSAT.Model Nat
open PPA PS LitVar ILit IVar LawfulLitVar PropFun
open Except

namespace SR

-- Apply unit propagation to clause `i`.
@[inline, always_inline]
def unitProp (τ : PPA) (F : RangeArray ILit) (i : Nat) : MUPResult :=
  unitPropOnIndexes τ F.data (F.index i) (F.index i + F.rsize i)

@[inline, always_inline]
def reduce (σ : PS) (F : RangeArray ILit) (i : Nat) : ReductionResult :=
  σ.reduceOnIndexes F.data (F.index i) (F.index i + F.rsize i)

-- On error: The Bool being true indicates contradiction, false indicates actual error.
@[inline]
def applyUPHint (F : RangeArray ILit) (bumps : Nat) (τ : PPA) (hint : Nat) : Except (PPA × Bool) PPA :=
  if hint < F.size && !F.isDeleted hint then
    match unitProp τ F hint with
    | .falsified => error ⟨τ, true⟩
    | .satisfied =>
      -- dbg_trace s!"ERROR: UP found a satisfied clause at index {hint}"
      error ⟨τ, false⟩
    | .multipleUnassignedLiterals =>
      -- dbg_trace s!"ERROR: UP found a non-unit clause at index {hint}"
      error ⟨τ, false⟩
    | .unit l =>
      -- dbg_trace s!"    Hint {hint} makes clause unit on literal {l}"
      ok (τ.setLitFor l bumps)
  else
    -- dbg_trace s!"ERROR: Hint out of bounds"
    error ⟨τ, false⟩

@[inline, always_inline]
def applyUPHints (F : RangeArray ILit) (offset : Nat) (τ : PPA) (hints : Array Nat) : Except (PPA × Bool) PPA :=
  -- A re-implementation of hints.foldlM ..., except it uses an explicit
  -- index and is tail-recursive in its loop.
  let rec go (i : Nat) (τ : PPA) : Except (PPA × Bool) PPA :=
    if hi : i < hints.size then
      match applyUPHint F offset τ (hints.get ⟨i, hi⟩) with
      | ok τ => go (i + 1) τ
      | error ⟨τ, true⟩ => error ⟨τ, true⟩
      | error ⟨τ, false⟩ => error ⟨τ, false⟩
    else ok τ
  termination_by hints.size - i
  go 0 τ
  --hints.foldlM (init := τ) (applyUPHint F offset)

-- Scans the RAT hints
def scanRATHints (clauseId : Nat) (ratHintIndexes : Array Nat) : Option (Fin ratHintIndexes.size) :=
  match ratHintIndexes.foldlM (init := 0) (fun counter hint =>
        if hint = clauseId then error counter
        else ok (counter + 1)) with
  | ok _ => none
  | error index =>
    if hi : index < ratHintIndexes.size then some ⟨index, hi⟩
    else none

-- Finds the RAT hint pair that matches the clauseId
def findRATHintIndex (ratIndex clauseId : Nat) (ratHintIndexes : Array Nat) : Option (Fin ratHintIndexes.size) :=
  -- If the RAT hints are sorted, then check the one under our "cached pointer" first
  if h_index : ratIndex < ratHintIndexes.size then
    let ratClauseIndex := ratHintIndexes.get ⟨ratIndex, h_index⟩
    if ratClauseIndex = clauseId then some ⟨ratIndex, h_index⟩
    else scanRATHints clauseId ratHintIndexes
  else
    scanRATHints clauseId ratHintIndexes

-- Returns an updated PPA. Bool is true if the clause is satisfied by σ or τ, false otherwise.
def assumeRATClause (F : RangeArray ILit) (index : Fin F.size) (σ : PS) (τ : PPA) : PPA × Bool :=
  let size := F.rsize index
  let rec go (i : Nat) (τ : PPA) : PPA × Bool :=
    if hi : i < size then
      let lit := F.getOffset index ⟨i, hi⟩
      match σ.litValue lit with
      | Sum.inr true => ⟨τ, true⟩
      | Sum.inr false => go (i + 1) τ
      | Sum.inl l =>
        match τ.litValue? l with
        | some true => ⟨τ, true⟩
        | some false => go (i + 1) τ
        | none => go (i + 1) (τ.setLit (-l))
    else ⟨τ, false⟩
  termination_by (F.rsize index) - i
  go 0 τ

def assumeWitness (σ : PS) (pivot : ILit) (A₁ : Array ILit) (A₂ : Array ILit) : PS :=
  ((σ.reset.setLits A₁).setVars' A₂).setLit pivot

def checkLine (F : RangeArray ILit) (τ : PPA) (σ : PS) (line : SRAdditionLine) : Except Bool (RangeArray ILit × PPA × PS) :=
  let ⟨C, wL, wM, upHints, ratHintIndexes, ratHints, _, _⟩ := line
  -- dbg_trace s!"{C}, {wL}, {wM}"
  -- dbg_trace s!"{upHints}, {ratHintIndexes}, {ratHints}"
  match assumeNegatedClauseFor τ.reset C (ratHints.size + 1) with
  | error _ =>
    -- dbg_trace s!"Assumed negation of clause had error"
    error false
  | ok τ =>
    -- dbg_trace s!"Assumed negation of clause succeeded"
    -- Evaluate the UP hints, with "# of RAT hints" as the offset
    match applyUPHints F (ratHints.size + 1) τ upHints with
    | error ⟨_, false⟩ =>
      -- dbg_trace s!"Applying UP hints encountered an error"
      error false
    | error ⟨τ, true⟩ =>
      -- dbg_trace s!"Applying UP hints found contradiction before RAT"
      if C.size = 0 then error true    -- If the clause is empty, we have a successful contradiction proof
      else ok ⟨F.add C, τ, σ⟩

    | ok τ =>
      -- If the clause is empty, we should have derived UP contradiction by now
      if hC : 0 < C.size then
        let pivot : ILit := wL.getD 0 (C.get ⟨0, hC⟩)
        if pivot != C.get ⟨0, hC⟩ then error false else
        let σ := assumeWitness σ pivot wL wM

        -- Loop through each clause in the formula to check RAT conditions
        -- The Bool is true if the check succeeds on all clauses, false otherwise
        let Fsize := F.size
        let rec loop (i cachedRatHintIndex bumpCounter : Nat) (τ : PPA) : PPA × Bool :=
          if hi : i < Fsize then
            if F.isDeleted i then loop (i + 1) cachedRatHintIndex bumpCounter τ
            else
              -- First, check how the ith clause is reduced by σ
              match reduce σ F i with
              | .satisfied => loop (i + 1) cachedRatHintIndex bumpCounter τ
              | .notReduced => loop (i + 1) cachedRatHintIndex bumpCounter τ
              | _ =>
                -- dbg_trace s!"Clause index {i} is a RAT candidate"
                if bumpCounter < ratHintIndexes.size then
                  -- Find the corresponding RAT hint
                  match findRATHintIndex cachedRatHintIndex i ratHintIndexes with
                  | none => ⟨τ, false⟩
                  | some ratIndex =>
                    -- Assume the negation of the RAT clause
                    match assumeRATClause F ⟨i, hi⟩ σ τ with
                    | ⟨τ, true⟩ => loop (i + 1) (ratIndex + 1) (bumpCounter + 1) τ.bump
                    | ⟨τ, false⟩ =>
                      match applyUPHints F 0 τ (ratHints.get ⟨ratIndex, by sorry⟩) with
                      | ok τ => ⟨τ, false⟩
                      | error ⟨τ, false⟩ => ⟨τ, false⟩
                      | error ⟨τ, true⟩ => loop (i + 1) (ratIndex + 1) (bumpCounter + 1) τ.bump
                else ⟨τ, false⟩
          else ⟨τ, true⟩
        termination_by F.size - i

        match loop 0 0 0 τ with
        | ⟨_, false⟩ => error false
        | ⟨τ, true⟩ => ok ⟨F.add C, τ, σ⟩

      else error false

end SR

partial def main (args : List String) : IO Unit := do
  let cnfFile := args[0]!
  let lsrFile := args[1]!
  let option : Nat := (args.getD 2 "0").toNat!
  let contents ← IO.FS.withFile cnfFile .read (·.readToEnd)
  let F : RangeArray ILit ← IO.ofExcept <| SRParser.parseFormula contents RangeArray.empty
  IO.println s!"Formula has {F.size} clauses"

  match option with
  | 0 =>
    let lsrContents : String ← IO.FS.withFile lsrFile .read (·.readToEnd)
    let lines := lsrContents.splitOn "\n"
      |>.filter (fun line => !line.startsWith "c" && line.any (!·.isWhitespace))

    match lines.foldlM (init := (⟨F, PPA.new 100, PS.new 100⟩ : RangeArray ILit × PPA × PS))
      (fun ⟨F, τ, σ⟩ line =>
        match SRParser.parseLSRLine' F.size line with
        | .error _ => throw false
        | .ok ⟨_, Sum.inl l⟩ => SR.checkLine F τ σ l
        | .ok (_, .inr l) =>
          return ⟨l.clauses.foldl RangeArray.delete F, τ, σ⟩) with
    | Except.ok _ =>
      IO.println "c Proof failed to derive the empty clause, but is otherwise valid"
      IO.println "s VALID"
    | Except.error false => IO.println "c Proof failed"
    | Except.error true => IO.println "s VERIFIED UNSAT"
  | _ =>
    let lsrContents : ByteArray ← IO.FS.withFile lsrFile .read (·.readBinToEnd)
    let rec go (readPtr : Nat) (F : RangeArray ILit) (τ : PPA) (σ : PS) : IO Unit := do
      if readPtr < lsrContents.size then
        match SRParser.parseLSRLineBinary lsrContents readPtr with
        | ok ⟨newPtr, lineId, .inl line⟩ =>
          match SR.checkLine F τ σ line with
          | Except.ok ⟨F, τ, σ⟩ => go newPtr F τ σ
          | Except.error false => IO.println "c Proof failed"
          | Except.error true => IO.println "s VERIFIED UNSAT"
        | ok ⟨newPtr, lineId, .inr line⟩ =>
          go newPtr (line.clauses.foldl RangeArray.delete F) τ σ
        | error str => IO.println s!"c Error: {str}"
      else
        IO.println "c End of file"
    go 0 F (PPA.new 100) (PS.new 100)
