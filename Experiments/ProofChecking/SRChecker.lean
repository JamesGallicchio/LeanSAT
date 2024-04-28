/-

An LSR proof checker, with proof of correctness.

Uses `RangeArray`s to efficiently implement CNF formulas with deletion.

Author: Cayden Codel
Carnegie Mellon University

-/

import Experiments.ProofChecking.RangeArray
import Experiments.ProofChecking.SRParser
import Experiments.ProofChecking.PPA
import Experiments.ProofChecking.PS

import LeanColls
open LeanColls

open RangeArray
open LeanSAT LeanSAT.Model
open PPA PS
open Except

namespace RangeArray


def uAssumeNegatedForM (F : RangeArray ILit) (τ : PPA) (bumps : Nat) : Except PPA PPA :=
  let usize := F.usize
  let rec loop (i : Nat) (τ : PPA) : Except PPA PPA :=
    if h : i < usize then
      let l := F.ugetFin ⟨i, h⟩
      match τ.litValue? l with
      | none       => loop (i + 1) (τ.setLitFor (-l) bumps)
      | some false => loop (i + 1) τ
      | some true  => .error τ
    else
      .ok τ
  termination_by F.usize - i
  loop 0 τ

def uAssumeNegatedFor (F : RangeArray ILit) (τ : PPA) (bumps : Nat) : PPA × Bool :=
  let usize := F.usize
  let rec loop (i : Nat) (τ : PPA) : (PPA × Bool) :=
    if h : i < usize then
      let l := F.ugetFin ⟨i, h⟩
      match τ.litValue? l with
      | none       => loop (i + 1) (τ.setLitFor (-l) bumps)
      | some false => loop (i + 1) τ
      | some true  => (τ, true)
    else
      (τ, false)
  termination_by F.usize - i
  loop 0 τ

-- TODO: Swap with tail-recursive function, move to PS.
/-- Assumes into `τ` the negation of RAT clause `C` under the substitution `σ` for one "bump."
    Errors if `C` is satisfied by either `σ` or `τ` under `σ`. -/
def assumeRATClauseM (F : RangeArray ILit) (index : Fin F.size) (σ : PS) (τ : PPA) : Except PPA PPA :=
  F.foldlM_index (init := τ) (fun τ lit =>
    match σ.litValue lit with
    | Sum.inr true => error τ       -- (C|σ) is satisfied, so return early to report satisfied
    | Sum.inr false => ok τ         -- Ignore the literal
    | Sum.inl l =>
      match τ.litValue? l with
      | some true => error τ        -- (C|σ)|τ is satisfied, so return early to report satisfied
      | some false => ok τ          -- Its negation is true in τ, so ignore the literal
      | none => ok (τ.setLit (-l))) index

def assumeRATClause (F : RangeArray ILit) (index : Fin F.size) (σ : PS) (τ : PPA) : PPA × Bool :=
  let rsize := F.rsizeFin index
  let rec loop (i : Nat) (τ : PPA) : PPA × Bool :=
    if h : i < rsize then
      let lit := F.ogetFin index ⟨i, h⟩
      match σ.litValue lit with
      | Sum.inr true => ⟨τ, true⟩
      | Sum.inr false => loop (i + 1) τ
      | Sum.inl l =>
        match τ.litValue? l with
        | some true => ⟨τ, true⟩
        | some false => loop (i + 1) τ
        | none => loop (i + 1) (τ.setLit (-l))
    else
      ⟨τ, false⟩
  termination_by F.rsizeFin index - i
  loop 0 τ

def unitProp (τ : PPA) (F : RangeArray ILit) (hint : Fin F.size) : PPA.UPResult :=
  let rsize := F.rsizeFin hint
  let rec loop (i : Nat) (unit? : Option ILit) : PPA.UPResult :=
    if hi : i < rsize then
      let lit := F.ogetFin hint ⟨i, hi⟩
      match τ.litValue? lit with
      | some true => .satisfied
      | some false => loop (i + 1) unit?
      | none =>
        match unit? with
        | none => loop (i + 1) (some lit)
        | some u =>
          if u = lit then loop (i + 1) unit?
          else .multipleUnassignedLiterals
    else
      match unit? with
      | none => .falsified
      | some l => .unit l
  termination_by F.rsizeFin hint - i
  loop 0 none

inductive HintResult where
  | unit
  | contra
  | err
  deriving DecidableEq, Inhabited

@[inline]
def applyUPHint (F : RangeArray ILit) (bumps : Nat) (τ : PPA) (hint : Nat) : PPA × HintResult :=
  if h_hint : hint < F.size then
    if !F.isDeleted hint then
      match unitProp τ F ⟨hint, h_hint⟩ with
      | .falsified => ⟨τ, .contra⟩
      | .satisfied =>
        -- dbg_trace s!"ERROR: UP found a satisfied clause at index {hint}"
        ⟨τ, .err⟩
      | .multipleUnassignedLiterals =>
        -- dbg_trace s!"ERROR: UP found a non-unit clause at index {hint}"
        ⟨τ, .err⟩
      | .unit l =>
        -- dbg_trace s!"    Hint {hint} makes clause unit on literal {l}"
        (τ.setLitFor l bumps, .unit)
    else
      ⟨τ, .err⟩
  else
    -- dbg_trace s!"ERROR: Hint out of bounds"
    ⟨τ, .err⟩

@[inline, always_inline]
def applyUPHints (F : RangeArray ILit) (offset : Nat) (τ : PPA) (hints : Array Nat) : PPA × HintResult :=
  let rec loop (i : Nat) (τ : PPA) : PPA × HintResult :=
    if hi : i < Size.size hints then
      match applyUPHint F offset τ (Seq.get hints ⟨i, hi⟩) with
      | (τ, .unit) => loop (i + 1) τ
      | (τ, .contra) => (τ, .contra)
      | (τ, .err) => (τ, .err)
    else (τ, .unit)
  termination_by hints.size - i
  loop 0 τ

def reduce (σ : PS) (F : RangeArray ILit) (index : Fin F.size) : ReductionResult :=
  let rsize := F.rsizeFin index
  let rec loop (i : Nat) (reduced? : Bool) : ReductionResult :=
    if hi : i < rsize then
      let lit := F.ogetFin index ⟨i, hi⟩
      match seval' σ lit with
      | .satisfied => .satisfied
      | .reduced => loop (i + 1) true
      | .notReduced => loop (i + 1) reduced?
    else
      if reduced? then .reduced else .notReduced
  termination_by F.rsizeFin index - i
  loop 0 false

def reduce' (σ : PS) (F : RangeArray ILit) (index : Fin F.size) : ReductionResult :=
  let rsize := F.rsizeFin index
  let rstart := F.indexFin index
  let rec loop (i : Nat) (reduced? : Bool) : ReductionResult :=
    if hi : i < rsize then
      let lit := F.getFin ⟨rstart + i, index_add_offset_in_range index ⟨i, hi⟩⟩
      match seval' σ lit with
      | .satisfied => .satisfied
      | .reduced => loop (i + 1) true
      | .notReduced => loop (i + 1) reduced?
    else
      if reduced? then .reduced else .notReduced
  termination_by F.rsizeFin index - i
  loop 0 false

-- CC: Causes quadratic(?) slowdown, from 0.79 secs to 12.21 secs on php25
--     Profiler claims that 41% of CPU is spent in σ.setLits though...
def reduceM (σ : PS) (F : RangeArray ILit) (index : Fin F.size)
    (h_del : F.isDeletedFin index = false) : ReductionResult :=
  match ((F.foldlM_indexHyps (fun reduced? lit =>
    match seval' σ lit with
    | .satisfied => throw ()
    | .reduced => return true
    | .notReduced => return reduced?) false index h_del) : Except Unit Bool) with
  | .ok reduced? => if reduced? then .reduced else .notReduced
  | .error _ => .satisfied

end RangeArray

namespace SR

-- Scans through the RAT hint clause IDs to find a matching ID
def scanRATHintIndexesM (clauseId : Nat) (ratHintIndexes : Array Nat) : Option (Fin ratHintIndexes.size) :=
  match ratHintIndexes.foldlM (init := 0) (fun counter hint =>
        if hint = clauseId then error counter
        else ok (counter + 1)) with
  | ok _ => none
  | error index =>
    if hi : index < Size.size ratHintIndexes then
      some ⟨index, hi⟩
    else
      none

def scanRATHintIndexes (clauseId : Nat) (ratHintIndexes : Array Nat) : Option (Fin ratHintIndexes.size) :=
  let rec loop (i : Nat) : Option (Fin ratHintIndexes.size) :=
    if h : i < Size.size ratHintIndexes then
      if Seq.get ratHintIndexes ⟨i, h⟩ = clauseId then some ⟨i, h⟩
      else loop (i + 1)
    else none
  termination_by ratHintIndexes.size - i
  loop 0

-- Finds the index for the (RAT clause ID + RAT hints) that matches the clauseId
def findRATHintIndex (ratIndex clauseId : Nat) (ratHintIndexes : Array Nat) : Option (Fin ratHintIndexes.size) :=
  -- If the RAT hints are sorted, then check the one under our "cached pointer" first
  if h_index : ratIndex < Size.size ratHintIndexes then
    let ratClauseIndex := Seq.get ratHintIndexes ⟨ratIndex, h_index⟩
    if ratClauseIndex = clauseId then
      some ⟨ratIndex, h_index⟩
    else
      -- TODO: Test with `M` here.
      scanRATHintIndexes clauseId ratHintIndexes
  else
    scanRATHintIndexes clauseId ratHintIndexes


/-- Set the witness substitution σ from the provided mapping, resetting σ first. -/
def assumeWitness (σ : PS) (pivot : ILit) (A₁ : Array ILit) (A₂ : Array ILit) : PS :=
  ((σ.reset.setLits A₁).setVars' A₂).setLit pivot

structure SRState where
  F : RangeArray ILit
  τ : PPA
  σ : PS

def checkLine (st : SRState) (line : SRAdditionLine) : Except Bool SRState :=
  --let ⟨C, wL, wM, upHints, ratHintIndexes, ratHints, _, _⟩ := line
  -- dbg_trace s!"{C}, {wL}, {wM}"
  -- dbg_trace s!"{upHints}, {ratHintIndexes}, {ratHints}"
  match uAssumeNegatedForM st.F st.τ.reset (line.ratHints.size + 1) with
  | error _ =>
    -- dbg_trace s!"Assuming the negation of the candidate clause had error"
    error false
  | ok τ =>
    let st := { st with τ := τ }
    -- dbg_trace s!"Assumed negation of clause succeeded"
    -- Evaluate the UP hints, with "# of RAT hints" as the offset
    match applyUPHints st.F (line.ratHints.size + 1) st.τ line.upHints with
    | (_, .err) =>
      -- dbg_trace s!"Applying UP hints encountered an error"
      error false
    | (τ, .contra) =>
      let st := { st with τ := τ }
      -- dbg_trace s!"Applying UP hints found contradiction before RAT"
      if st.F.usize = 0 then error true  -- If the clause is empty, we have a successful contradiction proof
      else ok { st with F := st.F.commit }

    | (τ, .unit) =>
      let st := { st with τ := τ }

      -- If the clause is empty, we should have derived UP contradiction by now
      if hu : 0 < st.F.usize then
        let pivot : ILit := line.witnessLits.getD 0 (st.F.ugetFin ⟨0, hu⟩)
        if pivot != st.F.ugetFin ⟨0, hu⟩ then error false else
        let st := { st with σ := assumeWitness st.σ pivot line.witnessLits line.witnessMaps }

        -- Loop through each clause in the formula to check RAT conditions
        -- The Bool is true if the check succeeds on all clauses, false otherwise
        let Fsize := st.F.size
        let rec loop (i cachedRatHintIndex bumpCounter : Nat) (τ : PPA) : PPA × Bool :=
          if hi : i < Fsize then
            if h_del : st.F.isDeletedFin ⟨i, hi⟩ = true then
              loop (i + 1) cachedRatHintIndex bumpCounter τ
            else
              -- First, check how the ith clause is reduced by σ
              match reduce st.σ st.F ⟨i, hi⟩ with
              | .satisfied => loop (i + 1) cachedRatHintIndex bumpCounter τ
              | .notReduced => loop (i + 1) cachedRatHintIndex bumpCounter τ
              | _ =>
                -- dbg_trace s!"Clause index {i} is a RAT candidate"
                if bumpCounter < line.ratHintIndexes.size then
                  -- Find the corresponding RAT hint
                  match findRATHintIndex cachedRatHintIndex i line.ratHintIndexes with
                  | none => ⟨τ, false⟩
                  | some ⟨ratIndex, hr⟩ =>
                    -- Assume the negation of the RAT clause
                    match assumeRATClause st.F ⟨i, hi⟩ st.σ τ with
                    | ⟨τ, true⟩ => loop (i + 1) (ratIndex + 1) (bumpCounter + 1) τ.bump
                    | ⟨τ, false⟩ =>
                      match applyUPHints st.F 0 τ (line.ratHints.get ⟨ratIndex, by rw [line.ratSizesEq] at hr; exact hr⟩) with
                      | (τ, .unit) => ⟨τ, false⟩
                      | (τ, .contra) => loop (i + 1) (ratIndex + 1) (bumpCounter + 1) τ.bump
                      | (τ, .err) => ⟨τ, false⟩
                else ⟨τ, false⟩
          else ⟨τ, true⟩
        termination_by st.F.size - i

        match loop 0 0 0 st.τ with
        | ⟨_, false⟩ => error false
        | ⟨τ, true⟩ => ok { st with τ := τ, F := st.F.commit }
      else error false

/-def checkLine (F : RangeArray ILit) (τ : PPA) (σ : PS) (line : SRAdditionLine)
    : Except Bool (RangeArray ILit × PPA × PS) :=
  --let ⟨C, wL, wM, upHints, ratHintIndexes, ratHints, _, _⟩ := line
  -- dbg_trace s!"{C}, {wL}, {wM}"
  -- dbg_trace s!"{upHints}, {ratHintIndexes}, {ratHints}"
  match uAssumeNegatedForM F τ.reset (line.ratHints.size + 1) with
  | error _ =>
    -- dbg_trace s!"Assuming the negation of the candidate clause had error"
    error false
  | ok τ =>
    -- dbg_trace s!"Assumed negation of clause succeeded"
    -- Evaluate the UP hints, with "# of RAT hints" as the offset
    match applyUPHints F (line.ratHints.size + 1) τ line.upHints with
    | (_, .err) =>
      -- dbg_trace s!"Applying UP hints encountered an error"
      error false
    | (τ, .contra) =>
      -- dbg_trace s!"Applying UP hints found contradiction before RAT"
      if F.usize = 0 then error true  -- If the clause is empty, we have a successful contradiction proof
      else ok ⟨F.commit, τ, σ⟩

    | (τ, .unit) =>
      -- If the clause is empty, we should have derived UP contradiction by now
      if hu : 0 < F.usize then
        let pivot : ILit := line.witnessLits.getD 0 (F.ugetFin ⟨0, hu⟩)
        if pivot != F.ugetFin ⟨0, hu⟩ then error false else
        let σ := assumeWitness σ pivot line.witnessLits line.witnessMaps

        -- Loop through each clause in the formula to check RAT conditions
        -- The Bool is true if the check succeeds on all clauses, false otherwise
        let Fsize := F.size
        let rec loop (i cachedRatHintIndex bumpCounter : Nat) (τ : PPA) : PPA × Bool :=
          if hi : i < Fsize then
            if h_del : F.isDeletedFin ⟨i, hi⟩ = true then
              loop (i + 1) cachedRatHintIndex bumpCounter τ
            else
              -- First, check how the ith clause is reduced by σ
              match reduce σ F ⟨i, hi⟩ with
              | .satisfied => loop (i + 1) cachedRatHintIndex bumpCounter τ
              | .notReduced => loop (i + 1) cachedRatHintIndex bumpCounter τ
              | _ =>
                -- dbg_trace s!"Clause index {i} is a RAT candidate"
                if bumpCounter < line.ratHintIndexes.size then
                  -- Find the corresponding RAT hint
                  match findRATHintIndex cachedRatHintIndex i line.ratHintIndexes with
                  | none => ⟨τ, false⟩
                  | some ⟨ratIndex, hr⟩ =>
                    -- Assume the negation of the RAT clause
                    match assumeRATClause F ⟨i, hi⟩ σ τ with
                    | ⟨τ, true⟩ => loop (i + 1) (ratIndex + 1) (bumpCounter + 1) τ.bump
                    | ⟨τ, false⟩ =>
                      match applyUPHints F 0 τ (line.ratHints.get ⟨ratIndex, by rw [line.ratSizesEq] at hr; exact hr⟩) with
                      | (τ, .unit) => ⟨τ, false⟩
                      | (τ, .contra) => loop (i + 1) (ratIndex + 1) (bumpCounter + 1) τ.bump
                      | (τ, .err) => ⟨τ, false⟩
                else ⟨τ, false⟩
          else ⟨τ, true⟩
        termination_by F.size - i

        match loop 0 0 0 τ with
        | ⟨_, false⟩ => error false
        | ⟨τ, true⟩ => ok ⟨F.commit, τ, σ⟩
      else error false -/

end SR
