/-

Theory and implementation for the SR proof system and a checker.

Authors: Cayden Codel
Carnegie Mellon University

-/

import Experiments.ProofChecking.PPA
import Experiments.ProofChecking.PS
import Experiments.ProofChecking.RangeArray

import LeanSAT.Data.Cnf
import LeanSAT.Data.ICnf
import LeanSAT.Model.PropFun
import LeanSAT.Model.Subst

open LeanSAT LeanSAT.Model Nat
open PPA PS LitVar ILit IVar LawfulLitVar PropFun
open Except

namespace PPA

def unitPropFlat (τ : PPA) (F : RangeArray ILit) (i : Nat) : MUPResult :=
  match F.foldlM_index (pevalUP τ) none i with
  | ok none => .falsified
  | ok (some lit) => .unit lit
  | error .satisfied => .satisfied
  | error .multipleUnassignedLiterals => .multipleUnassignedLiterals

-- TODO: Some correctness theorem relating this to unitProp

end PPA

namespace PS

def reduceFlat (σ : PS) (F : RangeArray ILit) (i : Nat) : ReductionResult :=
  F.foldl_index (seval_fold_fn' σ) .notReduced i

end PS

namespace SR

inductive UPResult
  | checked : UPResult
  | checkError : UPResult

open UPResult

structure SRLine where
  clause : IClause
  witness_lits : Array ILit
  witness_maps : Array (IVar × ILit)
  up_hints : Array Nat                -- Already 0-indexed clause IDs into the accumulated formula
  rat_hints : Array (Nat × Array Nat) -- Already 0-indexed clause IDs into the accumulated formula

structure SRState where
  F : ICnf -- Accumulated formula
  τ : PPA  -- Partial assignment, to store candidate and RAT negations
  σ : PS   -- Substitution, for the witness

-- Applies a single unit propagation step
-- On success, we set the unit literal in τ with the offset
-- On falsification of the clause, we error with .checked
-- On satisfied clause or multiple unassigned literals, we error with checkError
def applyUPHint (F : ICnf) (offset : Nat) (τ : PPA) (hint : Nat) : Except (PPA × UPResult) PPA :=
  if h_hint : hint < F.size then
    let C := F.get ⟨hint, h_hint⟩
    match τ.unitProp C with
    | .falsified => error ⟨τ, .checked⟩
    | .satisfied =>
      --dbg_trace s!"ERROR: UP found a satisfied clause"
      error ⟨τ, .checkError⟩
    | .multipleUnassignedLiterals =>
      --dbg_trace s!"ERROR: UP found a non-unit clause"
      error ⟨τ, .checkError⟩
    | .unit l => ok (τ.setLitFor l offset)
  else
    --dbg_trace s!"ERROR: Hint out of bounds"
    error ⟨τ, .checkError⟩

def scanRATHints (clauseId : Nat) (ratHints : Array (Nat × Array Nat)) : Option (Fin ratHints.size) :=
  match ratHints.foldlM (init := 0) (fun counter ⟨hint, _⟩ =>
        if hint = clauseId then error counter
        else ok (counter + 1)) with
  | ok _ => none
  | error index =>
    if hi : index < ratHints.size then some ⟨index, hi⟩
    else none

-- Finds the RAT hint pair that matches the clauseId
def findRATHintIndex (ratIndex clauseId : Nat) (ratHints : Array (Nat × Array Nat)) : Option (Fin ratHints.size) :=
  -- If the RAT hints are sorted, then check the one under our "cached pointer" first
  if h_index : ratIndex < ratHints.size then
    let ⟨ratClauseIndex, _⟩ := ratHints.get ⟨ratIndex, h_index⟩
    if ratClauseIndex = clauseId then some ⟨ratIndex, h_index⟩
    else scanRATHints clauseId ratHints
  else
    scanRATHints clauseId ratHints

-- Assuming that (C|σ) is reduced but not satisfied and that C is a RAT clause, sets τ ← τ ⊓ (C|σ)ᶜ
def assumeRATClause (C : IClause) (σ : PS) (τ : PPA) : Except PPA PPA :=
  C.foldlM (init := τ) (fun τ lit =>
    match σ.litValue lit with
    | Sum.inr true => error τ       -- (C|σ) is satisfied, so return early to report satisfied
    | Sum.inr false => ok τ         -- Ignore the literal
    | Sum.inl l =>
      match τ.litValue? l with
      | some true => error τ    -- (C|σ)|τ is satisfied, so return early to report satisfied
      | some false => ok τ      -- Its negation is true in τ, so ignore the literal
      | none => ok (τ.setLit (-l)))

-- Set the witness substitution σ from the provided mapping, resetting σ first
def assumeWitness (σ : PS) (pivot : ILit) (A₁ : Array ILit) (A₂ : Array (IVar × ILit)) : PS :=
  ((σ.reset.setLits A₁).setVars A₂).setLit pivot

structure FlatState where
  formula : RangeArray ILit -- Accumulated formula
  τ : PPA                   -- Partial assignment, to store candidate and RAT negations
  σ : PS                    -- Substitution, for the witness

-- Applies a single unit propagation step
-- On success, we set the unit literal in τ with the offset
-- On falsification of the clause, we error with .checked
-- On satisfied clause or multiple unassigned literals, we error with checkError
def applyUPHintFlat (F : RangeArray ILit) (offset : Nat) (τ : PPA) (hint : Nat) : Except (PPA × UPResult) PPA :=
  if hint < F.size then
    match τ.unitPropFlat F hint with
    | .falsified => error ⟨τ, .checked⟩
    | .satisfied =>
      -- dbg_trace s!"ERROR: UP found a satisfied clause"
      error ⟨τ, .checkError⟩
    | .multipleUnassignedLiterals =>
      -- dbg_trace s!"ERROR: UP found a non-unit clause"
      error ⟨τ, .checkError⟩
    | .unit l =>
      -- dbg_trace s!"    Hint {hint} makes clause unit on literal {l}"
      ok (τ.setLitFor l offset)
  else
    -- dbg_trace s!"ERROR: Hint out of bounds"
    error ⟨τ, .checkError⟩

-- Assuming that (C|σ) is reduced but not satisfied and that C is a RAT clause, sets τ ← τ ⊓ (C|σ)ᶜ
def assumeRATClauseFlat (F : RangeArray ILit) (i : Nat) (σ : PS) (τ : PPA) : Except PPA PPA :=
  F.foldlM_index (i := i) (init := τ) (fun τ lit =>
    match σ.litValue lit with
    | Sum.inr true => error τ       -- (C|σ) is satisfied, so return early to report satisfied
    | Sum.inr false => ok τ         -- Ignore the literal
    | Sum.inl l =>
      match τ.litValue? l with
      | some true => error τ    -- (C|σ)|τ is satisfied, so return early to report satisfied
      | some false => ok τ      -- Its negation is true in τ, so ignore the literal
      | none => ok (τ.setLit (-l)))

-- Check each clause in the formula.
-- C is the current clause in the formula to be checked for the RAT property under σ and τ
-- If C is reduced by σ, then it is RAT. Find a RAT hint and uses the RAT UP hints to derive contradiction.
def checkClauseFlat (F : RangeArray ILit) (σ : PS) (ratHints : Array (Nat × Array Nat))
    (p : PPA × Nat × Nat) (i : Nat) : Except Unit (PPA × Nat × Nat) :=
  let ⟨τ, ratIndex, bumpCounter⟩ := p
  match σ.reduceFlat F i with
  | .satisfied => ok (τ, ratIndex, bumpCounter)
  | .notReduced => ok (τ, ratIndex, bumpCounter)
  | _ =>
    -- dbg_trace s!"     Clause {i} is reduced, checking for RAT"
    -- We expect a RAT clause. Check if we have bumps left
    if bumpCounter < ratHints.size then
      -- Curiously, if the clause is completely falsified, we can still succeed
      -- on the check (which sr-check does not allow). This is because a UP
      -- derivation on a completely falsified clause is a global UP derivation,
      -- and so the certificate can be reduced quite a bit.

      -- Find a RAT hint matching the clause (add one to the current index, due to 1-indexing)
      -- We hope that the hints are sorted, but they don't have to be
      match findRATHintIndex ratIndex i ratHints with
      | none =>
        -- dbg_trace s!"Clause {i} found to be missing a RAT hint"
        error ()
      | some rI =>
        let ⟨_, hints⟩ := ratHints.get rI
        match assumeRATClauseFlat F i σ τ with
        -- If the clause is satisfied under σ and τ, then we move to the next iteration
        | error τ => ok (τ.bump, rI.val + 1, bumpCounter + 1)

        -- Otherwise, we have assumed the negation of the RAT clause
        -- Now check for UP derivation through its hints
        | ok τ =>
          match hints.foldlM (init := τ) (applyUPHintFlat F 0) with
          | error (τ, .checked) => ok (τ.bump, rI.val + 1, bumpCounter + 1)
          | error (_, .checkError) =>
            -- dbg_trace s!"ERROR: UP failed"
            error ()
          | ok _ =>
            -- dbg_trace s!"ERROR: UP succeeded, but didn't lead to contradiction"
            error ()
    -- We error if the bumpCounter equals the number of RAT hints, since that
    -- means we bumped the assignment too many times, clearing out the
    -- assumption of the candidate clause
    else
      -- dbg_trace s!"ERROR: Bump counter exceeded number of RAT hints"
      error ()

def checkLineFlat (S : FlatState) (line : SRLine) : Except Bool FlatState :=
  -- dbg_trace s!"About to check line with clause {line.clause}"
  let ⟨F, τ, σ⟩ := S
  let ⟨C, w_tf, w_maps, UPhints, RAThints⟩ := line

  -- Assumes the negation of the candidate clause, with "# of RAT hints" offset
  match assumeNegatedClauseFor τ.reset C (RAThints.size + 1) with
  | error _ =>
    -- dbg_trace s!"ERROR: Assumption of clause failed"
    error false
  | ok τ =>

  -- dbg_trace s!"Assumed negation of {C} with {RAThints.size + 1} offset"

  -- Evaluate the UP hints, with "# of RAT hints" offset
  -- We add one more than normal to help with proving
  match UPhints.foldlM (init := τ) (applyUPHintFlat F (RAThints.size + 1)) with
  -- The clause led to contradiction via unit propagation
  | error ⟨τ, .checked⟩ =>
    if C = #[] then error true       -- If the clause is empty, we have a successful proof
    else ok ⟨F.add C, τ, σ⟩ -- The clause is redundant, so add it to the formula

  -- Unit propagation failed due to multiple unassigned literals, satisfied clause, or out-of-bounds
  | error ⟨_, _⟩ =>
    -- dbg_trace s!"ERROR: UP failed"
    error false

  -- Unit propagation worked but didn't lead to contradiction, so continue to RAT checking
  | ok τ =>

    -- dbg_trace s!"  UP succeeded, checking for RAT"

    -- If the clause is empty, then we should have derived UP contradiction by now
    if hCw : 0 < C.size ∧ 0 < w_tf.size then
      if C.get ⟨0, hCw.1⟩ ≠ w_tf.get ⟨0, hCw.2⟩ then
        -- dbg_trace s!"Pivot doesn't agree with 0th literal"
        error false
      else

      -- Assume the witness, under substitution (the function call resets σ)
      let σ := assumeWitness σ (C.get ⟨0, hCw.1⟩) w_tf w_maps
      -- dbg_trace s!"{σ}"

      -- Go through each clause in the formula to check RAT
      let Fsize := F.size
      let rec loop (i : Nat) (p : PPA × Nat × Nat) := do
        if i < Fsize then
          loop (i + 1) (← checkClauseFlat F σ RAThints p i)
        else
          pure p
        termination_by Fsize - i

      --match F.foldlM_over_indexes (init := (⟨τ, 0, 0⟩ : PPA × Nat × Nat)) (checkClauseFlat F σ RAThints) with
      match loop 0 ⟨τ, 0, 0⟩ with
      | error () =>
        -- dbg_trace s!"ERROR: RAT check failed"
        error false
      | ok (τ, _) =>
        -- dbg_trace s!"RAT check succeeded, adding clause {C}"
        ok ⟨F.add C, τ, σ⟩ -- The RAT hint checked, so we continue

    else
      -- dbg_trace s!"ERROR: Either the clause or the true/false mappings are empty"
      error false

end SR
