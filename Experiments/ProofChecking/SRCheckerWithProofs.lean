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

/-
def unitPropFlat (τ : PPA) (F : RangeArray ILit) (i : Nat) : MUPResult :=
  match F.foldlM_index (pevalUP τ) none i with
  | ok none => .falsified
  | ok (some lit) => .unit lit
  | error true => .satisfied
  | error false => .multipleUnassignedLiterals -/

-- TODO: Some correctness theorem relating this to unitProp

end PPA

namespace PS

/-
def seval (σ : PS) (p : Bool × Bool) (l : ILit) : Except Unit (Bool × Bool) :=
  -- Has there been a non-id map, and has there been a literal that's unassigned
  let ⟨reduced?, unassigned?⟩ := p
  match σ.litValue l with
  | .tr => error ()
  | .fls => ok (true, unassigned?)
  | .lit lit => ok (reduced? || (l != lit), true) -/

/-
def reduceFlat (σ : PS) (F : RangeArray ILit) (i : Nat) : ReductionResult :=
  match F.foldlM_index (seval σ) false i with
  | ok true => .reduced
  | ok false => .notReduced
  | error _ => .satisfied
-/
-- TODO: Some correctness theorem releating this to reduce

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

-- Check each clause in the formula.
-- C is the current clause in the formula to be checked for the RAT property under σ and τ
-- If C is reduced by σ, then it is RAT. Find a RAT hint and uses the RAT UP hints to derive contradiction.
def checkClause (F : ICnf) (σ : PS) (ratHints : Array (Nat × Array Nat))
    (p : PPA × Nat × Nat × Nat) (C : IClause) : Except Unit (PPA × Nat × Nat × Nat) :=
  let ⟨τ, ratIndex, index, bumpCounter⟩ := p
  --let F := dbgTraceIfShared "Formula in checkClause" F
  match σ.seval_fold C with
  | .satisfied => ok (τ, ratIndex, index + 1, bumpCounter)
  | .notReduced => ok (τ, ratIndex, index + 1, bumpCounter)
  | _ =>
    -- We expect a RAT clause. Check if we have bumps left
    if bumpCounter < ratHints.size then
      -- Curiously, if the clause is completely falsified, we can still succeed
      -- on the check (which sr-check does not allow). This is because a UP
      -- derivation on a completely falsified clause is a global UP derivation,
      -- and so the certificate can be reduced quite a bit.

      -- Find a RAT hint matching the clause
      -- We hope that the hints are sorted, but they don't have to be
      match findRATHintIndex ratIndex index ratHints with
      | none => error ()
      | some rI =>
        let ⟨_, hints⟩ := ratHints.get rI
        match assumeRATClause C σ τ with
        -- If the clause is satisfied under σ and τ, then we move to the next iteration
        | error τ => ok (τ.bump, rI.val + 1, index + 1, bumpCounter + 1)

        -- Otherwise, we have assumed the negation of the RAT clause
        -- Now check for UP derivation through its hints
        | ok τ =>
          match hints.foldlM (init := τ) (applyUPHint F 0) with
          | error (τ, .checked) => ok (τ.bump, rI.val + 1, index + 1, bumpCounter + 1)
          | error (_, .checkError) => error ()
          | ok _ => error ()
    -- We error if the bumpCounter equals the number of RAT hints, since that
    -- means we bumped the assignment too many times, clearing out the
    -- assumption of the candidate clause
    else error ()


def checkLine (S : SRState) (line : SRLine) : Except Bool SRState :=
  let ⟨F, τ, σ⟩ := dbgTraceIfShared "Formula at start of checkLine" S
  let ⟨C, w_tf, w_maps, UPhints, RAThints⟩ := line

  -- Assumes the negation of the candidate clause, with "# of RAT hints" offset
  match assumeNegatedClauseFor τ.reset C (RAThints.size + 1) with
  | error _ => error false
  | ok τ =>

  -- Evaluate the UP hints, with "# of RAT hints" offset
  -- We add one more than normal to help with proving
  match UPhints.foldlM (init := τ) (applyUPHint F (RAThints.size + 1)) with
  -- The clause led to contradiction via unit propagation
  | error ⟨τ, .checked⟩ =>
    if C = #[] then error true       -- If the clause is empty, we have a successful proof
    else ok ⟨F.addClause C, τ, σ⟩ -- The clause is redundant, so add it to the formula

  -- Unit propagation failed due to multiple unassigned literals, satisfied clause, or out-of-bounds
  | error ⟨_, _⟩ => error false

  -- Unit propagation worked but didn't lead to contradiction, so continue to RAT checking
  | ok τ =>

    -- If the clause is empty, then we should have derived UP contradiction by now
    if hCw : 0 < C.size ∧ 0 < w_tf.size then
      if C.get ⟨0, hCw.1⟩ ≠ w_tf.get ⟨0, hCw.2⟩ then error false else

      -- Assume the witness, under substitution (the function call resets σ)
      let σ := assumeWitness σ (C.get ⟨0, hCw.1⟩) w_tf w_maps
      let F := dbgTraceIfShared "Formula" F

      -- Go through each clause in the formula to check RAT
      match F.foldlM (init := (⟨τ, 0, 0, 0⟩ : PPA × Nat × Nat × Nat)) (checkClause F σ RAThints) with
      | error () => error false
      | ok (τ, _) =>
        --let F := dbgTraceIfShared "Formula at end of checkLine" F
        ok ⟨F.addClause C, τ, σ⟩ -- The RAT hint checked, so we continue

    else error false

def checkProof (F : ICnf) (proof : Array SRLine) : Bool :=
  let τ := PPA.new 100
  let σ := PS.new 100
  match proof.foldlM (init := ⟨F, τ, σ⟩) checkLine with
  | ok _ => false
  | error false => false
  | error true => true

/-! # flat version -/

/-
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
      --dbg_trace s!"ERROR: UP found a satisfied clause"
      error ⟨τ, .checkError⟩
    | .multipleUnassignedLiterals =>
      --dbg_trace s!"ERROR: UP found a non-unit clause"
      error ⟨τ, .checkError⟩
    | .unit l =>
      --dbg_trace s!"    Hint {hint} makes clause unit on literal {l}"
      ok (τ.setLitFor l offset)
  else
    --dbg_trace s!"ERROR: Hint out of bounds"
    error ⟨τ, .checkError⟩

-- Assuming that (C|σ) is reduced but not satisfied and that C is a RAT clause, sets τ ← τ ⊓ (C|σ)ᶜ
def assumeRATClauseFlat (F : RangeArray ILit) (i : Nat) (σ : PS) (τ : PPA) : Except PPA PPA :=
  F.foldlM_index (i := i) (init := τ) (fun τ lit =>
    match σ.litValue lit with
    | .tr => error τ       -- (C|σ) is satisfied, so return early to report satisfied
    | .fls => ok τ         -- Ignore the literal
    | .lit l =>
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
    --dbg_trace s!"     Clause {i} is reduced, checking for RAT"
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
        --dbg_trace s!"Clause {i} found to be missing a RAT hint"
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
            --dbg_trace s!"ERROR: UP failed"
            error ()
          | ok _ =>
            --dbg_trace s!"ERROR: UP succeeded, but didn't lead to contradiction"
            error ()
    -- We error if the bumpCounter equals the number of RAT hints, since that
    -- means we bumped the assignment too many times, clearing out the
    -- assumption of the candidate clause
    else
      --dbg_trace s!"ERROR: Bump counter exceeded number of RAT hints"
      error ()

def checkLineFlat (S : FlatState) (line : SRLine) : Except Bool FlatState :=
  --dbg_trace s!"About to check line with clause {line.clause}"
  let ⟨F, τ, σ⟩ := S
  let ⟨C, w_tf, w_maps, UPhints, RAThints⟩ := line

  -- Assumes the negation of the candidate clause, with "# of RAT hints" offset
  match assumeNegatedClauseFor τ.reset C (RAThints.size + 1) with
  | error _ =>
    --dbg_trace s!"ERROR: Assumption of clause failed"
    error false
  | ok τ =>

  --dbg_trace s!"Assumed negation of {C} with {RAThints.size + 1} offset"

  -- Evaluate the UP hints, with "# of RAT hints" offset
  -- We add one more than normal to help with proving
  match UPhints.foldlM (init := τ) (applyUPHintFlat F (RAThints.size + 1)) with
  -- The clause led to contradiction via unit propagation
  | error ⟨τ, .checked⟩ =>
    if C = #[] then error true       -- If the clause is empty, we have a successful proof
    else ok ⟨F.add C, τ, σ⟩ -- The clause is redundant, so add it to the formula

  -- Unit propagation failed due to multiple unassigned literals, satisfied clause, or out-of-bounds
  | error ⟨_, _⟩ =>
    --dbg_trace s!"ERROR: UP failed"
    error false

  -- Unit propagation worked but didn't lead to contradiction, so continue to RAT checking
  | ok τ =>

    --dbg_trace s!"  UP succeeded, checking for RAT"

    -- If the clause is empty, then we should have derived UP contradiction by now
    if hCw : 0 < C.size ∧ 0 < w_tf.size then
      if C.get ⟨0, hCw.1⟩ ≠ w_tf.get ⟨0, hCw.2⟩ then
        --dbg_trace s!"Pivot doesn't agree with 0th literal"
        error false
      else

      -- Assume the witness, under substitution (the function call resets σ)
      let σ := assumeWitness σ (C.get ⟨0, hCw.1⟩) w_tf w_maps

      -- Go through each clause in the formula to check RAT
      match F.foldlM_over_indexes (init := (⟨τ, 0, 0⟩ : PPA × Nat × Nat)) (checkClauseFlat F σ RAThints) with
      | error () =>
        --dbg_trace s!"ERROR: RAT check failed"
        error false
      | ok (τ, _) =>
        --dbg_trace s!"RAT check succeeded, adding clause {C}"
        ok ⟨F.add C, τ, σ⟩ -- The RAT hint checked, so we continue

    else
      --dbg_trace s!"ERROR: Either the clause or the true/false mappings are empty"
      error false

#exit
-/

/-! # correctness -/

-- TODO: Exists a PS, or forall PS that meet the condition?
-- TODO: Can be "generalized" to one for (IVar → PropForm IVar), or maybe just substitutions in general
theorem SR_core {F : ICnf} {C : IClause} {σ : PS} :
    PropFun.substL C σ.toSubst = ⊤ → F.toPropFun ⊓ Cᶜ ≤ PropFun.substL F σ.toSubst →
    eqsat F (F ⊓ C.toPropFun) := by
  intro hC hFC
  constructor
  · rintro ⟨τ, hτF⟩
    by_cases hτC : τ ⊨ C.toPropFun
    · use τ
      rw [satisfies_conj]
      exact ⟨hτF, hτC⟩
    · replace hFC := entails_ext.mp hFC τ
      simp [satisfies_conj, and_imp, -satisfies_substL] at hFC
      replace hFC := hFC hτF hτC
      have : τ ⊨ PropFun.substL C σ.toSubst := by rw [hC]; rfl
      simp at hFC this
      use PropAssignment.subst (fun x => ⟦σ.toSubst x⟧) τ
      rw [satisfies_conj]
      exact ⟨hFC, this⟩
  · rintro ⟨τ, hτ⟩
    rw [satisfies_conj] at hτ
    exact ⟨τ, hτ.1⟩

theorem assumeWitness_subst {C : IClause} (hC : 0 < C.size) :
      ∀ σ A₁ A₂, PropFun.substL C.toPropFun (assumeWitness σ (C.get ⟨0, hC⟩) A₁ A₂).toSubst = ⊤ := by
  intro σ A₁ A₂
  rw [assumeWitness]
  simp [PropFun.ext_iff]
  intro τ
  rw [Clause.satisfies_iff]
  use C.get ⟨0, hC⟩
  constructor
  · simp [← Array.mem_data]; exact Array.getElem_mem_data C hC
  · simp [LitVar.satisfies_iff, PropAssignment.subst]
    sorry
  done

-- TODO: Is the standard `≤ ⊥` or `= ⊥`?
theorem applyUPHint_checked {F : ICnf} {offset : Nat} {τ τ' : PPA} {hint : Nat} :
    applyUPHint F offset τ hint = .error (τ', .checked) →
      τ = τ' ∧ F.toPropFun ⊓ τ ≤ ⊥ := by
  rw [applyUPHint]
  split <;> simp
  split <;> simp
  rintro rfl; use rfl
  rename hint < F.size => h_hint
  rename (unitProp τ _ = _) => h_up
  have := contradiction_of_UP_falsified h_up
  rw [inf_comm] at this
  rw [← le_bot_iff]
  exact le_trans (inf_le_inf_right τ.toPropFun (Cnf.ith_le ⟨hint, h_hint⟩)) this

-- TODO: Do we need everything in our spec?
-- Also, the spec is not strong enough to derive ge_of_applyUPHint_ok because
-- it doesn't comment on the state of F[hint]. See
theorem applyUPHint_ok {F : ICnf} {offset : Nat} {τ τ' : PPA} {hint : Nat} :
    applyUPHint F offset τ hint = .ok τ' →
      --∃ l, l ∈ F[hint] ∧ τ.litValue? l = none ∧ τ' = τ.setLitFor l offset
      ∃ l, τ.litValue? l = none ∧ τ' = τ.setLitFor l offset := by
  rw [applyUPHint]
  split <;> simp
  split <;> simp
  rename hint < F.size => h_hint
  rename ILit => lit
  rename (unitProp τ _ = _) => h_up
  rintro rfl
  rcases extended_of_UP_unit h_up with ⟨_, h₂, _⟩
  exact ⟨lit, h₂, rfl⟩

theorem ge_of_applyUPHint_ok {F : ICnf} {offset : Nat} {τ τ' : PPA} {hint : Nat} :
    applyUPHint F offset τ hint = .ok τ' → F.toPropFun ⊓ τ ≤ τ' := by
  rw [applyUPHint]
  split <;> simp
  split <;> simp
  rename hint < F.size => h_hint
  rename ILit => lit
  rename (unitProp τ _ = _) => h_up
  rintro rfl
  rcases extended_of_UP_unit h_up with ⟨_, h₂, h₃⟩
  rw [toPropFun_setLitFor_eq_setLit, toPropFun_setLit_of_none h₂]
  conv at h₃ => rhs; rw [inf_comm]
  apply le_trans _ h₃
  apply inf_le_inf_right
  exact Cnf.ith_le ⟨hint, h_hint⟩

-- TODO: Package up τ = τ' invariants into "agreeOn" or "unchanged" or something
theorem fold_UP_checked {F : ICnf} {A : Array Nat} {offset : Nat} {τ τ' : PPA} :
    A.foldlM (init := τ) (applyUPHint F offset) = error (τ', .checked) →
      F.toPropFun ⊓ τ ≤ ⊥ ∧ extended τ τ' offset := by
  have ⟨A⟩ := A
  rw [Array.foldlM_eq_foldlM_data]
  induction' A with hint hints ih generalizing τ
  · simp [pure, Except.pure]
  · simp [-le_bot_iff]
    intro h
    match h_apply : applyUPHint F offset τ hint with
    | error (τ₁, .checked) =>
      rcases applyUPHint_checked h_apply with ⟨rfl, hτ⟩
      use hτ
      simp [h_apply] at h; injection h; rename _ => h
      injection h; rename τ = τ' => heq; subst heq
      simp [PPA.extended]
      intro v hcon h
      exact absurd h hcon
    | error (τ₁, .checkError) =>
      simp [h_apply] at h; injection h; rename _ => h
      injection h
      contradiction
    | ok τ₁ =>
      rcases applyUPHint_ok h_apply with ⟨l, hl, rfl⟩
      -- TODO: What is a better hyp/spec?
      have hFτ := ge_of_applyUPHint_ok h_apply
      simp [h_apply] at h
      rcases ih h with ⟨ih₁, ih₂⟩
      rw [toPropFun_setLitFor_eq_setLit, toPropFun_setLit_of_none hl, ← inf_assoc] at ih₁
      rw [toPropFun_setLitFor_eq_setLit, toPropFun_setLit_of_none hl] at hFτ
      have := inf_le_inf_left F.toPropFun hFτ
      simp_rw [← inf_assoc, inf_idem] at this
      exact ⟨le_trans this ih₁, extended_trans (extended_setLitFor_of_none hl offset) ih₂⟩

theorem fold_UP_ok {F : ICnf} {A : Array Nat} {offset : Nat} {τ τ' : PPA} :
    A.foldlM (init := τ) (applyUPHint F offset) = ok τ' →
      F.toPropFun ⊓ τ ≤ τ' ∧ extended τ τ' offset := by
  have ⟨A⟩ := A
  rw [Array.foldlM_eq_foldlM_data]
  induction' A with hint hints ih generalizing τ
  · simp [pure, Except.pure]; rintro rfl; exact ⟨inf_le_right, extended_refl _ _⟩
  · simp
    intro h
    match h_apply : applyUPHint F offset τ hint with
    | error _ => simp [h_apply] at h; injection h
    | ok τ₁ =>
      simp [h_apply] at h
      rcases ih h with ⟨ih₁, ih₂⟩
      rcases applyUPHint_ok h_apply with ⟨l, hl, rfl⟩
      have := inf_le_inf_left F.toPropFun (ge_of_applyUPHint_ok h_apply)
      rw [← inf_assoc, inf_idem] at this
      exact ⟨le_trans this ih₁, extended_trans (extended_setLitFor_of_none hl offset) ih₂⟩

theorem assumeRATClause_ok {C : IClause} {σ : PS} {τ τ' : PPA} :
    assumeRATClause C σ τ = ok τ' →
      τ.toPropFun ⊓ (PropFun.substL C σ.toSubst)ᶜ ≤ τ' ∧ extended τ τ' 0 := by
  have ⟨C⟩ := C
  rw [assumeRATClause, Array.foldlM_eq_foldlM_data]
  induction' C with l ls ih generalizing τ
  · simp [pure, Except.pure]; rintro rfl; exact ⟨le_refl _, extended_refl _ _⟩
  · simp; split <;> rename _ => hσ
    · intro hcon; injection hcon
    · intro h
      rw [litValue_fls_iff] at hσ
      simp [hσ]
      exact ih h
    · rename ILit => mapped_lit
      rw [litValue_lit_iff] at hσ
      simp [hσ]
      split <;> rename _ => h_mapped_lit <;> try simp
      · intro hcon; injection hcon
      · intro h
        rcases ih h with ⟨ih₁, ih₂⟩
        constructor
        · apply le_trans _ ih₁
          apply inf_le_inf_left
          exact inf_le_right
        · exact ih₂
      · intro h
        rcases ih h with ⟨ih₁, ih₂⟩
        rw [← litValue?_negate_none_iff] at h_mapped_lit
        simp [toPropFun_setLit_of_none h_mapped_lit, inf_assoc] at ih₁
        exact ⟨ih₁, extended_trans (extended_setLitFor_of_none h_mapped_lit 0) ih₂⟩

theorem assumeRATClause_error {C : IClause} {σ : PS} {τ τ' : PPA} :
    assumeRATClause C σ τ = error τ' →
      τ.toPropFun ≤ (PropFun.substL C σ.toSubst) ∧ extended τ τ' 0 := by
  have ⟨C⟩ := C
  rw [assumeRATClause, Array.foldlM_eq_foldlM_data]
  induction' C with l ls ih generalizing τ
  · simp [pure, Except.pure]
  · simp; split <;> rename _ => hσ
    · intro h; injection h; rename _ => h; subst h
      rw [litValue_tr_iff] at hσ
      simp [hσ]
    · intro h
      rw [litValue_fls_iff] at hσ
      simp [hσ]
      exact ih h
    · rename ILit => mapped_lit
      rw [litValue_lit_iff] at hσ
      simp [hσ]
      split <;> rename _ => h_mapped_lit <;> try simp
      · intro h; injection h; rename _ => h; subst h
        rw [litValue?_true_iff] at h_mapped_lit
        exact ⟨le_trans h_mapped_lit le_sup_left, extended_refl _ _⟩
      · intro h
        rw [litValue?_false_iff] at h_mapped_lit
        rcases ih h with ⟨ih₁, ih₂⟩
        exact ⟨le_trans ih₁ le_sup_right, ih₂⟩
      · intro h
        rw [← litValue?_negate_none_iff] at h_mapped_lit
        rcases ih h with ⟨ih₁, ih₂⟩
        simp [toPropFun_setLit_of_none h_mapped_lit] at ih₁
        constructor
        · exact sdiff_le_iff.mp ih₁
        · exact extended_trans (extended_setLitFor_of_none h_mapped_lit 0) ih₂

-- Check each clause in the formula.
-- C is the current clause in the formula to be checked for the RAT property under σ and τ
-- If C is reduced by σ, then it is RAT. Find a RAT hint and uses the RAT UP hints to derive contradiction.
--def checkClause (F : ICnf) (σ : PS) (ratHints : Array (Nat × Array Nat))
--    (p : PPA × Nat) (index : Fin F.size) (C : IClause) : Except Unit (PPA × Nat)

theorem checkClause_ok {F : ICnf} {σ : PS} {ratHints : Array (Nat × Array Nat)}
    {τ τ' : PPA} {ratIndex ratIndex' index index' bc bc' : Nat} {C : IClause} :
    C ∈ F → uniform τ ((ratHints.size + 1) - bc) →
      checkClause F σ ratHints ⟨τ, ratIndex, index, bc⟩ C = ok (τ', ratIndex', index', bc') →
      F.toPropFun ⊓ τ ≤ PropFun.substL C σ.toSubst ∧
      ((bc' = bc ∧ τ' = τ) ∨
       (bc' = bc + 1 ∧ uniform τ' ((ratHints.size + 1) - bc') ∧ τ'.toPropFun = τ.toPropFun)) := by
  intro hC h_uni
  simp [checkClause]
  split <;> rename _ => h_red
  · simp; rintro rfl rfl rfl rfl
    rw [reduce_satisfied_iff] at h_red
    rw [h_red]
    exact ⟨le_top, Or.inl ⟨rfl, rfl⟩⟩
  · simp; rintro rfl rfl rfl rfl
    rw [reduce_notReduced_iff] at h_red
    rw [h_red]
    exact ⟨inf_le_of_left_le (Cnf.le_of_mem hC), Or.inl ⟨rfl, rfl⟩⟩
  · split <;> rename _ => hbc <;> try simp
    split <;> rename _ => h_hint <;> try simp
    rename Fin _ => hint_index
    have h_bc_lt : 1 < (ratHints.size + 1) - bc := by
      apply Nat.lt_sub_of_add_lt
      rw [add_comm]
      exact Nat.add_lt_add_right hbc 1
    split <;> rename PPA => τ₂ <;> rename _ => h_RAT_assumption <;> try simp
    · rintro rfl rfl rfl rfl
      use inf_le_of_right_le (assumeRATClause_error h_RAT_assumption).1
      right; use rfl
      rcases assumeRATClause_error h_RAT_assumption with ⟨_, h₂⟩
      exact uniform_bump_of_uniform_of_extended h_bc_lt h_uni h₂
    · split <;> rename PPA => τ₃ <;> rename _ => h_ratHints <;> try simp
      rintro rfl rfl rfl rfl
      rcases assumeRATClause_ok h_RAT_assumption with ⟨h_RAT₁, h_RAT₂⟩
      rcases fold_UP_checked h_ratHints with ⟨h₁, h₂⟩
      have h_ext := extended_trans h_RAT₂ h₂
      constructor
      -- TODO: Standard form can probably remove the need for these operations
      · rw [inf_compl_le_iff_le_sup, sup_comm, ← inf_compl_le_iff_le_sup, inf_comm] at h_RAT₁
        rw [← le_compl_iff_inf_le_bot] at h₁
        exact le_trans (inf_le_inf_right (PPA.toPropFun τ) h₁) h_RAT₁
      · exact Or.inr ⟨rfl, uniform_bump_of_uniform_of_extended h_bc_lt h_uni h_ext⟩

theorem fold_checkClause_ok {F F' : ICnf} {σ : PS} {ratHints : Array (Nat × Array Nat)}
    {τ τ' : PPA} {ratIndex ratIndex' index index' bc bc' : Nat} :
    -- TODO: Additional assumptions on τ, related to C or isSetFor
    (∀ C ∈ F, C ∈ F') →
    uniform τ ((ratHints.size + 1) - bc) →
    F.foldlM (checkClause F' σ ratHints) (τ, ratIndex, index, bc) = ok (τ', ratIndex', index', bc') →
      F'.toPropFun ⊓ τ ≤ (PropFun.substL F σ.toSubst) := by
  intro hF h_ext
  have ⟨F⟩ := F
  rw [Array.foldlM_eq_foldlM_data]
  induction' F with C CS ih generalizing τ ratIndex index bc <;> simp
  match h_check : checkClause F' σ ratHints (τ, ratIndex, index, bc) C with
  | error _ => intro hcon; injection hcon
  | ok (τ₂, rI₂, i₂, bc₂) =>
    simp [← Array.mem_data] at hF
    rcases hF with ⟨hF₁, hF₂⟩
    rw [Array.mem_data] at hF₁
    simp [Array.mem_data] at hF₂
    have : ∀ C ∈ ({ data := CS } : ICnf), C ∈ F' := by
      simp [← Array.mem_data]; simp_rw [Array.mem_data]; exact hF₂
    rcases checkClause_ok hF₁ h_ext h_check with ⟨h₁, h₂⟩
    rcases h₂ with (⟨rfl, rfl⟩ | ⟨rfl, hτ₂_ext, hτ₂_propfun⟩)
    · exact fun h => ⟨h₁, ih h_ext this h⟩
    · intro h
      use h₁
      rw [← hτ₂_propfun]
      exact ih hτ₂_ext this h

-- For the line to continue checking, the clause to be added must be redundant
theorem checkLine_ok {F : ICnf} {τ : PPA} {σ : PS} {line : SRLine} {S : SRState} :
    checkLine ⟨F, τ, σ⟩ line = ok S → eqsat F.toPropFun (F.toPropFun ⊓ line.1) := by
  simp [checkLine]
  rcases line with ⟨C, w_tf, w_maps, UPhints, RAThints⟩
  split <;> try simp
  rename PPA => τ₁
  rename _ = ok τ₁ => h_assumeNegatedCandidate
  rcases assumeNegatedClauseFor_ok h_assumeNegatedCandidate with ⟨hC₁, hC₂⟩
  replace hC₂ := uniform_of_extended_reset hC₂
  simp at hC₁ hC₂
  --replace hC₂ := uniform_of_extended_reset hC₂
  match h_hints : UPhints.foldlM (applyUPHint F (RAThints.size + 1)) τ₁ with
  | error (_, .checkError) => simp
  | error (τ', .checked) =>
    simp; split <;> simp
    rcases fold_UP_checked h_hints with ⟨h₁, h₂⟩
    rw [hC₁] at h₁
    rw [← le_iff_inf_compl_le_bot] at h₁
    exact fun _ => eqsat_of_entails h₁
  | ok τ₂ =>
    simp; split <;> try simp
    split <;> try simp
    rename 0 < _ ∧ 0 < _ => h_sizes
    rcases h_sizes with ⟨hC_size, hw_size⟩
    match h_RAT : F.foldlM (checkClause F (assumeWitness σ C[0] w_tf w_maps) RAThints) (τ₂, 0, 0, 0) with
    | error () => simp
    | ok (τ₃, idx₃) =>
      split <;> try simp
      rename _ => h_ok; simp at h_ok; rcases h_ok with ⟨rfl, rfl⟩
      rcases fold_UP_ok h_hints with ⟨h₁, h₂⟩
      rw [hC₁] at h₁
      intro
      apply SR_core (assumeWitness_subst hC_size σ w_tf w_maps)
      replace hC₂ : uniform τ₂ ((RAThints.size + 1) - 0) := uniform_of_uniform_of_extended hC₂ h₂
      have hFC_le_Fτ₂ : F.toPropFun ⊓ (C.toPropFun)ᶜ ≤ F.toPropFun ⊓ τ₂ := by
        have := inf_le_inf_left F.toPropFun h₁
        rwa [← inf_assoc, inf_idem] at this
      exact le_trans hFC_le_Fτ₂ (fold_checkClause_ok (by simp) hC₂ h_RAT)

end SR
