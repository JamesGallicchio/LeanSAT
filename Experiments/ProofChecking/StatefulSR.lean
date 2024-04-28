/-

SR checking with state monads.

Cayden Codel
-/

import LeanSAT.Data.Cnf
import LeanSAT.Data.Literal
import LeanSAT.Data.ICnf

import LeanSAT.Model.PropFun

import Experiments.ProofChecking.PPA
import Experiments.ProofChecking.PS
import Experiments.ProofChecking.RangeArray

open LeanSAT LeanSAT.Model PropFun

namespace SR
/-
@[inline, specialize]
def foldlM_index {β : Type v} {m : Type v → Type w} [Monad m] (f : β → α → m β)
    (init : β) (A : RangeArray α) (i : Nat) : m β :=
  A.data.foldlM f init (A.index i) (A.index i + A.rsize i)
-/
-- A typeclass for Formulas. Supports the basic operations needed for SR checking.
@[specialize]
class Formula (F : Type u) where
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
class LawfulFormula (F : Type u) [Formula F] where
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

structure SRState (CNF : Type _) [Formula CNF] where
  F : CNF
  τ : PPA
  σ : PS

structure SRLine where
  clause : IClause
  witness_lits : Array ILit
  witness_maps : Array (IVar × ILit)
  up_hints : Array Nat                -- Already 0-indexed clause IDs into the accumulated formula
  rat_hints : Array (Nat × Array Nat) -- Already 0-indexed clause IDs into the accumulated formula

abbrev ESt (CNF : Type _) [Formula CNF] := fun ε α => EStateM ε (SRState CNF) α
abbrev St (CNF : Type _) [Formula CNF] := fun α => StateM (SRState CNF) α

open Nat Formula PPA PS EStateM

variable {CNF : Type _} [Formula CNF]

namespace ESt

variable {ε : Type _} {m : Type u → Type v} [Monad m] {β : Type u}

@[always_inline, inline]
protected def size : ESt CNF ε Nat :=
  modifyGet (fun S => (Formula.size S.F, S))

@[always_inline, inline]
protected def foldMOnClause (i : Nat) (f : β → ILit → m β) (init : β) : ESt CNF ε (m β) :=
  modifyGet (fun S => ((Formula.foldMOnClause S.F i f init), S))

-- TODO: Better way to write this?
#check EStateM.modifyGet

@[always_inline, inline]
protected def setLitFor (l : ILit) (offset : Nat) : ESt CNF ε Unit :=
  modifyGet (fun S => ⟨(), { S with τ := S.τ.setLitFor l offset }⟩)

@[always_inline, inline]
protected def addClause (C : IClause) : ESt CNF ε Unit :=
  modifyGet (fun S => ⟨(), { S with F := Formula.addClause S.F C }⟩)

end ESt

namespace St

variable {m : Type u → Type v} [Monad m] {β : Type u}

@[always_inline, inline]
protected def size : St CNF Nat :=
  modifyGet (fun S => (Formula.size S.F, S))

@[always_inline, inline]
protected def foldMOnClause (i : Nat) (f : β → ILit → m β) (init : β) : St CNF (m β) :=
  modifyGet (fun S => ((Formula.foldMOnClause S.F i f init), S))

@[always_inline, inline]
protected def setLitFor (l : ILit) (offset : Nat) : St CNF Unit :=
  modifyGet (fun S => ⟨(), { S with τ := S.τ.setLitFor l offset }⟩)

@[always_inline, inline]
protected def addClause (C : IClause) : St CNF Unit :=
  modifyGet (fun S => ⟨(), { S with F := Formula.addClause S.F C }⟩)

-- Basically lifts StateM to EStateM
@[always_inline, inline]
protected def ebind (x : StateT σ Id α) (f : α → EStateM ε σ β) : EStateM ε σ β :=
  fun s => let (a, s) := x s; f a s

end St

-- TODO: Make this be a function in PPA for general UPBox
-- TODO: Determine if this is faster than `do (← get).F.size, etc`
open MUPResult in
def SRfoldUP (i : Nat) : St CNF MUPResult := fun ⟨F, τ, σ⟩ =>
  ⟨unitPropRes <| Formula.foldMOnClause F i (pevalUP τ) none, ⟨F, τ, σ⟩⟩

open ReductionResult in
def SRreduce (i : Nat) : St CNF ReductionResult := fun ⟨F, τ, σ⟩ =>
  (reduceRes <| Formula.foldMOnClause F i (seval σ) false, ⟨F, τ, σ⟩)

-- Applies a single unit propagation step
-- On success, we set the unit literal in τ with the offset
-- On falsification of the clause, we error with true (.checked)
-- On satisfied clause or multiple unassigned literals, we error with false (.checkError)
def applyUPHint (offset hint : Nat) : ESt CNF Bool Unit := fun ⟨F, τ, σ⟩ =>
  if hint < size F then
    match SRfoldUP hint ⟨F, τ, σ⟩ with
    | ⟨.falsified, ⟨F, τ, σ⟩⟩ =>
      EStateM.throw true ⟨F, τ, σ⟩
    | ⟨.satisfied, ⟨F, τ, σ⟩⟩ =>
      -- dbg_trace s!"ERROR: UP found a satisfied clause"
      EStateM.throw false ⟨F, τ, σ⟩
    | ⟨.multipleUnassignedLiterals, ⟨F, τ, σ⟩⟩ =>
      -- dbg_trace s!"ERROR: UP found a non-unit clause"
      EStateM.throw false ⟨F, τ, σ⟩
    | ⟨.unit l, ⟨F, τ, σ⟩⟩ =>
      Result.ok () { F, τ := τ.setLitFor l offset, σ }
  else
    EStateM.throw false ⟨F, τ, σ⟩

def scanRATHints (clauseId : Nat) (ratHints : Array (Nat × Array Nat)) : Option (Fin ratHints.size) :=
  match ratHints.foldlM (init := 0) (fun counter ⟨hint, _⟩ =>
        if hint = clauseId then Except.error counter
        else Except.ok (counter + 1)) with
  | Except.ok _ => none
  | Except.error index =>
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

-- `i` is the index into the formula
-- Assuming that (C|σ) is reduced but not satisfied and that C is a RAT clause, sets τ ← τ ⊓ (C|σ)ᶜ
def assumeRATClause (i : Nat) : ESt CNF Unit Unit := fun ⟨F, τ, σ⟩ =>
  if i < size F then
    match Formula.foldMOnClause F i (init := τ) (fun τ lit =>
      match σ.litValue lit with
      | .tr => Except.error τ       -- (C|σ) is satisfied, so return early to report satisfied
      | .fls => Except.ok τ         -- Ignore the literal
      | .lit l =>
        match τ.litValue? l with
        | some true => Except.error τ    -- (C|σ)|τ is satisfied, so return early to report satisfied
        | some false => Except.ok τ      -- Its negation is true in τ, so ignore the literal
        | none => Except.ok (τ.setLit (-l))) with
    | Except.ok τ => Result.ok () ⟨F, τ, σ⟩
    | Except.error τ => Result.error () ⟨F, τ, σ⟩
  else
    EStateM.throw () ⟨F, τ, σ⟩

-- Set the witness substitution σ from the provided mapping, resetting σ first
def assumeWitness (σ : PS) (pivot : ILit) (A₁ : Array ILit) (A₂ : Array (IVar × ILit)) : PS :=
  ((σ.reset.setLits A₁).setVars A₂).setLit pivot

-- Check each clause in the formula.
-- C is the current clause in the formula to be checked for the RAT property under σ and τ
-- If C is reduced by σ, then it is RAT. Find a RAT hint and uses the RAT UP hints to derive contradiction.
-- (Nat × Nat × Nat) is (ratIndex, index, bumpCounter), where
--     index := the current index into the formula
--     ratIndex := the (hopeful, cached) index into the RAT hints
--     bumpCounter := the number of times we've bumped the assignment
def checkClause (ratHints : Array (Nat × Array Nat)) :
    Nat → (Nat × Nat) → ESt CNF Unit (Nat × Nat) := fun index ⟨ratIndex, bumpCounter⟩ => do
  --let reducedRes ← SRreduce index
  --let F := dbgTraceIfShared "Formula in checkClause" F
  St.ebind (SRreduce index) fun v => do
  match v with
  | .satisfied => return (ratIndex, bumpCounter)
  | .notReduced => return (ratIndex, bumpCounter)
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
      | none => EStateM.throw ()
      | some rI =>
        -- CC TODO: There's probably an idiomatic way of writing this
       (fun v =>
          match v with
          -- If the clause is satisfied under σ and τ, then we move to the next iteration
          | Result.error () S =>
              Result.ok (rI.val + 1, bumpCounter + 1) ({ S with τ := S.τ.bump })

          -- Otherwise, we have assumed the negation of the RAT clause
          -- Now check for UP derivation through its hints
          | Result.ok () S =>
            let ⟨_, hints⟩ := ratHints.get rI
            (fun v' =>
              match v' with
              | Result.error true S =>
                  Result.ok (rI.val + 1, bumpCounter + 1) ({ S with τ := S.τ.bump })
              | Result.error false S => Result.error () S
              | Result.ok _ S => Result.error () S)
            ∘ hints.foldlM (init := ()) (fun _ hint => applyUPHint 0 hint) <| S
        ) ∘ (assumeRATClause index)

    -- We error if the bumpCounter equals the number of RAT hints, since that
    -- means we bumped the assignment too many times, clearing out the
    -- assumption of the candidate clause
    else EStateM.throw ()

def checkLine (line : SRLine) : ESt CNF Bool Unit :=
  --let ⟨F, τ, σ⟩ := dbgTraceIfShared "Formula at start of checkLine" S
  let ⟨C, w_tf, w_maps, UPhints, RAThints⟩ := line

  -- Assumes the negation of the candidate clause, with "# of RAT hints" offset
  --modifyGet (fun ⟨F, τ, σ⟩ =>
  --  match assumeNegatedClauseFor τ.reset C (RAThints.size + 1) with
  -- Gotta write this as a function, for now
  fun ⟨F, τ, σ⟩ =>
  match assumeNegatedClauseFor τ.reset C (RAThints.size + 1) with
  | Except.error _ => EStateM.throw false ⟨F, τ, σ⟩
  | Except.ok τ =>

  -- Evaluate the UP hints, with "# of RAT hints" offset
  -- We add one more than normal to help with proving
  (fun v =>
    match v with
    -- The clause led to contradiction via unit propagation
    | Result.error true S =>
      if C = #[] then EStateM.throw true S
      else ESt.addClause C S

    -- Unit propagation failed due to multiple unassigned literals, satisfied clause, or out-of-bounds
    | Result.error false S => EStateM.throw false S

    -- Unit propagation worked but didn't lead to contradiction, so continue to RAT checking
    | Result.ok () ⟨F, τ, σ⟩ =>
      -- If the clause is empty, then we should have derived UP contradiction by now
      if hCw : 0 < C.size ∧ 0 < w_tf.size then
        if C.get ⟨0, hCw.1⟩ ≠ w_tf.get ⟨0, hCw.2⟩ then EStateM.throw false ⟨F, τ, σ⟩ else

        -- Assume the witness, under substitution (the function call resets σ)
        let σ := assumeWitness σ (C.get ⟨0, hCw.1⟩) w_tf w_maps
        --let F := dbgTraceIfShared "Formula" F

        -- Go through each clause in the formula to check RAT
        let Fsize := size F
        let f := checkClause RAThints
        let rec loop (i : Nat) (p : Nat × Nat) : ESt CNF Unit (Nat × Nat) := do
          if i < Fsize then
            loop (i + 1) (← f i p)
          else
            pure p
          termination_by Fsize - i
        match loop 0 ⟨0, 0⟩ <| ⟨F, τ, σ⟩ with
        | Result.error () S => EStateM.throw false S
        | Result.ok _ S =>
          --let F := dbgTraceIfShared "Formula at end of checkLine" F
          ESt.addClause C S -- The RAT hint checked, so we continue

      else EStateM.throw false ⟨F, τ, σ⟩)
  ∘ UPhints.foldlM (init := ()) (fun _ hint => applyUPHint (RAThints.size + 1) hint) <| ⟨F, τ, σ⟩


/-
def checkProof (F : CNF) (proof : Array SRLine) : Bool :=
  let τ := PPA.new 100
  let σ := PS.new 100
  match proof.foldlM (init := ⟨F, τ, σ⟩) (fun _ S => checkLine S) with
  | ok _ => false
  | error false => false
  | error true => true -/

end SR
