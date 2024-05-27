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



-- CC: This probably shouldn't be at root, but what namespace do you put this in?
def clauseListToPropFun (C : List ILit) : PropFun IVar :=
  .any (Multiset.ofList C |>.map LitVar.toPropFun)

def cnfListToPropFun (Cs : List (Option (List ILit))) : PropFun IVar :=
  .all (Cs.map (fun C =>
    match C with
    | none => ⊤
    | some C => clauseListToPropFun C))

theorem clauseListToPropFun_eq_toPropFun (C : List ILit) :
  clauseListToPropFun C = Clause.toPropFun ({ data := C} : IClause) := by
  simp [clauseListToPropFun, Clause.toPropFun]

-- CC: Very hacky
theorem cnfListToPropFun_eq_toPropFun (Cs : List (Option (List ILit))) :
  cnfListToPropFun Cs = Cnf.toPropFun ({ data := Cs.map (fun cl =>
    match cl with
    | none => { data := [LitVar.mkPos 1, LitVar.mkNeg 1] }
    | some C => { data := C }) } : ICnf) := by
  simp [cnfListToPropFun]
  induction Cs with
  | nil => simp
  | cons C Cs ih =>
    match C with
    | none =>
      simp [PropFun.all]
      exact ih
    | some C =>
      simp
      rw [← ih, clauseListToPropFun_eq_toPropFun]
      simp [PropFun.all]

theorem clausePropFun_ge_of_mem {C : List ILit} {l : ILit} :
  l ∈ C → l.toPropFun ≤ clauseListToPropFun C := by
  intro h
  rw [clauseListToPropFun_eq_toPropFun]
  apply Clause.toPropFun_mem_le
  rw [← Array.mem_data]
  exact h

theorem cnfPropFun_le_of_mem {Cs : List (Option (List ILit))} {C : List ILit} {i : Nat}
      {hi : i < Cs.length} :
    Seq.get Cs ⟨i, hi⟩ = some C → cnfListToPropFun Cs ≤ clauseListToPropFun C := by
  intro h
  rw [cnfListToPropFun_eq_toPropFun]
  induction Cs generalizing i with
  | nil => simp at hi
  | cons X Xs ih =>
    match X with
    | none =>
      match i with
      | 0 => simp [Seq.get] at h
      | i + 1 =>
        simp at hi
        simp [Seq.get] at h
        simp [ih h]
    | some X =>
      match i with
      | 0 =>
        simp [Seq.get] at h; subst h
        simp [clauseListToPropFun_eq_toPropFun]
      | i + 1 =>
        simp [Seq.get] at h
        have := ih h
        apply le_trans _ this
        simp

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

-- Returns the updated PPA. True if C is a tautology (error), false if not.
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
/-
def assumeRATClauseM_index (F : RangeArray ILit) (index : Fin F.size) (σ : PS) (τ : PPA) : Except PPA PPA :=
  F.foldlM_index (init := τ) (fun τ lit =>
    match σ.litValue lit with
    | Sum.inr true => error τ       -- (C|σ) is satisfied, so return early to report satisfied
    | Sum.inr false => ok τ         -- Ignore the literal
    | Sum.inl l =>
      match τ.litValue? l with
      | some true => error τ        -- (C|σ)|τ is satisfied, so return early to report satisfied
      | some false => ok τ          -- Its negation is true in τ, so ignore the literal
      | none => ok (τ.setLit (-l))) index -/

/-- Assumes into `τ` the negation of RAT clause `C` under the substitution `σ` for one "bump."
    Errors if `C` is satisfied by either `σ` or `τ` under `σ`. -/
def assumeRATClauseM (F : RangeArray ILit) (index : Fin F.size) (σ : PS) (τ : PPA) : Except PPA PPA :=
  let rsize := F.rsizeFin index
  let rec loop (i : Nat) (τ : PPA) : Except PPA PPA :=
    if h : i < rsize then
      let lit := F.ogetFin index ⟨i, h⟩
      match σ.litValue lit with
      | Sum.inr true => error τ       -- (C|σ) is satisfied, so return early to report satisfied
      | Sum.inr false => loop (i + 1) τ         -- Ignore the literal
      | Sum.inl l =>
        match τ.litValue? l with
        | some true => error τ        -- (C|σ)|τ is satisfied, so return early to report satisfied
        | some false => loop (i + 1) τ          -- Its negation is true in τ, so ignore the literal
        | none => loop (i + 1) (τ.setLit (-l))
    else
      ok τ
  termination_by F.rsizeFin index - i
  loop 0 τ

-- A tail-recursive implementation of `assumeRATClauseM`
/-
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
  loop 0 τ -/

-- A tail-recursive implementation that breaks the API to go faster
def assumeRATClauseDirect (F : RangeArray ILit) (index : Fin F.size) (σ : PS) (τ : PPA) : Except PPA PPA :=
  let s := F.indexFin index
  let rsize := F.rsizeFin index
  let e : Nat := s + rsize
  let rec loop (i : Nat) (τ : PPA) : Except PPA PPA :=
    if h : i < e then
      let lit := F.getFin ⟨i, lt_of_lt_of_le h (indexFin_add_rsizeFin_le_size index)⟩
      match σ.litValue lit with
      | Sum.inr true => error τ
      | Sum.inr false => loop (i + 1) τ
      | Sum.inl l =>
        match τ.litValue? l with
        | some true => error τ
        | some false => loop (i + 1) τ
        | none => loop (i + 1) (τ.setLit (-l))
    else
      ok τ
  termination_by (F.indexFin index + F.rsizeFin index) - i
  loop s τ

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

/-
def unitPropDirect (τ : PPA) (F : RangeArray ILit) (hint : Fin F.size) : PPA.UPResult :=
  let s := F.indexFin hint
  let rsize := F.rsizeFin hint
  let e : Nat := s + rsize
  let he : e ≤ Size.size F.data := indexFin_add_rsizeFin_le_size hint
  let rec loop (i : Nat) (unit? : Option ILit) : PPA.UPResult :=
    if h : i < e then
      let lit := F.getFin ⟨i, lt_of_lt_of_le h he⟩
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
  termination_by e - i
  loop s none -/

inductive HintResult where
  | unit
  | contra
  | err
  deriving DecidableEq, Inhabited

@[inline]
def applyUPHint (F : RangeArray ILit) (bumps : Nat) (τ : PPA) (hint : Nat) : PPA × HintResult :=
  if h_hint : hint < F.size then
    if !F.isDeletedFin ⟨hint, h_hint⟩ then
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

/-
@[inline]
def applyUPHintDirect (F : RangeArray ILit) (bumps : Nat) (τ : PPA) (hint : Nat) : PPA × HintResult :=
  if h_hint : hint < F.size then
    if !F.isDeleted hint then
      match unitPropDirect τ F ⟨hint, h_hint⟩ with
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
    ⟨τ, .err⟩ -/

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

/-
@[inline, always_inline]
def applyUPHintsDirect (F : RangeArray ILit) (offset : Nat) (τ : PPA) (hints : Array Nat) : PPA × HintResult :=
  let rec loop (i : Nat) (τ : PPA) : PPA × HintResult :=
    if hi : i < Size.size hints then
      match applyUPHintDirect F offset τ (Seq.get hints ⟨i, hi⟩) with
      | (τ, .unit) => loop (i + 1) τ
      | (τ, .contra) => (τ, .contra)
      | (τ, .err) => (τ, .err)
    else (τ, .unit)
  termination_by hints.size - i
  loop 0 τ -/

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

def reduceDirect (σ : PS) (F : RangeArray ILit) (index : Fin F.size) : ReductionResult :=
  let s := F.indexFin index
  let rsize := F.rsizeFin index
  let e : Nat := s + rsize
  let he : e ≤ Size.size F.data := indexFin_add_rsizeFin_le_size index
  let rec loop (i : Nat) (reduced? : Bool) : ReductionResult :=
    if h : i < e then
      let lit := F.getFin ⟨i, lt_of_lt_of_le h he⟩
      match seval' σ lit with
      | .satisfied => .satisfied
      | .reduced => loop (i + 1) true
      | .notReduced => loop (i + 1) reduced?
    else
      if reduced? then .reduced else .notReduced
  termination_by e - i
  loop s false

/-
  if hl : l.index < σ.gens.size then
    let gen := σ.gens.get ⟨l.index, hl⟩
    if gen ≥ σ.generation then
      let n := σ.mappings.get ⟨l.index, by rw [σ.sizes_eq] at hl; exact hl⟩
      match n with
      | 0 => if polarity l then satisfied else reduced
      | 1 => if polarity l then reduced else satisfied
      | _ => reduced -- Technically can map to itself, but well-formed witnesses don't do this
    else notReduced
  else notReduced
-/

def reduceBreak (σ : PS) (F : RangeArray ILit) (index : Fin F.size) : ReductionResult :=
  let s := F.indexFin index
  let rsize := F.rsizeFin index
  let e : Nat := s + rsize
  let rec loop (i : Nat) (reduced? : Bool) : ReductionResult :=
    if h : i < e then
      let lit := F.getFin ⟨i, lt_of_lt_of_le h (indexFin_add_rsizeFin_le_size index)⟩
      if hlit : lit.index < σ.gens.size then
        let gen := σ.gens.get ⟨lit.index, hlit⟩
        if gen ≥ σ.generation then
          let n := σ.mappings.get ⟨lit.index, by rw [σ.sizes_eq] at hlit; exact hlit⟩
          match n with
          | 0 =>
            if LitVar.polarity lit then .satisfied
            else loop (i + 1) true
          | 1 =>
            if LitVar.polarity lit then loop (i + 1) true
            else .satisfied
          | n =>
            if PSV.toMapped' lit ≠ n then
              loop (i + 1) true
            else
              loop (i + 1) reduced?
        else loop (i + 1) reduced?
      else loop (i + 1) reduced?
    else
      if reduced? then .reduced else .notReduced
  termination_by (F.indexFin index + F.rsizeFin index) - i
  loop s false

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

def checkLine : SRState → SRAdditionLine → Except Bool SRState := fun ⟨F, τ, σ⟩ line =>
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
              match reduceBreak σ F ⟨i, hi⟩ with
              | .satisfied => loop (i + 1) cachedRatHintIndex bumpCounter τ
              | .notReduced => loop (i + 1) cachedRatHintIndex bumpCounter τ
              | .reduced =>
                -- dbg_trace s!"Clause index {i} is a RAT candidate"
                if bumpCounter < line.ratHintIndexes.size then
                  -- Find the corresponding RAT hint
                  match findRATHintIndex cachedRatHintIndex i line.ratHintIndexes with
                  | none => ⟨τ, false⟩
                  | some ⟨ratIndex, hr⟩ =>
                    -- Assume the negation of the RAT clause
                    match assumeRATClauseDirect F ⟨i, hi⟩ σ τ with
                    | error τ => loop (i + 1) (ratIndex + 1) (bumpCounter + 1) τ.bump
                    | ok τ =>
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
      else error false

/-! # Correctness -/

theorem uAssume.loop.aux {F : RangeArray ILit} {τ : PPA} {Ls : List (Option (List ILit))} {L : List ILit}
  (h_models : models F Ls L) {bumps : Nat} {i j : Nat} :
  j = Size.size L - i →
    uAssumeNegatedForM.loop F bumps i τ = assumeNegatedClauseFor.loop { data := L } bumps i τ := by
  intro hj
  induction j generalizing τ i with
  | zero =>
    have h_le₁ := Nat.le_of_sub_eq_zero hj.symm
    have h_le₂ := h_models.h_size₂.symm ▸ h_le₁
    unfold assumeNegatedClauseFor.loop
    simp only [LeanColls.size] at h_le₁ h_le₂ ⊢
    simp [not_lt.mpr h_le₁]
    unfold uAssumeNegatedForM.loop
    simp [not_lt.mpr h_le₂]
  | succ j ih =>
    rw [Nat.succ_eq_add_one] at hj
    unfold assumeNegatedClauseFor.loop
    simp [LeanColls.size] at hj ⊢
    have hi : i < List.length L := by
      apply Nat.lt_of_sub_pos
      rw [← hj]
      exact Nat.zero_lt_succ j
    simp [hi]
    have h_silly : Seq.get ({ data := L} : IClause) ⟨i, hi⟩ = Seq.get L ⟨i, hi⟩ := rfl
    have h_agree := h_models.h_uncommitted hi
    split <;> rename _ => h_get
    · rw [← @ih (setLitFor τ (-Seq.get ({ data := L} : IClause) { val := i, isLt := hi }) bumps) (i + 1)]
      · rw [uAssumeNegatedForM.loop]
        rw [h_silly, ← h_agree] at h_get
        have := h_models.h_size₂
        simp [LeanColls.size] at this
        rw [← this] at hi
        simp [hi]
        simp [ugetFin_eq_uget, h_get]
        rw [h_agree]
        rfl
      · simp [LeanColls.size]; exact Nat.eq_sub_succ_of_succ_eq_sub hj
    · rw [← @ih τ]
      rw [uAssumeNegatedForM.loop]
      split <;> rename _ => hi'
      · simp [ugetFin_eq_uget, h_agree, ← h_silly, h_get]
      · rw [h_models.h_size₂] at hi'
        exact absurd hi hi'
      · simp [LeanColls.size]; exact Nat.eq_sub_succ_of_succ_eq_sub hj
    · rw [uAssumeNegatedForM.loop]
      split <;> rename _ => hi'
      · simp [ugetFin_eq_uget, h_agree, ← h_silly, h_get]
      · rw [h_models.h_size₂] at hi'
        exact absurd hi hi'

theorem uAssumeNegatedForM_eq_assumeNegatedClauseFor {F : RangeArray ILit}
    {Ls : List (Option (List ILit))} {L : List ILit} {τ : PPA} {bumps : Nat} :
    models F Ls L →
    uAssumeNegatedForM F τ bumps = assumeNegatedClauseFor τ ({ data := L} : IClause) bumps := by
  intro h_models
  simp [uAssumeNegatedForM, assumeNegatedClauseFor]
  rw [@uAssume.loop.aux _ _ _ _ h_models bumps 0 (Size.size L)]
  simp

theorem assumeRATClauseDirect.loop.aux {F : RangeArray ILit} {Ls : List (Option (List ILit))} {L : List ILit}
  (h_models : models F Ls L) {σ : PS} {i j : Nat} (hi : i < F.size) :
  --    k = F.rsizeFin ⟨i, hi⟩ - j
    j = F.rsizeFin ⟨i, hi⟩ - i →
    assumeRATClauseDirect.loop F i σ j = assumeRATClauseM F hint σ := by
  intro hj
  induction j generalizing σ i with
  | zero =>
    have h_le₁ := Nat.le_of_sub_eq_zero hj.symm
    have h_le₂ := h_models.h_size₂.symm ▸ h_le₁
    unfold assumeRATClauseM
    simp [not_lt.mpr h_le₂]
    unfold assumeRATClauseDirect
    simp [not_lt.mpr h_le₁]
  | succ j ih =>
    rw [Nat.succ_eq_add_one] at hj
    unfold assumeRATClauseM
    simp [LeanColls.size] at hj ⊢
    have hi : i < List.length L := by
      apply Nat.lt_of_sub_pos
      rw [← hj]
      exact Nat.zero_lt_succ j
    simp [hi]
    have h_silly : Seq.get ({ data := L} : IClause) ⟨i, hi⟩ = Seq.get L ⟨i, hi⟩ := rfl
    have h_agree := h_models.h_uncommitted hi
    split <;> rename _ => h_get
    · rw [← @ih (σ.setLit (-Seq.get ({ data := L} : IClause) { val := i, isLt := hi })) (i + 1)]
      · rw [assumeRATClauseDirect.loop]
        rw [h_silly, ← h_agree] at h_get
        have := h_models.h_size₂
        simp [LeanColls.size] at this
        rw [← this] at hi
        simp [hi]
        simp [ogetFin_eq_oget, h_get]
        rw [h_agree]
        rfl
      · simp [LeanColls.size]; exact Nat.eq_sub_succ_of_succ_eq_sub hj
    · rw [← @ih σ]
      rw [assumeRATClauseDirect.loop]
      split <;> rename _ => hi'
      · simp [ogetFin_eq_oget, h_agree

#exit

theorem RangeArray.unitProp_eq_unitProp {F : RangeArray ILit}
  {Ls : List (Option (List ILit))} {L C : List ILit} (h_models : models F Ls L)
  {τ : PPA} {hint : Nat} {h_hint : hint < Size.size Ls} :
    Seq.get Ls ⟨hint, h_hint⟩ = some C →
    RangeArray.unitProp τ F ⟨hint, h_models.h_size₁ ▸ h_hint⟩ = PPA.unitProp τ ({ data := C } : IClause) := by
  sorry
  done

-- Clone of PPA.LawfulUP, but with `RangeArray`
theorem applyUPHint_unit {F : RangeArray ILit} {Ls : List (Option (List ILit))} {L : List ILit}
    (h_models : models F Ls L) {τ τ' : PPA} {bumps : Nat} {hint : Nat} :
    applyUPHint F bumps τ hint = (τ', .unit) →
      (h_hint : hint < Size.size Ls) ×'
      ∃ (C : List ILit), Seq.get Ls ⟨hint, h_hint⟩ = some C ∧
        ∃ (l : ILit),
          l ∈ C ∧
          τ.litValue? l = none ∧
          τ' = τ.setLitFor l bumps ∧ (clauseListToPropFun C) ⊓ τ = l.toPropFun ⊓ τ ∧
          (cnfListToPropFun Ls) ⊓ τ ≤ τ' := by
  simp [applyUPHint]
  intro h
  by_cases h_hint : hint < F.size
  <;> simp [h_hint] at h
  by_cases h_del : isDeletedFin F ⟨hint, h_hint⟩
  <;> simp [h_del] at h
  split at h
  <;> injection h <;> try contradiction
  rename ILit => lit
  rename _ = UPResult.unit lit => h_up
  rename setLitFor τ lit bumps = _ => h_set
  subst h_set
  have h_hint₂ := h_models.h_size₁ ▸ h_hint
  use h_hint₂
  simp at h_del
  rw [isDeletedFin_eq_isDeleted h_hint] at h_del
  rcases get_eq_some_of_models_of_not_deleted h_models h_del with ⟨_, sL, hsL⟩
  use sL, hsL
  rw [RangeArray.unitProp_eq_unitProp h_models hsL] at h_up
  have := (unitProp_LawfulUP τ ({ data := sL } : IClause)).2.1 h_up
  rcases this with ⟨h_lit_mem, h₁, h₂⟩
  simp [← Array.mem_data] at h_lit_mem
  simp [clauseListToPropFun_eq_toPropFun]
  use lit, h_lit_mem, h₁, rfl, h₂
  simp [toPropFun_setLit_of_none h₁]
  have := cnfPropFun_le_of_mem hsL
  apply le_trans (inf_le_inf_right τ.toPropFun this)
  rw [clauseListToPropFun_eq_toPropFun, h₂]
  exact inf_le_left

theorem applyUPHint_contra {F : RangeArray ILit} {Ls : List (Option (List ILit))} {L : List ILit}
    (h_models : models F Ls L) {τ τ' : PPA} {bumps : Nat} {hint : Nat} :
    (applyUPHint F bumps τ hint = (τ', .contra) →
      (h_hint : hint < Size.size Ls) ×'
      ∃ (C : List ILit), Seq.get Ls ⟨hint, h_hint⟩ = some C
        ∧ τ = τ' ∧ (clauseListToPropFun C) ⊓ τ = ⊥) := by
  simp [applyUPHint]
  intro h
  by_cases h_hint : hint < F.size
  <;> simp [h_hint] at h
  by_cases h_del : isDeletedFin F ⟨hint, h_hint⟩
  <;> simp [h_del] at h
  split at h
  <;> injection h <;> try contradiction
  rename τ = _ => hτ; subst hτ
  simp at h_del
  rw [isDeletedFin_eq_isDeleted h_hint] at h_del
  have := lt_of_isDeleted_false h_del
  use h_models.h_size₁ ▸ this
  rcases get_eq_some_of_models_of_not_deleted h_models h_del with ⟨_, sL, hsL⟩
  use sL, hsL, rfl
  rename _ = UPResult.falsified => h_up
  rw [RangeArray.unitProp_eq_unitProp h_models hsL] at h_up
  rw [clauseListToPropFun_eq_toPropFun]
  exact (unitProp_LawfulUP τ ({ data := sL } : IClause)).1 h_up

-- CC: Clone of proof from `unitProp.go.cons_aux`
theorem applyUPHints.loop.cons_aux (F : RangeArray ILit) (τ : PPA) (bumps : Nat)
    (hint : Nat) {hints : List Nat} {i j : Nat} :
    j = Size.size hints - i → applyUPHints.loop F bumps { data := hint :: hints } (i + 1) τ =
      applyUPHints.loop F bumps { data := hints } i τ := by
  intro hj
  induction j generalizing τ i with
  | zero =>
    have : i ≥ LeanColls.size hints := Nat.le_of_sub_eq_zero hj.symm
    unfold applyUPHints.loop
    simp [LeanColls.size] at this ⊢
    simp [not_lt.mpr this, not_lt.mpr (Nat.succ_le_succ_iff.mpr this)]
  | succ j ih =>
    unfold applyUPHints.loop
    simp [LeanColls.size, Nat.succ_eq_add_one] at hj ⊢
    have hi : i < List.length hints := by
      apply Nat.lt_of_sub_pos
      rw [← hj]
      exact Nat.zero_lt_succ j
    simp [hi]
    have : Seq.get ({data := hint :: hints} : Array Nat) ⟨i + 1, Nat.succ_lt_succ hi⟩
      = Seq.get ({data := hints} : Array Nat) ⟨i, hi⟩ := rfl
    rw [this]
    split <;> rename PPA => τ' <;> rename _ => h_up
    <;> simp [h_up]
    apply ih
    simp [LeanColls.size]
    exact Nat.eq_sub_succ_of_succ_eq_sub hj

theorem applyUPHints.loop.cons (F : RangeArray ILit) (τ : PPA) (bumps : Nat)
    (hint : Nat) (hints : List Nat) (i : Nat) :
    applyUPHints.loop F bumps { data := hint :: hints } (i + 1) τ =
      applyUPHints.loop F bumps { data := hints } i τ :=
  @applyUPHints.loop.cons_aux F τ bumps hint hints i (hints.length - i) rfl

theorem applyUPHints_unit {F : RangeArray ILit} {Ls : List (Option (List ILit))} {L : List ILit}
    (h_models : models F Ls L) {τ τ' : PPA} {bumps : Nat} {hints : Array Nat} :
    applyUPHints F bumps τ hints = (τ', .unit) →
      (cnfListToPropFun Ls) ⊓ τ ≤ τ' ∧ extended τ τ' bumps := by
  have ⟨hints⟩ := hints
  rw [applyUPHints] --, applyUPHints.loop]
  induction hints generalizing τ τ' with
  | nil =>
    rw [applyUPHints.loop]
    simp [LeanColls.size]
    rintro rfl
    constructor
    · exact inf_le_right
    · simp
  | cons hint hints ih =>
    intro h_uphints
    rw [applyUPHints.loop] at h_uphints
    simp [LeanColls.size] at h_uphints
    split at h_uphints
    <;> rename PPA => τ₂
    · rename applyUPHint _ _ _ _ = _ => h_up
      rw [applyUPHints.loop.cons] at h_uphints
      rcases applyUPHint_unit h_models h_up with ⟨h_hint, sL, _, lit', _, hτlit', rfl, _, h_inf₂⟩
      rcases ih h_uphints with ⟨h₁, h₂⟩
      have h_ext := extended_setLitFor_of_none hτlit' bumps
      constructor
      · have := entails_of_extended h₂
        have h_toPropFun := toPropFun_setLit_of_none hτlit'
        simp [h_toPropFun] at this
        have := inf_le_inf_left (cnfListToPropFun Ls) h_inf₂
        rw [← inf_assoc, inf_idem] at this
        exact le_trans this h₁
      · exact extended_trans h_ext h₂
    · injection h_uphints
      contradiction
    · injection h_uphints
      contradiction

theorem applyUPHints_contra {F : RangeArray ILit} {Ls : List (Option (List ILit))} {L : List ILit}
    (h_models : models F Ls L) {τ τ' : PPA} {bumps : Nat} {hints : Array Nat} :
    applyUPHints F bumps τ hints = (τ', .contra) →
      (cnfListToPropFun Ls) ⊓ τ = ⊥ ∧ extended τ τ' bumps := by
  have ⟨hints⟩ := hints
  rw [applyUPHints]
  induction hints generalizing τ τ' with
  | nil =>
    rw [applyUPHints.loop]
    simp [LeanColls.size]
  | cons hint hints ih =>
    intro h_uphints
    rw [applyUPHints.loop] at h_uphints
    simp [LeanColls.size] at h_uphints
    split at h_uphints
    <;> rename PPA => τ₂
    · rename applyUPHint _ _ _ _ = _ => h_up
      rw [applyUPHints.loop.cons] at h_uphints
      rcases applyUPHint_unit h_models h_up with ⟨h_hint, sL, _, lit', _, hτlit', rfl, _, h_inf₂⟩
      rcases ih h_uphints with ⟨h₁, h₂⟩
      constructor
      · simp at h₁ h_inf₂
        have h_toPropFun := toPropFun_setLit_of_none hτlit'
        rw [h_toPropFun] at h₁ h_inf₂
        rw [← inf_assoc] at h₁
        have := inf_le_inf_left (cnfListToPropFun Ls) h_inf₂
        simp_rw [← inf_assoc, inf_idem] at this
        rw [eq_bot_iff] at h₁ ⊢
        exact le_trans this h₁
      · exact extended_trans (extended_setLitFor_of_none hτlit' bumps) h₂
    · injection h_uphints
      rename τ₂ = _ => h; subst h
      rename applyUPHint _ _ _ _ = _ => h_up
      rcases applyUPHint_contra h_models h_up with ⟨h_hint, sL, hsL, rfl, h_inf⟩
      constructor
      · have := cnfPropFun_le_of_mem hsL
        rw [eq_bot_iff] at h_inf ⊢
        have := inf_le_inf_right τ.toPropFun this
        exact le_trans this h_inf
      · exact extended_refl _ _
    · injection h_uphints; contradiction

theorem reduce_eq_reduce {F : RangeArray ILit} {Ls : List (Option (List ILit))} {L : List ILit}
    (h_models : models F Ls L) {C : List ILit}
    {i : Nat} (hi : i < Size.size Ls) :
    Seq.get Ls ⟨i, hi⟩ = some C →
      ∀ (σ : PS), RangeArray.reduce σ F ⟨i, h_models.h_size₁ ▸ hi⟩ = PS.reduce σ ({ data := C} : IClause) := by
  sorry
  done

theorem reduceBreak.loop_eq_reduce.loop_aux {F : RangeArray ILit} {i : Nat} {hi : i < F.size}
    (σ : PS) {j k : Nat} :
    k = F.rsizeFin ⟨i, hi⟩ - j →
      reduceBreak.loop σ F ⟨i, hi⟩ (F.indexFin ⟨i, hi⟩ + j) = RangeArray.reduce.loop σ F ⟨i, hi⟩ j := by
  intro hk
  ext reduced?
  induction k generalizing σ j reduced? with
  | zero =>
    have h_le := Nat.le_of_sub_eq_zero hk.symm
    unfold reduceBreak.loop RangeArray.reduce.loop
    simp [Nat.not_lt.mpr h_le]
  | succ k ih =>
    have := ih σ (Nat.eq_sub_succ_of_succ_eq_sub hk)
    unfold reduceBreak.loop RangeArray.reduce.loop
    have hj : j < F.rsizeFin ⟨i, hi⟩ := by
      apply Nat.lt_of_sub_pos
      rw [← hk]
      exact Nat.zero_lt_succ k
    simp [hj, seval', litValue, ogetFin, varValue]
    split
    · rename _ => h_lit
      have h_var := h_lit
      simp [ILit.index, σ.sizes_eq] at h_var
      split
      · rename _ => h_gen
        split
        <;> rename _ => h_mappings
        <;> simp [ILit.index] at h_mappings
        <;> simp [h_mappings]
        · split
          · rfl
          · exact this true
        · split
          · exact this true
          · rfl
        · rename _ = 0 → False => h_ne_0
          rename _ = 1 → False => h_ne_1
          split
          · exact this reduced?
          · exact this true
      · exact this reduced?
    · exact this reduced?

theorem reduceBreak.loop_eq_reduce.loop (F : RangeArray ILit) {i : Nat} (hi : i < F.size) (σ : PS) :
    reduceBreak.loop σ F ⟨i, hi⟩ (F.indexFin ⟨i, hi⟩) = RangeArray.reduce.loop σ F ⟨i, hi⟩ 0 :=
  @reduceBreak.loop_eq_reduce.loop_aux F i hi σ 0 (F.rsizeFin ⟨i, hi⟩) rfl

theorem reduceBreak_eq_reduce (F : RangeArray ILit) {i : Nat} (hi : i < F.size) (σ : PS) :
    RangeArray.reduceBreak σ F ⟨i, hi⟩ = RangeArray.reduce σ F ⟨i, hi⟩ := by
  unfold reduceBreak RangeArray.reduce
  simp [reduceBreak.loop_eq_reduce.loop F hi]

theorem checkLine.loop_ok {line : SRAdditionLine} {F : RangeArray ILit} {Ls : List (Option (List ILit))} {L : List ILit}
    (h_models : models F Ls L) {τ τ' : PPA} {σ : PS} {i j cri bc : Nat} :
  j = F.size - i →
  uniform τ (numRatHints - bc) →
    checkLine.loop line F σ i cri bc τ = ⟨τ', true⟩ →
      (τ = τ' ∨ uniform τ' (numRatHints - (bc + 1)))
      ∧ τ'.toPropFun = τ.toPropFun
      ∧ ∀ (k : Nat) (hk₁ : k ≥ i) (hk₂ : k < Size.size Ls) (C : List ILit),
        Seq.get Ls ⟨k, hk₂⟩ = some C →
          (clauseListToPropFun C) ⊓ τ ≤ PropFun.substL (clauseListToPropFun C) σ.toSubst := by
  intro hj h_uniform
  induction j generalizing τ i cri bc with
  | zero =>
    have hi : i ≥ F.size := Nat.le_of_sub_eq_zero hj.symm
    unfold loop
    simp [not_lt.mpr hi, not_lt.mpr (Nat.succ_le_succ_iff.mpr hi)]
    rintro rfl
    simp
    intro k hk₁ hk₂
    rw [← h_models.h_size₁] at hk₂
    have := lt_of_le_of_lt hk₁ hk₂
    exact absurd this (not_lt.mpr hi)
  | succ j ih =>
    unfold loop
    have hi : i < F.size := by
      apply Nat.lt_of_sub_pos
      rw [← hj]
      exact Nat.zero_lt_succ j
    simp [hi]
    -- Split on whether the ith clause is deleted
    split
    · -- Deleted, so we skip the clause
      rename _ = true => h_del
      intro h_loop
      rcases ih (Nat.eq_sub_succ_of_succ_eq_sub hj) h_uniform h_loop with ⟨hτ, hpf, hkC⟩
      use hτ, hpf
      intro k hk₁ hk₂ C hC
      rw [isDeletedFin_eq_isDeleted hi] at h_del
      by_cases hik : i = k
      · -- if i = k, then we derive contradiction
        subst hik
        rw [h_models.h_size₁] at hi
        have := h_models.h_some hi
        simp [h_del, hC] at this
      · -- Otherwise, k is a higher index
        have : i + 1 ≤ k := Nat.succ_le_of_lt (lt_of_le_of_ne hk₁ hik)
        exact hkC _ this hk₂ C hC
    · -- Not deleted, so we actually check the clause
      rename ¬(_ = true) => h_del; simp at h_del
      split
      · -- Reduction returned .satisfied
        rename _ => h_reducedSatisfied
        intro h_loop
        rcases ih (Nat.eq_sub_succ_of_succ_eq_sub hj) h_uniform h_loop with ⟨hτ, hpf, hkC⟩
        use hτ, hpf
        intro k hk₁ hk₂ C hC
        have hj' := Nat.eq_sub_succ_of_succ_eq_sub hj
        by_cases hik : i = k
        · -- if i = k, then the loop body checks the kth clause
          subst hik
          rw [reduceBreak_eq_reduce F hi σ] at h_reducedSatisfied
          rw [h_models.h_size₁] at hi
          rw [reduce_eq_reduce h_models hi hC] at h_reducedSatisfied
          rw [clauseListToPropFun_eq_toPropFun]
          simp [(PS.reduce_Lawful σ { data := C }).1 h_reducedSatisfied]
        · -- Otherwise, k is a higher index
          have : i + 1 ≤ k := Nat.succ_le_of_lt (lt_of_le_of_ne hk₁ hik)
          exact hkC _ this hk₂ C hC
      · -- Reduction returned .notReduced, so we skip the clause here too
        rename _ => h_notReduced
        intro h_loop
        rcases ih (Nat.eq_sub_succ_of_succ_eq_sub hj) h_uniform h_loop with ⟨hτ, hpf, hkC⟩
        use hτ, hpf
        intro k hk₁ hk₂ C hC
        have hj' := Nat.eq_sub_succ_of_succ_eq_sub hj
        by_cases hik : i = k
        · -- if i = k, then the loop body checks the kth clause
          subst hik
          rw [reduceBreak_eq_reduce F hi σ] at h_notReduced
          rw [h_models.h_size₁] at hi
          rw [reduce_eq_reduce h_models hi hC] at h_notReduced
          rw [clauseListToPropFun_eq_toPropFun]
          simp [(PS.reduce_Lawful σ { data := C }).2 h_notReduced]
        · -- Otherwise, k is a higher index
          have : i + 1 ≤ k := Nat.succ_le_of_lt (lt_of_le_of_ne hk₁ hik)
          exact hkC _ this hk₂ C hC
      · -- Reduction returned .reduced
        rename _ => h_reduced
        split <;> try simp
        rename bc < _ => h_bc
        split <;> try simp
        rename Nat => ratIndex
        rename ratIndex < _ => h_ratIndex
        rename _ => h_findRatHint
        -- How does assuming the negation of the reduced clause go?
        split
        · rename PPA => τ₂
          rename _ => h_assumeRAT
          --rw [assumeRATClauseDirect_eq_assumeRATClauseDirectFor h_models h_reduced]
          intro h_loop
          rcases ih (Nat.eq_sub_succ_of_succ_eq_sub hj) h_loop with ⟨hτ, hpf, hkC⟩
          ·
            done
          done
        done
      done
    done
  done

#exit

theorem checkLine_correct {F : RangeArray ILit} {τ : PPA} {σ : PS} {line : SRAdditionLine}
    {S : SRState} {Cs : List (Option (List ILit))} {C : List ILit} :
    models F Cs C →
    checkLine ⟨F, τ, σ⟩ line = .ok S →
    -- S = ⟨F.commit, τ', σ'⟩ ∧
    PropFun.eqsat (cnfListToPropFun Cs) (cnfListToPropFun Cs ⊓ clauseListToPropFun C) := by
  intro h_models h_checkLine
  simp [checkLine] at h_checkLine
  split at h_checkLine
  · contradiction
  · rename PPA => τ₁
    rename _ = ok τ₁ => h_uAssume
    rw [uAssumeNegatedForM_eq_assumeNegatedClauseFor h_models] at h_uAssume
    rcases PPA.assumeNegatedClauseFor_Lawful τ.reset τ₁ { data := C } (Array.size line.ratHints + 1) with ⟨_, h₂⟩
    rcases h₂ h_uAssume with ⟨h_toPropFun_τ₁, h_ext_τ₁⟩
    simp at h_toPropFun_τ₁
    clear h₂
    split at h_checkLine
    <;> rename PPA => τ₂
    · contradiction
    · split at h_checkLine
      · contradiction
      · injection h_checkLine
        rename _ = (_, HintResult.contra) => h_hints
        rcases applyUPHints_contra h_models h_hints with ⟨hF, _⟩
        rw [h_toPropFun_τ₁] at hF
        apply PropFun.eqsat_of_entails
        rw [clauseListToPropFun_eq_toPropFun]
        rwa [eq_bot_iff, ← PropFun.le_iff_inf_compl_le_bot] at hF
    · split at h_checkLine <;> try contradiction
      rename applyUPHints _ _ _ _ = _ => h_uphints
      rename F.dsize < _ => h_Fsize
      split at h_checkLine <;> try contradiction
      rename _ = ugetFin _ => h_getD
      split at h_checkLine <;> try contradiction
      rename PPA => τ₃
      rename checkLine.loop _ _ _ _ _ _ _ = _ => h_checkLine_loop
      injection h_checkLine; rename _ => hS

      stop
      done

    done
  done

#exit
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
