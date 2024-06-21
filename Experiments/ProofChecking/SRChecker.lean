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
open PropFun

-- CC: This probably shouldn't be at root, but what namespace do you put this in?
def clauseListToPropFun (C : List ILit) : PropFun IVar :=
  .any (Multiset.ofList C |>.map LitVar.toPropFun)

def cnfListToPropFun (Cs : List (Option (List ILit))) : PropFun IVar :=
  .all (Cs.map (fun C =>
    match C with
    | none => ⊤
    | some C => clauseListToPropFun C))

@[simp]
theorem clauseListToPropFun_eq_toPropFun (C : List ILit) :
  clauseListToPropFun C = Clause.toPropFun ({ data := C } : IClause) := by
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
      simp [← ih, PropFun.all]

theorem clausePropFun_ge_of_mem {C : List ILit} {l : ILit} :
  l ∈ C → l.toPropFun ≤ clauseListToPropFun C := by
  intro h
  rw [clauseListToPropFun_eq_toPropFun]
  apply Clause.toPropFun_mem_le
  rw [← Array.mem_data]
  exact h

theorem cnfPropFun_le_of_mem {Cs : List (Option (List ILit))} {C : List ILit} {i : Nat}
      {hi : i < Size.size Cs} :
    Seq.get Cs ⟨i, hi⟩ = some C → cnfListToPropFun Cs ≤ clauseListToPropFun C := by
  intro h
  simp [cnfListToPropFun_eq_toPropFun]
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

theorem list_satisfies_iff {τ : PropAssignment IVar} {Cs : List (Option (List ILit))} :
    τ ⊨ cnfListToPropFun Cs ↔ ∀ {C : List ILit}, (some C) ∈ Cs → τ ⊨ clauseListToPropFun C := by
  simp [cnfListToPropFun_eq_toPropFun]
  induction Cs with
  | nil => simp
  | cons C Cs ih =>
    match C with
    | none => simp [ih]
    | some C =>
      simp at ih ⊢
      intro _
      exact ih

namespace RangeArray

-- Returns the updated PPA. Returns `error` if `C` is a tautology, `ok` if not
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


-- A tail-recursive implementation that breaks the API to go faster
-- We prove that these two implementations are equal
def assumeRATClauseDirect (F : RangeArray ILit) (index : Fin F.size) (σ : PS) (τ : PPA) : Except PPA PPA :=
  let s := F.indexFin index
  /- CC: Instead of calculating `rsizeFin` and then subtracting off `s`,
        we compute the ending manually as the start of the next index.
        The performance improvement is about ~8-10%.  -/
  let e :=
    if h_index : index.val + 1 < F.size then
      F.indexFin ⟨index.val + 1, h_index⟩
    else
      F.dsize
  let rec loop (i : Nat) (τ : PPA) : Except PPA PPA :=
    if h : i < e then
      let lit := F.getFin ⟨i, by
        simp [e, indexFin_eq_index] at h
        split at h
        · have := lt_of_lt_of_le h (F.index_le_dataSize (index.val + 1))
          exact lt_of_lt_of_le this F.h_size
        · exact lt_of_lt_of_le h F.h_size⟩

      match σ.litValue lit with
      | Sum.inr true => error τ
      | Sum.inr false => loop (i + 1) τ
      | Sum.inl l =>
        match τ.litValue? l with
        | some true => error τ
        | some false => loop (i + 1) τ
        | none => loop (i + 1) (τ.setLit (-l))

      /-
      if hlit : lit.index < σ.gens.size then
        let gen := σ.gens.get ⟨lit.index, hlit⟩
        if gen ≥ σ.generation then
          let n := σ.mappings.get ⟨lit.index, by rw [σ.sizes_eq] at hlit; exact hlit⟩
          match n with
          | 0 =>
            if LitVar.polarity lit then error τ
            else loop (i + 1) τ
          | 1 =>
            if LitVar.polarity lit then loop (i + 1) τ
            else error τ
          | n =>
            -- Map the subst index back into a literal
            let l :=
              if n % 2 = 0 then
                LitVar.mkPos ⟨n / 2 + 1, Nat.succ_pos _⟩
              else
                LitVar.mkNeg ⟨n / 2 + 1, Nat.succ_pos _⟩
            -- TODO: Break the litValue api
            match τ.litValue? l with
            | some true => error τ
            | some false => loop (i + 1) τ
            | none => loop (i + 1) (τ.setLit (-l))
        else
          -- lit gets mapped to itself
          match τ.litValue? lit with
          | some true => error τ
          | some false => loop (i + 1) τ
          | none => loop (i + 1) (τ.setLit (-lit))
      -- If we are outside the size of σ, lit gets mapped to itself
      else
        match τ.litValue? lit with
        | some true => error τ
        | some false => loop (i + 1) τ
        | none => loop (i + 1) (τ.setLit (-lit)) -/
    else
      ok τ
  termination_by
    (if h_index : index.val + 1 < F.size then
      F.indexFin ⟨index.val + 1, h_index⟩
    else
      F.dsize) - i
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

@[inline]
def unitPropDirect (τ : PPA) (F : RangeArray ILit) (hint : Fin F.size) : PPA.UPResult :=
  let s := F.indexFin hint
  /- CC: Instead of calculating `rsizeFin` and then subtracting off `s`,
        we compute the ending manually as the start of the next index.
        The performance improvement is about ~8-10%.  -/
  let e :=
    if h_index : hint + 1 < F.size then
      F.indexFin ⟨hint + 1, h_index⟩
    else
      F.dsize
  --let gen := τ.generation
  let rec loop (i : Nat) (unit? : Option ILit) : PPA.UPResult :=
    if h : i < e then
      let lit := F.getFin ⟨i, by
        simp [e, indexFin_eq_index] at h
        split at h
        · have := lt_of_lt_of_le h (F.index_le_dataSize (hint + 1))
          exact lt_of_lt_of_le this F.h_size
        · exact lt_of_lt_of_le h F.h_size⟩
      /- match τ.assignment.get? lit.index with
      | none =>
        match unit? with
        | none => loop (i + 1) (some lit)
        | some u =>
          if u = lit then loop (i + 1) unit?
          else .multipleUnassignedLiterals
      | some n =>
        if gen ≤ n.natAbs then
          if xor (!(LitVar.polarity lit)) (0 < n) then
            .satisfied
          else
            loop (i + 1) unit?
        else
          match unit? with
          | none => loop (i + 1) (some lit)
          | some u =>
            if u = lit then loop (i + 1) unit?
            else .multipleUnassignedLiterals -/
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
  termination_by
    (if h_index : hint + 1 < F.size then
      F.indexFin ⟨hint + 1, h_index⟩
    else
      F.dsize) - i
  loop s none

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

@[inline]
def applyUPHintDirect (F : RangeArray ILit) (bumps : Nat) (τ : PPA) (hint : Nat) : PPA × HintResult :=
  if h_hint : hint < F.size then
    if !F.isDeletedFin ⟨hint, h_hint⟩ then
      match unitPropDirect τ F ⟨hint, h_hint⟩ with
      | .falsified => ⟨τ, .contra⟩
      | .satisfied => ⟨τ, .err⟩
      | .multipleUnassignedLiterals => ⟨τ, .err⟩
      | .unit l => (τ.setLitFor l bumps, .unit)
    else
      ⟨τ, .err⟩
  else
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

def reduceBreak (σ : PS) (F : RangeArray ILit) (index : Fin F.size) : ReductionResult :=
  let s := F.indexFin index
  /- CC: Instead of calculating `rsizeFin` and then subtracting off `s`,
         we compute the ending manually as the start of the next index.
         The performance improvement is about ~8-10%.  -/
  let e :=
    if h_index : index.val + 1 < F.size then
      F.indexFin ⟨index.val + 1, h_index⟩
    else
      F.dsize
  let rec loop (i : Nat) (reduced? : Bool) : ReductionResult :=
    if h : i < e then
      let lit := F.getFin ⟨i, by
        simp [e, indexFin_eq_index] at h
        split at h
        · have := lt_of_lt_of_le h (F.index_le_dataSize (index.val + 1))
          exact lt_of_lt_of_le this F.h_size
        · exact lt_of_lt_of_le h F.h_size⟩
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
  termination_by
    (if h_index : index.val + 1 < F.size then
      F.indexFin ⟨index.val + 1, h_index⟩
     else
      F.dsize) - i
  loop s false

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
    match applyUPHintsDirect F (line.ratHints.size + 1) τ line.upHints with
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
                if bumpCounter < line.ratHints.size then
                  -- Find the corresponding RAT hint
                  match findRATHintIndex cachedRatHintIndex i line.ratHintIndexes with
                  | none => ⟨τ, false⟩
                  | some ⟨ratIndex, hr⟩ =>
                    -- Assume the negation of the RAT clause
                    match assumeRATClauseDirect F ⟨i, hi⟩ σ τ with
                    | error τ => loop (i + 1) (ratIndex + 1) (bumpCounter + 1) τ.bump
                    | ok τ =>
                      match applyUPHintsDirect F 0 τ (Seq.get line.ratHints ⟨ratIndex, by rw [line.ratSizesEq] at hr; exact hr⟩) with
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

#exit

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
  simp [uAssumeNegatedForM, assumeNegatedClauseFor,
    @uAssume.loop.aux _ _ _ _ h_models bumps 0 (Size.size L)]

theorem assumeRATClauseDirect.loop.aux {F : RangeArray ILit} (σ : PS)
  {i j k : Nat} (hi : i < F.size) :
    k = F.rsizeFin ⟨i, hi⟩ - j →
    assumeRATClauseDirect.loop F ⟨i, hi⟩ σ (F.indexFin ⟨i, hi⟩ + j) = assumeRATClauseM.loop F ⟨i, hi⟩ σ j := by
  intro hk
  ext τ
  induction k generalizing τ j with
  | zero =>
    have h_le := Nat.le_of_sub_eq_zero hk.symm
    unfold assumeRATClauseM.loop
    simp [not_lt.mpr h_le]
    unfold assumeRATClauseDirect.loop
    simp [not_lt.mpr h_le]
  | succ k ih =>
    rw [Nat.succ_eq_add_one] at hk
    unfold assumeRATClauseDirect.loop assumeRATClauseM.loop
    have hj : j < F.rsizeFin ⟨i, hi⟩ := by
      apply Nat.lt_of_sub_pos
      rw [← hk]
      exact Nat.zero_lt_succ k
    simp [hj, ogetFin_eq_getFin]
    replace ih := ih (Nat.eq_sub_succ_of_succ_eq_sub hk)
    split <;> rename _ => h_litValue
    stop
    --<;> simp [h_litValue]
    · rw [add_assoc]
      exact ih _
    · rename ILit => lit
      split <;> rename _ => hτ
      · rfl
      · exact ih _
      · rw [add_assoc]
        exact ih _

#exit

theorem assumeRATClauseDirect_eq_assumeRATClauseM : assumeRATClauseDirect = assumeRATClauseM := by
  ext F index σ τ
  have ⟨i, hi⟩ := index
  simp [assumeRATClauseDirect, assumeRATClauseM]
  have := @assumeRATClauseDirect.loop.aux F σ i 0 (F.rsizeFin ⟨i, hi⟩) hi (by simp)
  simp at this
  rw [this]

/-
theorem uAssume.loop.aux {F : RangeArray ILit} {τ : PPA} {Ls : List (Option (List ILit))} {L : List ILit}
  (h_models : models F Ls L) {bumps : Nat} {i j : Nat} :
  j = Size.size L - i →
    uAssumeNegatedForM.loop F bumps i τ = assumeNegatedClauseFor.loop { data := L } bumps i τ
-/

/-theorem assumeRATClauseM.loop.aux {F : RangeArray ILit}
    {Ls : List (Option (List ILit))} {L : List ILit} (h_models: models F Ls L)
    {i : Nat} (hi : i < Size.size Ls)
      {C : List ILit} (hC : Seq.get Ls ⟨i, hi⟩ = some C)
      {τ : PPA} {j k : Nat} :
  k = Size.size C - j →
    assumeRATClauseM.loop F ⟨i, h_models.h_size₁ ▸ hi⟩ τ j = assumeNegatedClauseFor.loop { data := C } 0 j τ := by
  sorry
  done-/

/- theorem assumeRATClauseM.loop.cons_aux {F : RangeArray ILit}
      {Ls : List (Option (List ILit))} {L : List ILit} (h_models : models F Ls L)
      {i : Nat} (hi : i < Size.size Ls)
      {lit : ILit} {C : List ILit} (hC : Seq.get L ⟨i, hi⟩ = some (lit :: C))
      {τ : PPA} {j k : Nat} :
    k = Size.size L - j → -/

/-
theorem assumeNegatedClauseFor.loop.cons_aux (τ : PPA) (l : ILit) (bumps : Nat)
      {ls : List ILit} {i j : Nat} :
    j = ls.length - i → assumeNegatedClauseFor.loop { data := l :: ls } bumps (i + 1) τ =
      assumeNegatedClauseFor.loop { data := ls } bumps i τ := by
  intro hj
  induction j generalizing τ i with
  | zero =>
    have := Nat.le_of_sub_eq_zero hj.symm
    unfold loop
    simp [LeanColls.size, not_lt.mpr this, not_lt.mpr (succ_le_succ_iff.mpr this)]
  | succ j ih =>
    rw [succ_eq_add_one] at hj
    unfold loop
    simp [LeanColls.size, succ_eq_add_one]
    have hi : i < List.length ls := by
      apply Nat.lt_of_sub_pos
      rw [← hj]
      exact Nat.zero_lt_succ j
    simp [hi]
    have : Seq.get ({data := l :: ls} : IClause) ⟨i + 1, succ_lt_succ hi⟩
      = Seq.get ({data := ls} : IClause) ⟨i, hi⟩ := rfl
    rw [this]
    split <;> rename _ => h_get
    <;> simp [h_get]
    · apply @ih (setLitFor τ (-Seq.get ({ data := ls } : IClause) { val := i, isLt := hi }) bumps) (i + 1)
      exact Nat.eq_sub_succ_of_succ_eq_sub hj
    · apply @ih τ
      exact Nat.eq_sub_succ_of_succ_eq_sub hj

theorem assumeNegatedClauseFor.loop.cons (τ : PPA) (l : ILit) (ls : List ILit) (bumps i : Nat) :
    assumeNegatedClauseFor.loop { data := l :: ls } bumps (i + 1) τ
      = assumeNegatedClauseFor.loop { data := ls } bumps i τ :=
  @assumeNegatedClauseFor.loop.cons_aux τ l bumps ls i (ls.length - i) rfl
-/

theorem assumeRATClauseM.loop_Lawful {F : RangeArray ILit}
    {Ls : List (Option (List ILit))} {L : List ILit} (h_models : models F Ls L)
    {i : Nat} (hi : i < Size.size Ls)
    {C : List ILit} (hC : Seq.get Ls ⟨i, hi⟩ = some C)
    (τ τ' : PPA) (σ : PS) {j k : Nat} :
    k = Size.size C - j →
      (assumeRATClauseM.loop F ⟨i, h_models.h_size₁ ▸ hi⟩ σ j τ = .error τ'
        → τ.toPropFun ≤ PropFun.substL (clauseListToPropFun (C.drop j)) σ.toSubst ∧ extended τ τ' 0)
    ∧ (assumeRATClauseM.loop F ⟨i, h_models.h_size₁ ▸ hi⟩ σ j τ = .ok τ'
        → τ'.toPropFun = ↑τ ⊓ (PropFun.substL (clauseListToPropFun (C.drop j)) σ.toSubst)ᶜ
            ∧ extended τ τ' 0) := by
  intro hk
  induction k generalizing τ j with
  | zero =>
    have h_le₁ := Nat.le_of_sub_eq_zero hk.symm
    have h_le₂ := h_models.h_sizes hi hC
    unfold assumeRATClauseM.loop
    simp only [LeanColls.size] at h_le₁ h_le₂ ⊢
    simp [not_lt.mpr h_le₁]
    -- We split because the hypothesis is dependent. Otherwise can be proven
    split <;> rename _ => h_rsize
    · -- Contradiction branch
      rw [rsizeFin_eq_rsize, h_le₂] at h_rsize
      exact absurd h_le₁ (not_le.mpr h_rsize)
    · simp [assumeRATClauseM]
      rintro rfl
      simp [List.drop_eq_nil_iff_le.mpr h_le₁]
  | succ k ih =>
    rw [Nat.succ_eq_add_one] at hk
    unfold assumeRATClauseM.loop
    simp [LeanColls.size] at hk ⊢
    split <;> rename _ => h_rsize
    · rw [rsizeFin_eq_rsize, h_models.h_sizes hi hC] at h_rsize
      rw [ogetFin_eq_oget, h_models.h_agree hi hC h_rsize]
      simp [← List.get_cons_drop C ⟨_, h_rsize⟩]
      split <;> rename _ => h_litValue
      · simp [ogetFin_eq_oget, h_models.h_agree hi hC h_rsize, Seq.get] at h_litValue
        simp [← satisfies_substL, ← PS.litValue_eq_substL', h_litValue]
        rintro rfl
        exact extended_refl _ _
      · rcases @ih τ (j + 1) (Nat.eq_sub_succ_of_succ_eq_sub hk) with ⟨ih₁, ih₂⟩
        constructor
        · intro h_loop
          rcases ih₁ h_loop with ⟨h₁, h₂⟩
          simp [h₂]
          apply le_trans h₁
          simp
        · intro h_loop
          rcases ih₂ h_loop with ⟨h₁, h₂⟩
          simp [h₂]
          simp [Seq.get] at h_litValue
          simp [← PS.litValue_eq_substL', h_litValue, h₁]
      · rename ILit => lit_mapped
        split <;> rename _ => h_litValue?
        · simp [ogetFin_eq_oget, h_models.h_agree hi hC h_rsize, Seq.get] at h_litValue
          rw [litValue?_true_iff] at h_litValue?
          simp [← satisfies_substL, ← PS.litValue_eq_substL', h_litValue]
          rintro rfl
          simp
          apply le_trans h_litValue?
          exact le_sup_left
        · rcases @ih τ _ (Nat.eq_sub_succ_of_succ_eq_sub hk) with ⟨ih₁, ih₂⟩
          constructor
          · intro h_loop
            rcases ih₁ h_loop with ⟨h₁, h₂⟩
            simp [h₂]
            apply le_trans h₁
            simp
          · intro h_loop
            rcases ih₂ h_loop with ⟨h₁, h₂⟩
            simp [h₂]
            simp [Seq.get] at h_litValue
            simp [← PS.litValue_eq_substL', h_litValue, h₁]
            have := litValue?_false_iff.mp h_litValue?
            have : toPropFun τ ⊓ (LitVar.toPropFun lit_mapped)ᶜ = toPropFun τ := by
              apply le_antisymm
              · exact inf_le_left
              · have h_inf : toPropFun τ ≤ toPropFun τ ⊓ toPropFun τ := by simp
                apply le_trans h_inf
                apply inf_le_inf_left
                exact this
            simp [← inf_assoc, this]
        · rcases @ih (τ.setLit (-lit_mapped)) _ (Nat.eq_sub_succ_of_succ_eq_sub hk) with ⟨ih₁, ih₂⟩
          simp [Seq.get] at h_litValue
          simp [← satisfies_substL, ← PS.litValue_eq_substL', h_litValue]
          rw [← litValue?_negate_none_iff] at h_litValue?
          have := extended_setLitFor_of_none h_litValue? 0
          constructor
          · intro h_loop
            rcases ih₁ h_loop with ⟨h₁, h₂⟩
            simp [toPropFun_setLit_of_none h_litValue?, inf_compl_le_iff_le_sup] at h₁
            simp [h₁, extended_trans this h₂]
          · intro h_loop
            rcases ih₂ h_loop with ⟨h₁, h₂⟩
            simp [toPropFun_setLit_of_none h_litValue?, inf_compl_le_iff_le_sup] at h₁
            simp [← inf_assoc, h₁, extended_trans this h₂]
    · -- Contradiction branch
      simp [rsizeFin_eq_rsize, h_models.h_sizes hi hC, LeanColls.size] at h_rsize
      have : j < List.length C := by omega
      exact absurd h_rsize (not_le.mpr this)

/-- Unfortunately, because `LawfulAssumeNegatedFor` requires a clause, but a
    clause C under a substitution σ via `substL` is not guaranteed to be a
    clause (it is a PropFun), we need to use the facts from LawfulAssumeNegatedFor
    directly.  -/
theorem assumeRATClauseM_Lawful {F : RangeArray ILit}
    {Ls : List (Option (List ILit))} {L : List ILit} (h_models : models F Ls L)
    {i : Nat} (hi : i < Size.size Ls)
    {C : List ILit} (hC : Seq.get Ls ⟨i, hi⟩ = some C)
    (τ τ' : PPA) (σ : PS) :
      (assumeRATClauseM F ⟨i, h_models.h_size₁ ▸ hi⟩ σ τ = .error τ'
        → τ.toPropFun ≤ PropFun.substL (clauseListToPropFun C) σ.toSubst ∧ extended τ τ' 0)
    ∧ (assumeRATClauseM F ⟨i, h_models.h_size₁ ▸ hi⟩ σ τ = .ok τ'
        → τ'.toPropFun = ↑τ ⊓ (PropFun.substL (clauseListToPropFun C) σ.toSubst)ᶜ
            ∧ extended τ τ' 0) := by
  simp [assumeRATClauseM]
  have := @assumeRATClauseM.loop_Lawful F Ls L h_models i hi C hC τ τ' σ 0 (Size.size C) rfl
  simp at this
  exact this

/-
theorem assumeRATClauseM.loop_Lawful {F : RangeArray ILit}
    {Ls : List (Option (List ILit))} {L : List ILit} (h_models : models F Ls L)
    {i : Nat} (hi : i < Size.size Ls)
    {C : List ILit} (hC : Seq.get Ls ⟨i, hi⟩ = some C)
    (τ τ' : PPA) (σ : PS) {j k : Nat} :
    k = Size.size C - j →
      (assumeRATClauseM.loop F ⟨i, h_models.h_size₁ ▸ hi⟩ σ j τ = .error τ'
        → τ.toPropFun ≤ PropFun.substL (clauseListToPropFun (C.drop j)) σ.toSubst ∧ extended τ τ' 0)
    ∧ (assumeRATClauseM.loop F ⟨i, h_models.h_size₁ ▸ hi⟩ σ j τ = .ok τ'
        → τ'.toPropFun = ↑τ ⊓ (PropFun.substL (clauseListToPropFun (C.drop j)) σ.toSubst)ᶜ
            ∧ extended τ τ' 0) := by
-/

theorem unitProp_loop_eq_unitProp_go {F : RangeArray ILit}
  {Ls : List (Option (List ILit))} {L C : List ILit} (h_models : models F Ls L)
  {τ : PPA} {hint : Nat} {h_hint : hint < Size.size Ls} {i j : Nat} :
    j = Size.size C - i →
    Seq.get Ls ⟨hint, h_hint⟩ = some C →
      ∀ (unit? : Option ILit),
        (unitProp.loop τ F ⟨hint, h_models.h_size₁ ▸ h_hint⟩ i unit?
          = PPA.unitProp.go τ ({ data := C }) i unit?) := by
  intro hj hC unit?
  simp [LeanColls.size] at hj
  induction j generalizing i unit? with
  | zero =>
    unfold unitProp.loop unitProp.go
    simp [LeanColls.size, rsizeFin_eq_rsize, h_models.h_sizes h_hint hC, ogetFin_eq_oget]
    have h_le := Nat.le_of_sub_eq_zero hj.symm
    simp [LeanColls.size] at h_le
    simp [LeanColls.size, not_lt.mpr h_le]
    rfl
  | succ j ih =>
    unfold unitProp.loop unitProp.go
    simp [LeanColls.size, rsizeFin_eq_rsize, h_models.h_sizes h_hint hC, ogetFin_eq_oget]
    rw [Nat.succ_eq_add_one] at hj
    have : i < List.length C := by
      apply Nat.lt_of_sub_pos
      rw [← hj]
      exact Nat.zero_lt_succ j
    have h_get : Seq.get ({ data := C } : IClause) ⟨i, this⟩ = Seq.get C ⟨i, this⟩ := rfl
    simp [this, h_get, h_models.h_agree h_hint hC this]
    split <;> rename _ => h_litValue
    <;> simp [h_litValue]
    · exact ih (Nat.eq_sub_succ_of_succ_eq_sub hj) unit?
    · simp [ih (Nat.eq_sub_succ_of_succ_eq_sub hj)]
      cases unit? <;> simp

theorem unitProp_eq_unitProp {F : RangeArray ILit}
  {Ls : List (Option (List ILit))} {L C : List ILit} (h_models : models F Ls L)
  {τ : PPA} {hint : Nat} {h_hint : hint < Size.size Ls} :
    Seq.get Ls ⟨hint, h_hint⟩ = some C →
    RangeArray.unitProp τ F ⟨hint, h_models.h_size₁ ▸ h_hint⟩ = PPA.unitProp τ ({ data := C } : IClause) := by
  intro hC
  simp [RangeArray.unitProp, PPA.unitProp]
  exact @unitProp_loop_eq_unitProp_go _ _ _ _ h_models τ _ h_hint 0 (Size.size C) rfl hC none

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
  rw [unitProp_eq_unitProp h_models hsL] at h_up
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
  rw [unitProp_eq_unitProp h_models hsL] at h_up
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
        rw [_root_.eq_bot_iff] at h₁ ⊢
        exact le_trans this h₁
      · exact extended_trans (extended_setLitFor_of_none hτlit' bumps) h₂
    · injection h_uphints
      rename τ₂ = _ => h; subst h
      rename applyUPHint _ _ _ _ = _ => h_up
      rcases applyUPHint_contra h_models h_up with ⟨h_hint, sL, hsL, rfl, h_inf⟩
      constructor
      · have := cnfPropFun_le_of_mem hsL
        rw [_root_.eq_bot_iff] at h_inf ⊢
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

theorem cnfPropFun_compl_le_compl_of_mem {Cs : List (Option (List ILit))} {C : List ILit} {i : Nat}
      {hi : i < Cs.length} :
    Seq.get Cs ⟨i, hi⟩ = some C → (clauseListToPropFun C)ᶜ ≤ (cnfListToPropFun Cs)ᶜ := by
  simp only [compl_le_compl_iff_le]
  exact cnfPropFun_le_of_mem

theorem checkLine.loop_ok_aux {line : SRAdditionLine} {F : RangeArray ILit}
    {Ls : List (Option (List ILit))} {L : List ILit} (h_models : models F Ls L)
    {τ τ' : PPA} {σ : PS} {i j cri bc : Nat} :
  j = F.size - i →
  uniform τ (line.ratHints.size + 1 - bc) →
    checkLine.loop line F σ i cri bc τ = ⟨τ', true⟩ →
    ---- can probably be done in a suffices -----
      (∃ (b : Nat), b ≤ line.ratHints.size + 1 - bc ∧ uniform τ' b)
      ∧ τ'.toPropFun = τ.toPropFun
    ---- suffices -----
      ∧ ∀ {k : Nat} {hk : k < Size.size Ls} {C : List ILit},
        Seq.get Ls ⟨k, hk⟩ = some C → i ≤ k →
          (cnfListToPropFun Ls) ⊓ τ ≤ PropFun.substL (clauseListToPropFun C) σ.toSubst := by
  stop
  intro hj h_uniform; simp
  induction j generalizing τ i cri bc with
  | zero =>
    have hi : i ≥ F.size := Nat.le_of_sub_eq_zero hj.symm
    unfold loop
    simp [not_lt.mpr hi, not_lt.mpr (Nat.succ_le_succ_iff.mpr hi)]
    rintro rfl
    simp
    use ⟨line.ratHints.size + 1 - bc, le_refl _, h_uniform⟩
    intro k hk₂ _ _ hk₁
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
      intro k hk₂ C hC hk₁
      rw [isDeletedFin_eq_isDeleted hi] at h_del
      by_cases hik : i = k
      · -- if i = k, then we derive contradiction
        subst hik
        rw [h_models.h_size₁] at hi
        have := h_models.h_some hi
        simp [h_del, hC] at this
      · -- Otherwise, k is a higher index
        have : i + 1 ≤ k := Nat.succ_le_of_lt (lt_of_le_of_ne hk₁ hik)
        exact hkC hC this
    · -- Not deleted, so we actually check the clause
      rename ¬(_ = true) => h_del; simp at h_del
      split
      · -- Reduction returned .satisfied
        rename _ => h_reducedSatisfied
        intro h_loop
        rcases ih (Nat.eq_sub_succ_of_succ_eq_sub hj) h_uniform h_loop with ⟨hτ, hpf, hkC⟩
        use hτ, hpf
        intro k hk₂ C hC hk₁
        have hj' := Nat.eq_sub_succ_of_succ_eq_sub hj
        by_cases hik : i = k
        · -- if i = k, then the loop body checks the kth clause
          subst hik
          rw [reduceBreak_eq_reduce F hi σ] at h_reducedSatisfied
          rw [h_models.h_size₁] at hi
          rw [reduce_eq_reduce h_models hi hC] at h_reducedSatisfied
          simp [(PS.reduce_Lawful σ { data := C }).1 h_reducedSatisfied]
        · -- Otherwise, k is a higher index
          have : i + 1 ≤ k := Nat.succ_le_of_lt (lt_of_le_of_ne hk₁ hik)
          exact hkC hC this
      · -- Reduction returned .notReduced, so we skip the clause here too
        rename _ => h_notReduced
        intro h_loop
        rcases ih (Nat.eq_sub_succ_of_succ_eq_sub hj) h_uniform h_loop with ⟨hτ, hpf, hkC⟩
        use hτ, hpf
        intro k hk₂ C hC hk₁
        have hj' := Nat.eq_sub_succ_of_succ_eq_sub hj
        by_cases hik : i = k
        · -- if i = k, then the loop body checks the kth clause
          subst hik
          rw [reduceBreak_eq_reduce F hi σ] at h_notReduced
          rw [h_models.h_size₁] at hi
          rw [reduce_eq_reduce h_models hi hC] at h_notReduced
          simp [(PS.reduce_Lawful σ { data := C }).2 h_notReduced]
          have := cnfPropFun_le_of_mem hC
          simp at this
          exact le_trans inf_le_left this
        · -- Otherwise, k is a higher index
          have : i + 1 ≤ k := Nat.succ_le_of_lt (lt_of_le_of_ne hk₁ hik)
          exact hkC hC this
      · -- Reduction returned .reduced
        rename _ => h_reduced
        split <;> try simp
        rename bc < _ => h_bc
        split <;> try simp
        rename Nat => ratIndex
        rename ratIndex < _ => h_ratIndex
        rename _ => h_findRatHint
        have hi₂ := h_models.h_size₁ ▸ hi
        have := h_models.h_some hi₂
        rw [isDeletedFin_eq_isDeleted hi] at h_del
        simp [h_del] at this
        rcases this with ⟨C, hC⟩
        have h_bumps_left : ∃ (bumps_left : Nat), bumps_left + 2 = line.ratHints.size + 1 - bc := by
          use line.ratHints.size + 1 - bc - 2
          rw [Nat.sub_add_cancel]
          omega
        rcases h_bumps_left with ⟨bumps_left, h_bumps_left⟩
        rw [← h_bumps_left] at h_uniform
        -- How does assuming the negation of the reduced clause go?
        split
        · -- .error, meaning that τ satisfied the reduced clause
          rename_i τ₂ h_assumeRAT
          intro h_loop
          rw [assumeRATClauseDirect_eq_assumeRATClauseM] at h_assumeRAT
          rcases (assumeRATClauseM_Lawful h_models hi₂ hC τ τ₂ σ).1 h_assumeRAT with ⟨h_sat, h_ext⟩
          clear h_assumeRAT
          simp at h_sat
          rcases uniform_bump_of_uniform_of_extended' h_uniform h_ext with ⟨h_uniform₂, hτ_pf⟩
          rw [Nat.eq_sub_succ_of_succ_eq_sub h_bumps_left] at h_uniform₂
          rcases ih (Nat.eq_sub_succ_of_succ_eq_sub hj) h_uniform₂ h_loop with ⟨⟨bc', hbc', h_uniform'⟩, hpf, hkC⟩
          have hbc_le : bc' ≤ line.ratHints.size + 1 - bc := by omega
          use ⟨bc', hbc_le, h_uniform'⟩
          rw [hτ_pf]
          use hpf
          intro k hk₂ D hD hk₁
          rcases eq_or_lt_of_le hk₁ with (rfl | hk₁)
          · rw [hD] at hC; injection hC; rename _ => hD; subst hD
            apply le_trans _ h_sat
            rw [hτ_pf]
            exact inf_le_right
          · exact hkC hD hk₁
        · -- .ok, meaning that the negation of the reduced clause was assumed
          rename_i τ₂ h_assumeRAT
          -- Does unit propagation find contradiction?
          split <;> try simp
          -- We found a contradiction (the only acceptable result to return `true` at top-level)
          rename_i τ₃ h_up
          intro h_loop
          rw [assumeRATClauseDirect_eq_assumeRATClauseM] at h_assumeRAT
          rcases (assumeRATClauseM_Lawful h_models hi₂ hC τ τ₂ σ).2 h_assumeRAT with ⟨h_sat, h_ext⟩
          clear h_assumeRAT
          simp at h_sat
          rcases applyUPHints_contra h_models h_up with ⟨hτ₂, h_ext₂⟩
          have h_ext₃ := extended_trans h_ext h_ext₂
          rcases uniform_bump_of_uniform_of_extended' h_uniform h_ext₃ with ⟨h_uniform₃, hτ_pf⟩
          rw [Nat.eq_sub_succ_of_succ_eq_sub h_bumps_left] at h_uniform₃
          rcases ih (Nat.eq_sub_succ_of_succ_eq_sub hj) h_uniform₃ h_loop with ⟨⟨bc', hbc', h_uniform'⟩, hpf, hkC⟩
          simp at hbc'
          have hbc_le : bc' ≤ line.ratHints.size + 1 - bc := by omega
          use ⟨bc', hbc_le, h_uniform'⟩
          rw [hτ_pf, hpf]
          use rfl
          intro k hk₂ D hD hk₁
          rcases eq_or_lt_of_le hk₁ with (rfl | hk₁)
          · rw [hD] at hC; injection hC; rename _ => hD; subst hD
            clear hkC h_up h_del h_reduced h_loop hbc' hbc_le
            rw [hτ_pf] at h_sat
            rw [h_sat, ← inf_assoc] at hτ₂
            rw [PropFun.le_iff_inf_compl_le_bot, le_bot_iff]
            exact hτ₂
          · exact hkC hD hk₁

theorem checkLine.loop_ok {F : RangeArray ILit} {Ls : List (Option (List ILit))} {L : List ILit}
    (h_models : models F Ls L) {τ τ' : PPA} {σ : PS} {line : SRAdditionLine} :
    uniform τ (line.ratHints.size + 1) →
    checkLine.loop line F σ 0 0 0 τ = ⟨τ', true⟩ →
      (cnfListToPropFun Ls) ⊓ τ ≤ PropFun.substL (cnfListToPropFun Ls) σ.toSubst := by
  intro h_uniform h_loop
  have : F.size = F.size - 0 := by omega
  conv at h_uniform => rhs; rw [← Nat.sub_zero (line.ratHints.size + 1)]
  have := checkLine.loop_ok_aux h_models this h_uniform h_loop
  rcases this with ⟨_, _, h_loop⟩
  simp at h_loop
  refine entails_ext.mpr fun τ' hτ' => ?_
  rw [satisfies_substL]
  simp [list_satisfies_iff]
  intro C hC
  simp only [← satisfies_substL]
  simp at hτ'
  rcases hτ' with ⟨hLs, hτ⟩
  rw [list_satisfies_iff] at hLs
  have := hLs hC
  have h_get : ∃ (k : Nat) (hk : k < Size.size Ls), Seq.get Ls ⟨k, hk⟩ = some C := by
    rw [List.mem_iff_get] at hC
    rcases hC with ⟨⟨n, hn⟩, hC⟩
    simp [LeanColls.size]
    use n, hn, hC
  rcases h_get with ⟨k, hk, h_get⟩
  apply entails_ext.mp (h_loop h_get) τ'
  simp
  rw [← list_satisfies_iff] at hLs
  use hLs, hτ

theorem eqsat_of_SR {F C : PropFun ν} :
    (∃ σ, F ⊓ Cᶜ ≤ subst (F ⊓ C) σ) → eqsat F (F ⊓ C) := by
  rintro ⟨σ, hSR⟩
  constructor
  · rintro ⟨τ, hτF⟩
    by_cases hτC : τ ⊨ C
    · use τ
      rw [satisfies_conj]
      exact ⟨hτF, hτC⟩
    · replace hSR := entails_ext.mp hSR τ
      simp [satisfies_conj, and_imp, -satisfies_substL] at hSR
      replace hSR := hSR hτF hτC
      use PropAssignment.subst σ τ
      rw [satisfies_conj]
      exact hSR
  · rintro ⟨τ, hτ⟩
    rw [satisfies_conj] at hτ
    exact ⟨τ, hτ.1⟩

theorem eqsat_of_SR' {F C : PropFun ν} :
    (∃ σ, F ⊓ Cᶜ ≤ substL (F ⊓ C) σ) → eqsat F (F ⊓ C) := by
  rintro ⟨σ, hSR⟩
  constructor
  · rintro ⟨τ, hτF⟩
    by_cases hτC : τ ⊨ C
    · use τ
      rw [satisfies_conj]
      exact ⟨hτF, hτC⟩
    · replace hSR := entails_ext.mp hSR τ
      simp [satisfies_conj, and_imp, -satisfies_substL] at hSR
      replace hSR := hSR hτF hτC
      use PropAssignment.subst (liftSubst σ) τ
      rw [satisfies_conj]
      simp [← subst_liftSubst_eq_substL] at hSR
      exact hSR
  · rintro ⟨τ, hτ⟩
    rw [satisfies_conj] at hτ
    exact ⟨τ, hτ.1⟩

theorem checkLine_correct {F : RangeArray ILit} {τ : PPA} {σ : PS} {line : SRAdditionLine}
    {S : SRState} {Cs : List (Option (List ILit))} {C : List ILit} :
    models F Cs C →
    checkLine ⟨F, τ, σ⟩ line = .ok S →
      (∃ τ' σ', S = ⟨F.commit, τ', σ'⟩) ∧
      PropFun.eqsat (cnfListToPropFun Cs) (cnfListToPropFun Cs ⊓ clauseListToPropFun C) := by
  intro h_models h_checkLine
  simp [checkLine] at h_checkLine
  split at h_checkLine
  · contradiction
  · rename PPA => τ₁
    rename _ = ok τ₁ => h_uAssume
    rw [uAssumeNegatedForM_eq_assumeNegatedClauseFor h_models] at h_uAssume
    rcases PPA.assumeNegatedClauseFor_Lawful τ.reset τ₁ { data := C } (Array.size line.ratHints + 1) with ⟨_, h₂⟩
    rcases h₂ h_uAssume with ⟨h_toPropFun_τ₁, h_ext₁⟩
    simp at h_toPropFun_τ₁
    clear h₂
    split at h_checkLine
    <;> rename PPA => τ₂
    · contradiction
    · split at h_checkLine
      · contradiction
      · injection h_checkLine; rename _ => h; subst h
        rename _ = (_, HintResult.contra) => h_hints
        rcases applyUPHints_contra h_models h_hints with ⟨hF, _⟩
        rw [h_toPropFun_τ₁] at hF
        constructor
        · use τ₂, σ
        · apply PropFun.eqsat_of_entails
          rw [clauseListToPropFun_eq_toPropFun]
          rwa [_root_.eq_bot_iff, ← PropFun.le_iff_inf_compl_le_bot] at hF
    · split at h_checkLine <;> try contradiction
      rename applyUPHints _ _ _ _ = _ => h_uphints
      rename F.dsize < _ => h_Fsize
      split at h_checkLine <;> try contradiction
      rename _ = ugetFin _ => h_getD
      split at h_checkLine <;> try contradiction
      rename PPA => τ₃
      rename checkLine.loop _ _ _ _ _ _ _ = _ => h_checkLine_loop
      injection h_checkLine; rename _ => hS
      -- Now we unpack all the hypotheses about the "success" path to derive the SR statement
      rcases applyUPHints_unit h_models h_uphints with ⟨h_le₁₂, h_ext₁₂⟩
      clear h_uphints
      have h_uniform₁ := uniform_of_extended_reset h_ext₁
      have h_uniform₂ := uniform_of_uniform_of_extended h_uniform₁ h_ext₁₂
      rw [ugetFin_eq_uget] at h_checkLine_loop hS h_getD
      have := checkLine.loop_ok h_models h_uniform₂ h_checkLine_loop
      simp [← hS]
      apply eqsat_of_SR'
      use (assumeWitness σ (Option.getD line.witnessLits[0]? (uget F 0)) line.witnessLits
            line.witnessMaps).toSubst
      rw [substL_conj, le_inf_iff]
      constructor
      · apply le_trans _ this
        simp [← h_toPropFun_τ₁]
        exact h_le₁₂
      · apply le_trans le_top
        simp [h_getD, assumeWitness]
        ext τ_abs
        simp [Clause.satisfies_iff]
        use uget F 0
        constructor
        · -- The first literal is a member of C, through the model
          have : 0 < Size.size C := by
            simp [← h_models.h_size₂]
            exact h_Fsize
          rw [h_models.h_uncommitted this]
          simp [Seq.get, ← Array.mem_data]
          exact List.get_mem C _ _
        · -- We drop σ back into the PS model
          -- We set the first literal to true in σ, so it satisfies C
          simp [← satisfies_substL, ← PS.litValue_eq_substL']

end SR
