/-

An abstracted checker for SR.

Authors: Cayden Codel
Carnegie Mellon University

-/

import Experiments.ProofChecking.PPA
import Experiments.ProofChecking.PS
import Experiments.ProofChecking.RangeArray
import Experiments.ProofChecking.SRParserBasic

import LeanSAT.Data.Cnf
import LeanSAT.Model.PropFun
import LeanSAT.Model.Subst

open LeanSAT LeanSAT.Model Nat
open PPA PS ILit IVar LitVar LawfulLitVar PropFun

namespace SR

-- Standing for "Formula and candidate clause"
-- CC: What does it mean to specialize a `class`?
@[specialize]
class FaC (FC : Type _) where
  new : FC
  size : FC → Nat
  clauseSize : (F : FC) → (Fin (size F)) → Nat
  candidateSize : FC → Nat
  addCandidateLiteral : FC → ILit → FC
  addCandidate : FC → FC
  deleteClause : (F : FC) → (Fin (size F)) → FC
  isDeleted : (F : FC) → (Fin (size F)) → Bool
  getLit : (F : FC) → (i : Fin (size F)) → (Fin (clauseSize F i)) → ILit
  getCandidateLit : (F : FC) → (i : Fin (candidateSize F)) → ILit
  toPropFunClause : (F : FC) → (i : Fin (size F)) → PropFun IVar
  toPropFun : FC → PropFun IVar
  toPropFunCandidate : FC → PropFun IVar
  unitProp : (F : FC) → (i : Fin (size F)) → PPA → MUPResult

instance : FaC (RangeArray ILit) where
  new := (RangeArray.empty : RangeArray ILit)
  size := RangeArray.size
  clauseSize := (fun F i => F.rsize i)
  candidateSize := RangeArray.uncommittedSize
  addCandidateLiteral := RangeArray.addElement
  addCandidate := RangeArray.commit
  deleteClause := (fun F i => F.delete i.val)
  isDeleted := (fun F i => F.isDeleted i.val)
  getLit := (fun F i j => F.getO i j)
  getCandidateLit := (fun F ⟨i, hi⟩ => F.get ⟨F.dsize + i, by
    simp [RangeArray.uncommittedSize] at hi
    done⟩)
  toPropFunClause := sorry
  toPropFun := sorry
  toPropFunCandidate := sorry
  unitProp := (fun F i τ => PPA.unitProp τ F.data (F.index i) (F.index i + F.rsize i))

instance : FaC (ICnf × IClause) where
  new := (#[], #[])
  size := (fun ⟨F, _⟩ => F.size)
  clauseSize := (fun ⟨F, _⟩ i => (F.get i).size)
  candidateSize := (fun ⟨_, C⟩ => C.size)
  addCandidateLiteral := (fun ⟨F, C⟩ l => ⟨F, C.push l⟩)
  addCandidate := (fun ⟨F, C⟩ => (F.push C, #[]))
  deleteClause := (fun ⟨F, C⟩ i => ⟨F.set i #[mkPos 1, mkNeg 1], C⟩)
  isDeleted := (fun _ _ => false)
  getLit := (fun ⟨F, _⟩ i j => (F.get i).get j)
  getCandidateLit := (fun ⟨_, C⟩ i => C.get i)
  toPropFunClause := (fun ⟨F, _⟩ i => (F.get i).toPropFun)
  toPropFun := (fun ⟨F, _⟩ => F.toPropFun)
  toPropFunCandidate := (fun ⟨_, C⟩ => C.toPropFun)
  unitProp := (fun ⟨F, _⟩ i τ => PPA.unitProp τ (F.get i))

open FaC

inductive AssumeCandidateResult
  | sat
  | updated
  deriving DecidableEq, Inhabited

inductive AssumeRATResult
  | sat
  | updated
  deriving DecidableEq, Inhabited

inductive UPResult where
  | conflict
  | updated
  | satOrMult
  | err
  deriving Inhabited, DecidableEq

inductive LineResult where
  | lineOk
  | lineOkAndDerivedEmptyClause
  | err

class SRChecker (FC : Type _) [FaC FC] where
  assumeCandidate : FC → PPA → Nat → (AssumeCandidateResult × PPA)
  applyUPHints : FC → PPA → Nat → Array Nat → (UPResult × PPA)
  assumeWitness : PS → ILit → Array ILit → Array ILit → PS
  assumeRAT : (F : FC) → (Fin (size F)) → PS → PPA → (AssumeRATResult × PPA)
  checkRATClauses : (F : FC) → PS → PPA → Array Nat → Array (Array Nat)
#exit

class LawfulFaC (FC : Type _) [FaC FC] where
  addCandidateLitLawful (F : FC) (l : ILit) :
    toPropFunCandidate (addCandidateLiteral F l) = toPropFunCandidate F ⊔ l

  addCandidateLawful (F : FC) :
    toPropFun (addCandidate F) = toPropFun F ⊓ toPropFunCandidate F ∧
    toPropFunCandidate (addCandidate F) = ⊥

  -- CC: Weaker than actually deleting, but is all that's required for checking
  deleteClauseLawful (F : FC) (i : Fin (size F)) :
    toPropFun (deleteClause F i) ≥ toPropFun F

  toPropFunClauseLawful (F : FC) (i : Fin (size F)) (j : Fin (clauseSize F i)) :
    (getLit F i j) ≤ toPropFunClause F i

  toPropFunLawful (F : FC) (i : Fin (size F)) :
    toPropFun F ≤ toPropFunClause F i

  -- CC: TODO lawful unit prop

variable {FC : Type _} [FaC FC]

inductive AssumeRATResult
  | sat
  | updated
  deriving DecidableEq, Inhabited

@[specialize]
def assumeRATClause (F : FC) (index : Fin (size F)) (σ : PS) (τ : PPA) : AssumeRATResult × PPA :=
  let size := clauseSize F index
  let rec go (i : Nat) (τ : PPA) : AssumeRATResult × PPA :=
    if hi : i < size then
      let lit := getLit F index ⟨i, hi⟩
      match σ.litValue lit with
      | Sum.inr true => ⟨.sat, τ⟩
      | Sum.inr false => go (i + 1) τ
      | Sum.inl l =>
        match τ.litValue? l with
        | some true => ⟨.sat, τ⟩
        | some false => go (i + 1) τ
        | none => go (i + 1) (τ.setLit (-l))
    else ⟨.updated, τ⟩
  termination_by (clauseSize F index) - i
  go 0 τ

theorem assumeRATClause.go_spec [LawfulFaC FC] {F : FC} {index : Fin (size F)} {σ : PS}
      {τ τ' : PPA} {r : AssumeRATResult}
      {i : Nat} (hi : i ≤ clauseSize F index) :
    (∀ {j : Nat} (hj : j < i), τ.toPropFun ⊓ (PropFun.substL (getLit F index ⟨j, lt_of_lt_of_le hj hi⟩).toPropFun σ)ᶜ ≤ τ') →
  assumeRATClause.go F index σ i τ = ⟨r, τ'⟩ →
    extended τ τ' 0 ∧
      (r = .sat → τ.toPropFun ≤ (PropFun.substL (toPropFunClause F index) σ)) ∧
      (r = .updated → τ.toPropFun ⊓ (PropFun.substL (toPropFunClause F index) σ)ᶜ ≤ τ') := by
  intro ih h_go
  rw [go] at h_go
  induction' h_diff : (clauseSize F index) - i with diff ih_diff generalizing τ
  · have : i = clauseSize F index := Nat.le_antisymm hi (Nat.le_of_sub_eq_zero h_diff)
    subst this
    simp at h_go
    rcases h_go with ⟨rfl, rfl⟩
    simp
  · have hi' : i < clauseSize F index := by sorry
    simp [hi'] at h_go
    stop
    match hlit : σ.litValue (getLit F index ⟨i, hi'⟩) with
    | Sum.inr true =>
      simp [hlit] at h_go
      rcases h_go with ⟨rfl, rfl⟩
      simp
      --refine entails_ext.mpr fun τ' hτ' => ?_
      have : getLit F index ⟨i, hi'⟩ ≤ toPropFunClause F index := by sorry
      have : toPropFunClause F index = toPropFunClause F index ⊔ getLit F index ⟨i, hi'⟩ := by
        apply le_antisymm
        · exact le_sup_left
        · exact sup_le (fun τ a => a) this
          done
        done
      rw [this]
      simp
      apply le_sup_of_le_right
      refine entails_ext.mpr fun τ' hτ' => ?_
      simp
      rw [LitVar.satisfies_iff]
      stop

      have := congrArg PSV.toPropFun hlit
      rw [litValue_eq_substL] at this
      simp at this
      done
    stop
    split at h_go
    injection h_go
    rename _ = b => h; subst h
    rename τ = _ => h; subst h
    simp [this] at ih_diff
    done
  stop
  by_cases h_size : clauseSize F index = 0
  · simp [h_size] at hi; subst hi
    rw [go]
    simp [h_size]
    rintro rfl rfl
    simp
  · replace h_size : clauseSize F index > 0 := Nat.pos_of_ne_zero h_size
    intro ih h_go
    induction' h_diff : (clauseSize F index) - i generalizing τ
    · have : i = clauseSize F index := Nat.le_antisymm hi (Nat.le_of_sub_eq_zero h_diff)
      subst this
      rw [go] at h_go
      simp at h_go
      rcases h_go with ⟨rfl, rfl⟩
      simp
    ·
      done

    done
  stop
  induction i generalizing τ
  · simp
    rw [go]

    done
  done

theorem assumeRATClause_spec [LawfulFaC FC] {F : FC} {index : Fin (size F)} {σ : PS} {τ τ' : PPA} {r : AssumeRATResult} :
  assumeRATClause F index σ τ = ⟨r, τ'⟩ →
    extended τ τ' 0 ∧
      (r = .sat → τ.toPropFun ≤ (PropFun.substL (toPropFunClause F index) σ)) ∧
      (r = .updated → τ.toPropFun ⊓ (PropFun.substL (toPropFunClause F index) σ)ᶜ ≤ τ') := by
  simp [assumeRATClause]
  apply assumeRATClause.go_spec
  · simp
  · exact Nat.zero_le (clauseSize F index)

def LawfulAssumeRAT (assume_fn : (F : FC) → (Fin (size F)) → PS → PPA → (AssumeRATResult × PPA)) : Prop :=
  ∀ {F : FC} {index : Fin (size F)} {σ : PS} {τ τ' : PPA} {r : AssumeRATResult},
    assume_fn F index σ τ = ⟨r, τ'⟩ →
    extended τ τ' 0 ∧
      (r = .sat → τ.toPropFun ≤ (PropFun.substL (toPropFunClause F index) σ)) ∧
      (r = .updated → τ.toPropFun ⊓ (PropFun.substL (toPropFunClause F index) σ)ᶜ ≤ τ')

inductive UPResult where
  | conflict
  | updated
  | satOrMult
  | err
  deriving Inhabited, DecidableEq

/-- Returns an updated PPA, and the result of the UP across the hints. -/
@[inline, always_inline]
def applyUPHints' (F : FC) (offset : Nat) (τ : PPA) (hints : Array Nat) : UPResult × PPA :=
  -- A re-implementation of hints.foldlM ..., except it uses an explicit
  -- index and is tail-recursive in its loop.
  let rec go (i : Nat) (τ : PPA) : UPResult × PPA :=
    if hi : i < hints.size then
      let hint := hints.get ⟨i, hi⟩
      if h_hint : hint < size F then
        if !(isDeleted F ⟨hint, h_hint⟩) then
          match unitProp F ⟨hint, h_hint⟩ τ with
          | .falsified => ⟨.conflict, τ⟩
          | .satisfied => ⟨.satOrMult, τ⟩
          | .multipleUnassignedLiterals => ⟨.satOrMult, τ⟩
          | .unit l => go (i + 1) (τ.setLitFor l offset)
        else
          ⟨.err, τ⟩     -- Hinted clause was deleted
      else
        ⟨.err, τ⟩       -- Hint was out of bounds
    else ⟨.updated, τ⟩
  termination_by hints.size - i
  go 0 τ

def LawfulApplyUPHints (hints_fn : FC → Nat → PPA → Array Nat → (UPResult × PPA)) : Prop :=
  ∀ {F : FC} {offset : Nat} {hints : Array Nat} {τ τ' : PPA} {res : UPResult},
    hints_fn F offset τ hints = ⟨res, τ'⟩ →
      extended τ τ' offset
      ∧ (res = .conflict → toPropFun F ⊓ τ = ⊥)
      ∧ (res = .updated → toPropFun F ⊓ τ ≤ τ')

inductive LineResult where
  | lineOk
  | lineOkAndDerivedEmptyClause
  | err

open Except in
@[inline, always_inline]
def checkLine (F : FC) (τ : PPA) (σ : PS) (line : SRAdditionLine) : LineResult × FC × PPA × PS :=
  let ⟨C, wL, wM, upHints, ratHintIndexes, ratHints, _, _⟩ := line
  -- dbg_trace s!"{C}, {wL}, {wM}"
  -- dbg_trace s!"{upHints}, {ratHintIndexes}, {ratHints}"
  match assumeNegatedClauseFor τ.reset C (ratHints.size + 1) with
  | .error _ =>
    -- dbg_trace s!"Assumed negation of clause had error"
    ⟨.err, F, τ, σ⟩
  | ok τ =>
    -- dbg_trace s!"Assumed negation of clause succeeded"
    -- Evaluate the UP hints, with "# of RAT hints" as the offset
    match applyUPHints' F (ratHints.size + 1) τ upHints with
    | ⟨.satOrMult, τ⟩ => ⟨.err, F, τ, σ⟩
    | ⟨.err, τ⟩ => ⟨.err, F, τ, σ⟩
    | ⟨.conflict, τ⟩ =>
      -- dbg_trace s!"Applying UP hints found contradiction before RAT"
      if C.size = 0 then
        ⟨.lineOkAndDerivedEmptyClause, F, τ, σ⟩ -- If the clause is empty, we have a successful contradiction proof
      else
        ⟨.ok ⟨F.add C, τ, σ⟩

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
/-
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
-/

end SR
