/-

Persistent partial assignments and substitutions.

Resizable arrays that can be ``cleared'' in O(1) time by bumping a generation
number. Each cell in the array stores a generation number that determines if the
cell is set (i.e. that it is above the data structure's generation number).
Used to implement partial assignments and substitutions by assuming that all
variables are unset (PPA) or set to themselves (PS) at initialization.

Authors: Cayden Codel, Wojciech Nawrocki, James Gallicchio
Carnegie Mellon University
-/

import LeanSAT.Data.Cnf
import LeanSAT.Data.ICnf
import Mathlib.Data.Nat.Basic

import LeanSAT.Model.Subst
import LeanSAT.Model.PropFun

import LeanSAT.Upstream.ToStd
import LeanSAT.Upstream.ToMathlib

import Experiments.ProofChecking.PPA

open LeanSAT LeanSAT.Model Nat
open LitVar ILit IVar LawfulLitVar
open PropFun

/- The value contained in the partial substitution. Values can either be booleans
   (in LRAT/LPR, they are only booleans), or set to other variables, with sign.

  When set to other variables, the boolean indicates the sign (true is positive),
  and the ILit refers to the underlying literal this variable is set to.     -/
inductive PSVal where
  | tr : PSVal
  | fls : PSVal
  | lit (l : ILit) : PSVal

attribute [match_pattern] PSVal

/-- A persistent partial assignment of truth values to propositional variables.

If used linearly, it is an efficient way of clearing out partial assignments
when doing proof checking, tautology checking, or unit propagation. -/
structure PS where
  assignment : Array (Nat × PSVal)
  /-- The generation counter is used to avoid clearing the assignment array.
  Instead, we just bump the counter and interpret values in the array
  below the counter as unassigned. -/
  generation : PNat
  /-- The maximum absolute value of any entry in `assignments`. -/
  maxGen : Nat
  le_maxGen : ∀ i ∈ assignment.data, i.1 ≤ maxGen

/-! ## Reading values from the PS -/

@[reducible] abbrev PSubst := (IVar → PropForm IVar)

namespace PSVal

protected def negate : PSVal → PSVal
  | .tr => .fls
  | .fls => .tr
  | .lit l => .lit (LitVar.negate l)

@[simp] theorem negate_tr : PSVal.negate .tr = .fls := by rfl
@[simp] theorem negate_fls : PSVal.negate .fls = .tr := by rfl
@[simp] theorem negate_lit (l : ILit) : PSVal.negate (.lit l) = .lit (LitVar.negate l) := by rfl

@[simp] theorem negate_negate : PSVal.negate ∘ PSVal.negate = id := by
  ext r; cases r <;> simp [PSVal.negate]

@[simp] theorem negate_negate' (r : PSVal) :
    r.negate.negate = r := by
  cases r <;> simp [PSVal.negate]

theorem negate_eq_iff_eq_negate (r₁ r₂ : PSVal) :
    r₁.negate = r₂ ↔ r₁ = r₂.negate := by
  cases r₁ <;> cases r₂ <;> simp [PSVal.negate]; aesop

@[simp] def isBool : PSVal →  Bool
  | .tr => true
  | .fls => true
  | _ => false

@[simp] def isLit : PSVal → Bool
  | .lit _ => true
  | _ => false

@[simp] def getVar : PSVal → IVar
  | .tr => 1  -- Useless return value for non-.lit values
  | .fls => 1
  | .lit l => toVar l

@[simp] def getLit : PSVal → ILit
  | .tr => mkPos ⟨1, succ_pos _⟩
  | .fls => mkNeg ⟨1, succ_pos _⟩
  | .lit l => l

@[simp] def sign : PSVal → Bool
  | .tr => true
  | .fls => false
  | .lit l => polarity l

def toPropForm : PSVal → PropForm IVar
  | .tr => .tr
  | .fls => .fls
  | .lit l => LitVar.toPropForm l

def toPropFun : PSVal → PropFun IVar
  | .tr => ⊤
  | .fls => ⊥
  | .lit l => LitVar.toPropFun l

@[simp] theorem tr_toPropForm : PSVal.toPropForm .tr = .tr := by rfl
@[simp] theorem fls_toPropForm : PSVal.toPropForm .fls = .fls := by rfl
@[simp] theorem lit_toPropForm (l : ILit) : PSVal.toPropForm (.lit l) = LitVar.toPropForm l := by rfl

@[simp] theorem tr_toPropFun : PSVal.toPropFun .tr = ⊤ := by rfl
@[simp] theorem fls_toPropFun : PSVal.toPropFun .fls = ⊥ := by rfl
@[simp] theorem lit_toPropFun (l : ILit) : PSVal.toPropFun (.lit l) = LitVar.toPropFun l := by rfl

@[simp] theorem toPropFun_negate (r : PSVal) :
    PSVal.toPropFun r.negate = (PSVal.toPropFun r)ᶜ := by
  cases r <;> simp [PSVal.toPropFun, PSVal.negate]

instance : Coe PSVal (PropForm IVar) := ⟨toPropForm⟩
instance : Coe PSVal (PropFun IVar) := ⟨toPropFun⟩

instance : ToString PSVal where
  toString v :=
    match v with
    | .tr => "t"
    | .fls => "f"
    | .lit l => s!"{l}"

end PSVal

/-! # PS -/

namespace PS

@[reducible] def size (σ : PS) : Nat := σ.assignment.size

instance : ToString PS where
  toString σ := String.intercalate " ∧ "
    (σ.assignment.foldl (init := []) (f := fun acc a => s!"{a}" :: acc))

/-! # varValue -/

def varValue (σ : PS) (v : IVar) : PSVal :=
  match σ.assignment.get? v.index with
  | none => PSVal.lit (mkPos v)
  | some ⟨n, val⟩ =>
    if σ.generation ≤ n then val
    else PSVal.lit (mkPos v)

@[inline] def litValue (σ : PS) (l : ILit) : PSVal :=
  if polarity l then
    varValue σ (toVar l)
  else
    PSVal.negate (varValue σ (toVar l))

-- TODO: Better name
def idxToSubst (σ : PS) (S : PSubst) (i : Fin σ.size) : PSubst :=
  fun v =>
    if v.index = i.val then σ.varValue v
    else S v

def toSubst (σ : PS) : PSubst :=
  Fin.foldl σ.size (init := .var) (idxToSubst σ)

instance : Coe PS PSubst := ⟨toSubst⟩

theorem idxToSubst_comm (σ : PS) :
  ∀ (S : PSubst) (idx₁ idx₂ : Fin σ.size),
    (idxToSubst σ) ((idxToSubst σ) S idx₁) idx₂ =
    (idxToSubst σ) ((idxToSubst σ) S idx₂) idx₁ := by
  intro S idx₁ idx₂
  unfold idxToSubst
  apply funext
  intro v
  by_cases hidx : idx₁.val = idx₂.val
  <;> by_cases hv₁ : v.index = idx₁.val
  <;> by_cases hv₂ : v.index = idx₂.val
  <;> try simp [hv₁, hv₂, hidx]

theorem toSubst_of_comm (σ : PS) {v : IVar} (hv : v.index < σ.size) :
    ∃ S, σ.toSubst = idxToSubst σ S ⟨v.index, hv⟩ :=
  Fin.foldl_of_comm σ.size (idxToSubst σ) .var ⟨v.index, hv⟩ (idxToSubst_comm σ)

/-
theorem toSubst_of_ge_size {σ : PS} {v : IVar} (hv : σ.size ≤ v.index) :
    σ.toSubst v = .var v := by
  rw [toSubst]
  let s := σ.size

  generalize h : s = s₂

  apply (· = .var v) |> Fin.foldl_induction σ.size
  induction σ.size with
  | zero =>

    done
  --simp [toSubst, idxToSubst, hv]k
  done
--σ.size (idxToSubst σ) .var ⟨v.index, hv⟩ (idxToSubst_comm σ) -/

instance : ToString PS where
  toString σ := String.intercalate " ∧ "
    (σ.assignment.foldl (init := []) (f := fun acc a =>
      match a.2 with
        | .tr => s!"{a.1}" :: acc
        | .fls => s!"-{a.1}" :: acc
        | .lit l => s!"<{l}>" :: acc))

@[simp]
theorem litValue_negate (σ : PS) (l : ILit) :
    (σ.litValue (-l)) = PSVal.negate (σ.litValue l) := by
  cases hpol : polarity l <;> simp [hpol, litValue]

theorem negate_varValue_eq_iff {σ : PS} {v : IVar} {val : PSVal} :
    PSVal.negate (σ.varValue v) = val ↔ σ.varValue v = PSVal.negate val :=
  PSVal.negate_eq_iff_eq_negate (varValue σ v) val

theorem litValue_eq_varValue_true {l : ILit} :
    polarity l = true → ∀ (σ : PS), σ.litValue l = σ.varValue (toVar l) := by
  intro hl; simp [hl, litValue]

theorem litValue_eq_varValue_false {l : ILit} :
    polarity l = false → ∀ (σ : PS), σ.litValue l = PSVal.negate (σ.varValue (toVar l)) := by
  intro hl; simp [hl, litValue]

theorem lt_size_of_varValue_ne {σ : PS} {v : IVar} :
    σ.varValue v ≠ .lit (mkPos v) → v.index < σ.size := by
  intro hv
  simp [varValue, Array.get?] at hv
  rcases Nat.lt_trichotomy v.index σ.size with (hlt | heq | hgt)
  · exact hlt
  · simp [heq] at hv
  · simp [Nat.lt_asymm hgt] at hv

theorem lt_size_of_varValue_tr {σ : PS} {v : IVar} :
    σ.varValue v = .tr → v.index < σ.size := by
  intro hσ
  apply lt_size_of_varValue_ne
  simp [hσ]

theorem lt_size_of_varValue_fls {σ : PS} {v : IVar} :
    σ.varValue v = .fls → v.index < σ.size := by
  intro hσ
  apply lt_size_of_varValue_ne
  simp [hσ]

theorem lt_size_of_litValue_tr {σ : PS} {l : ILit} :
    σ.litValue l = .tr → l.index < σ.size := by
  intro hσ
  by_cases hpol : polarity l
  <;> simp [hpol, litValue] at hσ
  <;> try apply lt_size_of_varValue_tr hσ
  rw [negate_varValue_eq_iff] at hσ
  exact lt_size_of_varValue_fls hσ

theorem lt_size_of_litValue_fls {σ : PS} {l : ILit} :
    σ.litValue l = .fls → l.index < σ.size := by
  intro hσ
  by_cases hpol : polarity l
  <;> simp [hpol, litValue] at hσ
  <;> try apply lt_size_of_varValue_fls hσ
  rw [negate_varValue_eq_iff] at hσ
  exact lt_size_of_varValue_tr hσ

theorem varValue_eq_toSubst {σ : PS} {v : IVar} :
    v.index < σ.size → σ.varValue v = σ.toSubst v := by
  intro hv
  have ⟨_, h_toSubst⟩ := (Fin.foldl_of_comm σ.size (idxToSubst σ) .var ⟨v.index, hv⟩ (idxToSubst_comm σ))
  simp [toSubst, h_toSubst, idxToSubst]

theorem varValue_eq_substL {σ : PS} {v : IVar} : v.index < σ.size →
    σ.varValue v = PropFun.substL ⟦v⟧ σ.toSubst := by
  intro hv
  have ⟨S, h_toSubst⟩ := (Fin.foldl_of_comm σ.size (idxToSubst σ) .var ⟨v.index, hv⟩ (idxToSubst_comm σ))
  simp [PropFun.ext_iff, satisfies_substL, PropAssignment.subst]
  intro τ
  rw [toSubst, h_toSubst, idxToSubst]
  simp [hv]
  cases hσ : σ.varValue v
  <;> simp [PSVal.toPropForm, PSVal.toPropFun]

theorem litValue_eq_substL {σ : PS} {l : ILit} :
    l.index < σ.size → σ.litValue l = PropFun.substL ⟦l⟧ σ.toSubst := by
  intro hl
  by_cases hpol : polarity l
  <;> simp [hpol, litValue, LitVar.toPropFun, varValue_eq_substL hl]

theorem litValue_eq_substL' {σ : PS} {l : ILit} :
    l.index < σ.size → σ.litValue l = PropFun.substL (LitVar.toPropFun l) σ.toSubst := by
  intro hl
  by_cases hpol : polarity l
  <;> simp [hpol, litValue, LitVar.toPropFun, varValue_eq_substL hl]

/-! # setLit -/

-- Cayden TODO: How to make setF more efficient when the value needs to be a cell?
-- Can an efficient implementation do this linearly? Ow will run out of memory?
-- One idea is to use a .setF' that takes a function : (Option α → α) instead of value v : α
-- That way, if the cell exists, its value can be mapped

-- This is a more efficient version
/-
def setLit (σ : PS) (l : ILit) : PS := { τ with
  assignment :=
    if hidx : l.index < τ.size then
      σ.assignment.set ⟨l.index, hidx⟩ ((σ.get ⟨l.index, hidx⟩).setLit l σ.generation)
    else
      σ.assignment.setF l.index (PSCell.mkEmptyCell.setLit l σ.generation) PSCell.mkEmptyCell
  maxGen := max τ.maxGen σ.generation
}
-/

theorem setVar_le_maxGen (σ : PS) (i : Nat) (p : Nat × PSVal) :
    ∀ cell ∈ (σ.assignment.setF i p ⟨0, .tr⟩).data, cell.1 ≤ max σ.maxGen p.1 := by
  intro cell hcell
  sorry
  done

-- This is a more functional version
/-- Set the given literal to `true` for the current generation in the PS. -/
def setLit (σ : PS) (l : ILit) : PS :=
  let val : PSVal := if polarity l then .tr else .fls
  { σ with
    assignment := σ.assignment.setF l.index ⟨σ.generation, val⟩ ⟨0, .tr⟩
    maxGen := max σ.maxGen σ.generation
    le_maxGen := setVar_le_maxGen σ l.index ⟨σ.generation, val⟩
  }

def setVarToLit (σ : PS) (v : IVar) (l : ILit) : PS := { σ with
  assignment := σ.assignment.setF v.index ⟨σ.generation, .lit l⟩ ⟨0, .tr⟩
  maxGen := max σ.maxGen σ.generation
  le_maxGen := setVar_le_maxGen σ v.index ⟨σ.generation, .lit l⟩
}

def setVars (σ : PS) (A : Array (IVar × ILit)) : PS :=
  A.foldl (init := σ) (fun σ ⟨v, l⟩ => σ.setVarToLit v l)

def setLits (σ : PS) (A : Array ILit) : PS :=
  A.foldl setLit σ

/- Lemmas -/

@[simp]
theorem setLit_size (σ : PS) (l : ILit) : (σ.setLit l).size = max σ.size (l.index + 1) := by
  simp [setLit, size]

@[simp]
theorem litValue_setLit_pos (σ : PS) (l : ILit) : (σ.setLit l).litValue l = .tr := by
  by_cases hpol : polarity l
  <;> by_cases hl : l.index < σ.size
  <;> simp [litValue, varValue, size, setLit, hpol, hl, PSVal.negate, Array.getElem_setF]

/-
theorem litValue_setLit_neg (σ : PS) {l₁ l₂ : ILit} :
    l₁ ≠ l₂ → (σ.setLit l₁).litValue l₂ = σ.litValue l₂ := by
  intro hne
  by_cases hpol₁ : polarity l₁
  · by_cases hpol₂ : polarity l₂
    · simp [hpol₁, hpol₂, litValue]
      sorry
    sorry
  /-by_cases hpol : polarity l₂
  · simp [litValue, hpol, setLit, Array.size_setF, -Array.get_eq_getElem]
    by_cases hl₂ : l₂.index < τ.size
    · rw [size] at hl₂
      have : l₂.index < σ.assignment.size ∨ l₂.index < l₁.index + 1 := Or.inl hl₂
      simp [hl₂, this, -Array.get_eq_getElem]
      by_cases hpol₁ : polarity l₁
      · rw [Array.getElem_setF' σ.assignment l₁.index ⟨σ.generation, PSVal.tr⟩ PSCell.mkEmptyCell]

      done
    done
  --by_cases hpol : polarity l₂
  --<;> by_cases hl₂ : l₂.index < τ.size
  --<;> simp [litValue, setLit, hpol,
  --    hl₂, Or.inl hl₂, Array.size_setF, PSCell.varValue?, PSVal.negate] -/
  sorry
  done -/

/-! # New -/

/-- Initialize to an empty partial assignment,
supporting variables in the range `[1, maxVar]`.

The assignment will resize dynamically if it's used with
a variable above the initial `maxVar`. -/

def new (n : Nat) : PS where
  assignment := Array.mkArray n ⟨0, .tr⟩
  generation := ⟨1, Nat.one_pos⟩
  maxGen := 0
  le_maxGen := by simp_all [List.mem_replicate]

/-
theorem new_WF (n : Nat) : (new n).WF := by
  simp [new]
  constructor
  · intro i
    sorry
  · simp only [gt_iff_lt, zero_lt_one] -/

/-! # Reset -/

/-- Reset the assignment to an empty one. -/
def reset (σ : PS) : PS :=
  { σ with generation := ⟨σ.maxGen + 1, Nat.succ_pos _⟩ }

/-! # Bump -/

/-- Clear all temporary assignments at the current generation. -/
def bump (σ : PS) : PS :=
  { σ with generation := σ.generation + 1 }

section monadic

/-! # Unit propagation -/

/-

Cayden note 1/8: In SR checking, the substitution witness σ is provided in the proof line,
  and then never modified. Instead, a partial assignment α is produced and modified.

To save memory and time, the substitution and partial assignments use the "generation bumping" strategy
to clear out their computations after each proof line/group of hints.

Since unit propagation is never done/evaluated against a substitution, proving its correctness is moot.
But! We do need to compute a clause's reduction under a substitution, and so we need a theory for that.
We also need to think about an efficient way to either compute a reduction OR make reduction and evaluation
against a partial assignment happen in the same step (possibly using another "PPA" structure off to the side
to record which literals have been seen in the reduction, so a tautology can be detected)

-/
/-

inductive UPResult where
  | falsified
  | satisfied
  | unit (l : ILit) (σ : PS) -- Updated substitution and unit literal l
  | multipleUnassignedLiterals

inductive UPDone where
  | satisfied
  | multipleUnassignedLiterals

abbrev UPBox := Except UPDone (Option ILit)

open Except UPResult UPDone PPA

def sevalUP (σ : PS) (unit? : Option ILit) (l : ILit) : UPBox :=
  match σ.litValue l with
  | .tr => error .satisfied
  | .fls => ok unit?
  | .lit lit =>
    match unit? with
    | none => ok lit
    | some u =>
      if u = lit then ok unit?
      -- Since σ is a substitution, tautology could occur
      else if u = -lit then error .satisfied
      else error .multipleUnassignedLiterals

def foldUP (σ : PS) (C : IClause) := C.foldlM (sevalUP σ) none

def unitProp (σ : PS) (C : IClause) : UPResult :=
  match foldUP σ C with
  | ok none => .falsified
  | ok (some lit) => .unit lit (σ.setLit lit)
  | error .satisfied => .satisfied
  | error .multipleUnassignedLiterals => .multipleUnassignedLiterals

def UP_motive_fn (σ : PS) (C : IClause) : ℕ → Option ILit → Prop
  | idx, none => ∀ ⦃i : Fin C.size⦄, i < idx → σ.litValue C[i] = .fls
  | idx, some lit => ∃ (i : Fin C.size), i < idx ∧ σ.litValue C[i] = .lit lit ∧
      (∀ ⦃j : Fin C.size⦄, j < idx → j ≠ i → (σ.litValue C[j] = .fls ∨ σ.litValue C[j] = .lit lit))

theorem SatisfiesM_UP (σ : PS) (C : IClause) :
    SatisfiesM (fun
      | none => ∀ l ∈ C.data, σ.litValue l = .fls
      | some lit => ∃ (l : ILit), l ∈ C.data ∧ σ.litValue l = .lit lit ∧
          (∀ l' ∈ C.data, l' ≠ l → (σ.litValue l' = .fls ∨ σ.litValue l' = .lit lit))) (foldUP σ C) := by
  have := C.SatisfiesM_foldlM (init := (none : Option ILit)) (f := sevalUP σ)
    (motive := UP_motive_fn σ C)
    (h0 := by simp [UP_motive_fn])
    (hf := by
      unfold UP_motive_fn
      simp only [SatisfiesM_Except_eq, getElem_fin]
      -- Cayden question: is the proof more compact if I use pattern-matching with intro?
      intro i box ih
      intro
      | none, hbox =>
        intro j hj
        unfold sevalUP at hbox
        match hσ : σ.litValue C[i.val] with
        | .tr => simp_rw [hσ] at hbox
        | .fls =>
          simp_rw [hσ, ok.injEq] at hbox; subst hbox
          rcases eq_or_lt_of_le (le_of_lt_succ hj) with (hj | hj)
          · rw [Fin.ext hj]; exact hσ
          · exact ih hj
        | .lit lit =>
          simp [hσ] at hbox
          match box with
          | none => simp at hbox
          | some u =>
            rcases eq_trichotomy u lit with (rfl | rfl | hvar)
            · simp at hbox
            · simp at hbox
            · simp [ne_of_toVar_ne hvar, ne_of_toVar_ne ((toVar_negate lit).symm ▸ hvar)] at hbox
      | some u, hbox =>
        rename ILit => lit
        unfold sevalUP at hbox
        match hσ : σ.litValue C[i.val] with
        | .tr => simp_rw [hσ] at hbox
        | .fls =>
          simp_rw [hσ, ok.injEq] at hbox; subst hbox
          rcases ih with ⟨idx, hidx_lt, hidxσ, hidx_fls⟩
          use idx, lt_succ_of_lt hidx_lt, hidxσ
          intro j hj
          rcases lt_or_eq_of_le (le_of_lt_succ hj) with (h | h)
          · exact hidx_fls h
          · replace h := Fin.ext h; subst h; intro _; exact Or.inl hσ
        | .lit lit' =>
          simp [hσ] at hbox
          match box with
          | none =>
            simp at hbox; subst hbox
            have : C[i.val] ∈ C.data := Array.getElem_mem_data C i.isLt
            use i, lt_succ_self _, hσ
            intro j hj
            rcases lt_or_eq_of_le (le_of_lt_succ hj) with (h | h)
            · intro _; exact Or.inl (ih h)
            · replace h := Fin.ext h; subst h; intro hcon; contradiction
          | some u =>
            rcases eq_trichotomy u lit' with (rfl | rfl | hvar)
            · simp at hbox; subst hbox
              rcases ih with ⟨idx, hidx_lt, hidxσ, hidx_fls⟩
              use idx, lt_succ_of_lt hidx_lt, hidxσ
              intro j hj
              rcases lt_or_eq_of_le (le_of_lt_succ hj) with (h | h)
              · exact hidx_fls h
              · replace h := Fin.ext h; subst h; intro _; exact Or.inr hσ
            · simp at hbox
            · simp [ne_of_toVar_ne hvar, ne_of_toVar_ne ((toVar_negate lit').symm ▸ hvar)] at hbox)
  apply SatisfiesM.imp this
  intro
  | none =>
    intro h l hl
    rcases Array.mem_data_iff_exists_fin.mp hl with ⟨i, rfl⟩
    exact h i.isLt
  | some lit =>
    simp [UP_motive_fn]
    intro i hi ih
    use C[i.val], Array.getElem_mem_data C i.isLt, hi
    intro l hl₁ hl₂
    rcases Array.mem_data_iff_exists_fin.mp hl₁ with ⟨j, rfl⟩
    apply ih
    exact ne_of_apply_ne (C[·]) hl₂

theorem contradiction_of_UP_falsified {σ : PS} {C : IClause} :
    σ.unitProp C = .falsified → (C.toPropFun).substL σ.toSubst ≤ ⊥ := by
  unfold unitProp
  intro h_falsified
  split at h_falsified <;> try simp at h_falsified
  clear h_falsified
  rename (foldUP σ C = ok none) => h
  refine entails_ext.mpr fun τ hτ => ?_
  rw [satisfies_substL] at hτ
  have ⟨lit, hlit, hτlit⟩ := Clause.satisfies_iff.mp hτ
  rw [← Array.mem_data] at hlit
  have := SatisfiesM_Except_eq.mp (SatisfiesM_UP σ C) none h lit hlit
  clear h hτ
  replace hτlit := satisfies_iff.mp hτlit
  cases hpol : polarity lit
  <;> simp [hpol, PropAssignment.subst] at hτlit
  · rw [litValue_eq_varValue_neg hpol, PSVal.negate_rhs_eq_lhs_negate, PSVal.negate,
          varValue_tr_iff, substL_distrib] at this
    rw [this] at hτlit
    contradiction
  · rw [litValue_eq_varValue_pos hpol, varValue_fls_iff, substL_distrib] at this
    rw [this] at hτlit
    exact hτlit

theorem extended_of_UP_unit {σ σ' : PS} {C : IClause} {l : ILit} :
    σ.unitProp C = .unit l σ' →
      (C.toPropFun).substL σ.toSubst ≤ l.toPropFun ∧
      (∃ lit ∈ C.data, σ.litValue lit = .lit l ∧ σ'.litValue l = .tr) := by
      -- Cayden question: how to express this in an abstract way? Perhaps with a bind (l.bind σ) or as a (. ∘ .) of two subs
  unfold unitProp
  intro h_unit
  split at h_unit <;> try simp at h_unit
  --clear h_unit
  rename ILit => lit
  rename (foldUP σ C = ok (some lit)) => h
  rcases h_unit with ⟨rfl, rfl⟩
  have hlv := SatisfiesM_Except_eq.mp (SatisfiesM_UP σ C) (some lit) h
  clear h
  rcases hlv with ⟨l, hl_mem, hσl, ih⟩
  constructor
  · refine entails_ext.mpr fun τ hτ => ?_
    rw [satisfies_substL] at hτ
    by_cases heq : l = lit
    · subst heq
      rw [Clause.satisfies_iff] at hτ; rcases hτ with ⟨l', hl'_mem, hl'⟩
      rw [← satisfies_substL] at hl'
      sorry -- Proof got stuck here. And we may not need unit propagaion after all
      done
    · sorry
      done
    done
  · exact ⟨l, hl_mem, hσl, litValue_setLit_pos _ _⟩
  done
  -/

/-! # Reduction -/

inductive ReductionResult where
  | satisfied
  | reduced
  | notReduced

open Except ReductionResult

/- Reduction without tautology checking -/

def seval (σ : PS) (r : Bool) (l : ILit) : Except Unit Bool :=
  match σ.litValue l with
  | .tr => error ()
  | .fls => ok true
  | .lit lit => ok (r || l != lit)

-- CC: Helpful?
theorem litValue_tr_iff_seval_satisfied {σ : PS} {r : Bool} {l : ILit} :
    (σ.litValue l = .tr) ↔ (σ.seval r l = error ()) := by
  simp [seval]; aesop

def reduce (σ : PS) (C : IClause) : ReductionResult :=
  match C.foldlM (seval σ) false with
  | ok true => .reduced
  | ok false => .notReduced
  | error _ => .satisfied

theorem reduce_satisfied_iff {σ : PS} {C : IClause} :
    σ.reduce C = .satisfied ↔ (C.toPropFun).substL σ.toSubst = ⊤ := by
  have ⟨C⟩ := C
  rw [reduce, Array.foldlM_eq_foldlM_data]
  --generalize hb : false = b
  induction C with
  | nil => simp [reduce, pure, Except.pure]
  | cons l ls ih =>
    match hσ : σ.litValue l with
    | .tr => simp [← litValue_eq_substL' (lt_size_of_litValue_tr hσ), hσ, seval]; rfl
    | .fls =>
      simp [← litValue_eq_substL' (lt_size_of_litValue_fls hσ), hσ, seval]
      --TODO: need to generalize across input
      stop
      simp [seval, hσ, LitVar.toPropFun]
    | .lit lit =>
      by_cases hls : l = lit
      · subst hls
        simp [seval, hσ]
        constructor
        · intro h; simp [ih.mp h]
        · sorry
          done
      · stop
        done

theorem reduce_notReduced_iff {σ : PS} {C : IClause} :
    σ.reduce C = .notReduced ↔ (C.toPropFun).substL σ.toSubst = ↑C := by
  sorry
  done

theorem reduce_reduced {σ : PS} {C : IClause} :
    σ.reduce C = .reduced ↔
      ((C.toPropFun).substL σ.toSubst ≠ ⊤ ∧ (C.toPropFun).substL σ.toSubst ≠ ⊥) := by
  sorry
  done

end monadic

end PS
