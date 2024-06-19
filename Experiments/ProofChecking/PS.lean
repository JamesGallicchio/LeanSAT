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

import LeanColls
open LeanColls

open LeanSAT LeanSAT.Model Nat
open LitVar ILit IVar LawfulLitVar
open PropFun

/-- A persistent partial assignment of truth values to propositional variables.

If used linearly, it is an efficient way of clearing out partial assignments
when doing proof checking, tautology checking, or unit propagation. -/
structure PS where
  gens : Array Nat
  mappings : Array Nat
  /-- The generation counter is used to avoid clearing the assignment array.
  Instead, we just bump the counter and interpret values in the array
  below the counter as unassigned. -/
  generation : PNat
  /-- The maximum absolute value of any entry in `assignments`. -/
  maxGen : Nat
  sizes_eq : gens.size = mappings.size
  le_maxGen : ∀ i ∈ gens.data, i ≤ maxGen

@[reducible] abbrev PSubst := (IVar → PropForm IVar)

namespace PS

@[reducible] def size (σ : PS) : Nat := σ.gens.size

abbrev PSV := ILit ⊕ Bool

namespace PSV

def toPropForm : PSV → PropForm IVar
  | Sum.inl l => LitVar.toPropForm l
  | Sum.inr true => .tr
  | Sum.inr false => .fls

def toPropFun : PSV → PropFun IVar
  | Sum.inl l => LitVar.toPropFun l
  | Sum.inr true => ⊤
  | Sum.inr false => ⊥

def negate : PSV → PSV
  | Sum.inl l => Sum.inl (LitVar.negate l)
  | Sum.inr b => Sum.inr !b

instance : Coe IVar PSV := ⟨Sum.inl ∘ mkPos⟩
instance : Coe ILit PSV := ⟨Sum.inl⟩
instance : Coe Bool PSV := ⟨Sum.inr⟩

instance : Coe PSV (PropForm IVar) := ⟨toPropForm⟩
instance : Coe PSV (PropFun IVar) := ⟨toPropFun⟩

@[simp] theorem toPropFun_lit (l : ILit) : toPropFun (Sum.inl l) = LitVar.toPropFun l := rfl
@[simp] theorem toPropFun_true : toPropFun (Sum.inr true) = ⊤ := rfl
@[simp] theorem toPropFun_false : toPropFun (Sum.inr false) = ⊥ := rfl

-- CC: Was originally (Int.natAbs l.val) * 2, but made proofs hard
--     See if this is slower?
def toMapped' (l : ILit) : Nat :=
  if polarity l then
    (Int.natAbs l.val) * 2
  else
    (Int.natAbs l.val) * 2 + 1

def toMapped : PSV → Nat
  | Sum.inl l => toMapped' l
  | Sum.inr true => 0
  | Sum.inr false => 1

def fromMapped (n : Nat) : PSV :=
  match n with
  | 0 => Sum.inr true
  | 1 => Sum.inr false
  | n + 2 =>
    if n % 2 = 0 then
      Sum.inl <| mkPos ⟨n / 2 + 1, Nat.succ_pos _⟩
    else
      Sum.inl <| mkNeg ⟨n / 2 + 1, Nat.succ_pos _⟩

#check Int.natAbs_ofNat
#check Int.cast_div
#check Int.cast_div_charZero

private theorem exists_double {n : Nat} : n % 2 = 0 → ∃ m, n = 2 * m := by
  intro h
  use n / 2
  induction n with
  | zero => simp
  | succ n ih =>
    sorry
    done
  done
  --rw [Nat.mod_eq_of_lt (Nat.succ_pos _)] at h
  --rw [Nat.div_eq_of_lt (Nat.succ_pos _)] at h
  --exact ⟨n / 2, h⟩

@[simp]
theorem toMapped_fromMapped_id (n : Nat) : toMapped (fromMapped n) = n := by
  match n with
  | 0 => rfl
  | 1 => rfl
  | n + 2 =>
    by_cases hn : n % 2 = 0
    · rcases exists_double hn with ⟨m, rfl⟩
      simp [fromMapped, toMapped, toMapped', hn]
      simp [mkPos]
      stop
      rw [← Int.cast_one] --, ← Int.cast_add m 1]
      simp
      --have : (n : ℤ) / 2 + 1 = ↑(n / (2 : Nat) + (1 : Nat)) := rfl
      --rw [this, Int.natAbs_ofNat, add_mul]
      --simp

      --rw [mul_div_right, mul_comm]
      --trivial
      done
    · stop
    done

@[simp]
theorem fromMapped_toMapped_id (val : PSV) : fromMapped (toMapped val) = val := by
  match val with
  | Sum.inr true => rfl
  | Sum.inr false => rfl
  | Sum.inl l =>
    simp [fromMapped, toMapped, toMapped']
    by_cases hpol : polarity l
    <;> simp [hpol]
    stop
    done

-- CC: Proof of id, or inverses

instance : Coe PSV Nat := ⟨toMapped⟩
instance : Coe Nat PSV := ⟨fromMapped⟩

theorem negate_ILit (l : ILit) : Sum.inl (-l) = negate (Sum.inl l) := rfl

theorem negate_eq_iff_eq_negate {val₁ val₂ : PSV} :
    negate val₁ = val₂ ↔ val₁ = negate val₂ := by
  cases val₁; cases val₂ <;> simp [negate]
  · exact neg_eq_iff_eq_neg
  · simp [negate]; aesop

@[simp]
theorem negate_negate {val : PSV} :
    negate (negate val) = val := by
  cases val <;> simp [negate]

@[simp]
theorem toPropFun_negate {val : PSV} :
    toPropFun (negate val) = (toPropFun val)ᶜ := by
  cases val <;> simp [toPropFun, negate]
  rename Bool => b
  cases b <;> simp

/-
@[simp]
theorem toPropForm_negate {val : PSV} :
    toPropForm (negate val) = PropForm.neg (toPropForm val) := by
  cases val <;> simp [toPropForm, negate]
  · rename _ => l
    simp [LitVar.toPropForm]
    by_cases hpol : polarity l
    · simp [hpol]
      done
    · simp at hpol
      rw [hpol]
      conv => lhs; simp
      conv => rhs; simp [PropForm.neg]
      simp only [↓reduceIte]
      --simp at hpol ⊢
      --simp [LitVar.toPropForm, hpol]
      done
    rw [LitVar.toPropForm]
    done
  · rename Bool => b
    cases b <;> simp -/

end PSV

open PSV

instance : ToString PS where
  toString σ := String.intercalate ", "
    (Fin.foldl σ.gens.size (fun str idx =>
      if σ.gens.get! idx ≥ σ.generation then
        str ++ [s!"({idx}: {σ.gens.get! idx}, {σ.mappings.get! idx})"]
      else
        str) [])

/-! # varValue -/

-- CC: This is used for the model of the substitution, but for performing
--     reduction, it should be faster to case on the value of the array
--     directly (or think about inlining)
@[inline, always_inline]
def varValue (σ : PS) (v : IVar) : PSV :=
  match σ.gens.get? v.index with
  | none => Sum.inl (mkPos v)
  | some gen =>
    if gen ≥ σ.generation then
      match σ.mappings.get? v.index with
      | none => Sum.inl (mkPos v) -- Technically, dead branch
      | some n => n
    else
      Sum.inl (mkPos v)

@[inline, always_inline]
def litValue (σ : PS) (l : ILit) : ILit ⊕ Bool :=
  if polarity l then
    varValue σ (toVar l)
  else
    negate (varValue σ (toVar l))

def idxToSubst (σ : PS) (S : PSubst) (i : Fin σ.size) : PSubst :=
  fun v =>
    if v.index = i.val then toPropForm (σ.varValue v)
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

theorem toSubst_eq_of_ge {σ : PS} {v : IVar} :
    v.index ≥ σ.size → σ.toSubst v = v := by
  have : ∃ n, n = σ.gens.size := by
    use σ.gens.size
  rcases this with ⟨n, hn⟩
  induction n with
  | zero =>
    simp [toSubst, ← hn, Fin.foldl]
    rw [Fin.foldl.loop]
    simp [← hn]
  | succ n ih =>
    stop
    done

@[simp]
theorem litValue_negate (σ : PS) (l : ILit) :
    (σ.litValue (-l)) = negate (σ.litValue l) := by
  cases hpol : polarity l <;> simp [hpol, litValue]

variable {σ : PS} {v : IVar} {l : ILit}

theorem negate_varValue_eq_iff {val : PSV} :
    negate (σ.varValue v) = val ↔ σ.varValue v = negate val :=
  negate_eq_iff_eq_negate

theorem litValue_eq_varValue_true {l : ILit} :
    polarity l = true → ∀ (σ : PS), σ.litValue l = σ.varValue (toVar l) := by
  intro hl; simp [hl, litValue]

theorem litValue_eq_varValue_false {l : ILit} :
    polarity l = false → ∀ (σ : PS), σ.litValue l = negate (σ.varValue (toVar l)) := by
  intro hl; simp [hl, litValue]

theorem lt_size_of_varValue_ne : σ.varValue v ≠ v → v.index < σ.size := by
  intro hv
  simp [varValue, Array.get?] at hv
  rcases Nat.lt_trichotomy v.index σ.size with (hlt | heq | hgt)
  · exact hlt
  · simp [heq] at hv
  · simp [Nat.lt_asymm hgt] at hv

theorem lt_size_of_varValue_true : σ.varValue v = true → v.index < σ.size := by
  intro hσ
  apply lt_size_of_varValue_ne
  simp [hσ]

theorem lt_size_of_varValue_false : σ.varValue v = false → v.index < σ.size := by
  intro hσ
  apply lt_size_of_varValue_ne
  simp [hσ]

theorem varValue_eq_of_ge : v.index ≥ σ.size → σ.varValue v = v := by
  intro hv
  simp [size, varValue, getElem?, Nat.not_lt_of_ge hv]

theorem lt_size_of_litValue_true : σ.litValue l = true → l.index < σ.size := by
  intro hσ
  by_cases hpol : polarity l
  <;> simp [hpol, litValue] at hσ
  <;> try apply lt_size_of_varValue_true hσ
  rw [negate_varValue_eq_iff] at hσ
  exact lt_size_of_varValue_false hσ

theorem lt_size_of_litValue_false : σ.litValue l = false → l.index < σ.size := by
  intro hσ
  by_cases hpol : polarity l
  <;> simp [hpol, litValue] at hσ
  <;> try apply lt_size_of_varValue_false hσ
  rw [negate_varValue_eq_iff] at hσ
  exact lt_size_of_varValue_true hσ

theorem litValue_eq_of_ge : l.index ≥ σ.size → σ.litValue l = l := by
  intro hl
  by_cases hpol : polarity l
  <;> simp [litValue, hpol, varValue_eq_of_ge hl, PSV.negate]
  <;> ext
  <;> simp [hpol]

theorem varValue_eq_toSubst : σ.varValue v = σ.toSubst v := by
  by_cases hv : v.index < σ.size
  · have ⟨_, h_toSubst⟩ := (Fin.foldl_of_comm σ.size (idxToSubst σ) .var ⟨v.index, hv⟩ (idxToSubst_comm σ))
    simp [toSubst, h_toSubst, idxToSubst]
  · rw [not_lt] at hv
    simp [varValue_eq_of_ge hv, toSubst_eq_of_ge hv, PSV.toPropForm]

theorem varValue_eq_substL : σ.varValue v = PropFun.substL ⟦v⟧ σ.toSubst := by
  by_cases hv : v.index < σ.size
  · have ⟨S, h_toSubst⟩ := (Fin.foldl_of_comm σ.size (idxToSubst σ) .var ⟨v.index, hv⟩ (idxToSubst_comm σ))
    simp [PropFun.ext_iff, satisfies_substL, PropAssignment.subst]
    intro τ
    rw [toSubst, h_toSubst, idxToSubst]
    simp [hv]
    cases hσ : σ.varValue v
    <;> simp [PSV.toPropFun, PSV.toPropForm]
    rename Bool => b
    cases b <;> simp
  · rw [not_lt] at hv
    simp [varValue_eq_of_ge hv, PSV.toPropFun]
    simp [PropFun.ext_iff, satisfies_substL, PropAssignment.subst]
    intro τ
    simp [toSubst_eq_of_ge hv]
    done

theorem litValue_eq_substL : σ.litValue l = PropFun.substL ⟦l⟧ σ.toSubst := by
  by_cases hpol : polarity l
  <;> simp [litValue, hpol, varValue_eq_substL, PSV.toPropForm, LitVar.toPropFun]

theorem litValue_eq_substL' : σ.litValue l = PropFun.substL (LitVar.toPropFun l) σ.toSubst := by
  by_cases hpol : polarity l
  <;> simp [hpol, litValue, LitVar.toPropFun, varValue_eq_substL]

/-! # setLit -/

theorem setVar_le_maxGen (σ : PS) (i : Nat) (gen : Nat) :
    ∀ cell ∈ (σ.gens.setF i gen 0).data, cell ≤ max σ.maxGen p := by
  intro cell hcell
  sorry
  done

-- This is a more functional version
/-- Set the given literal to `true` for the current generation in the PS. -/
def setLit (σ : PS) (l : ILit) : PS :=
  let val : PSV := if polarity l then true else false
  { σ with
    gens := σ.gens.setF l.index σ.generation 0,
    mappings := σ.mappings.setF l.index val 0,
    maxGen := max σ.maxGen σ.generation
    sizes_eq := by simp [σ.sizes_eq]
    le_maxGen := setVar_le_maxGen σ l.index σ.generation
  }

def setVarToLit (σ : PS) (v : IVar) (l : ILit) : PS := { σ with
  gens := σ.gens.setF v.index σ.generation 0
  mappings := σ.mappings.setF v.index (PSV.toMapped' l) 0
  maxGen := max σ.maxGen σ.generation
  sizes_eq := by simp [σ.sizes_eq]
  le_maxGen := setVar_le_maxGen σ v.index σ.generation
}

def setVars (σ : PS) (A : Array (IVar × ILit)) : PS :=
  A.foldl (init := σ) (fun σ ⟨v, l⟩ => σ.setVarToLit v l)

def setVars' (σ : PS) (A : Array ILit) : PS :=
  let rec go (i : Nat) (σ : PS) : PS :=
    if hi : i + 1 < A.size then
      have : Array.size A - (i + 2) < Array.size A - i := Nat.sub_add_lt_sub hi (le.step le.refl)
      go (i + 2) (σ.setVarToLit (toVar (A.get ⟨i, Nat.lt_of_succ_lt hi⟩)) (A.get ⟨i + 1, hi⟩))
    else
      σ
  termination_by A.size - i
  go 0 σ

def setLits (σ : PS) (A : Array ILit) : PS :=
  A.foldl setLit σ

/- Lemmas -/

@[simp]
theorem setLit_size (σ : PS) (l : ILit) : (σ.setLit l).size = max σ.size (l.index + 1) := by
  simp [setLit, size]

@[simp]
theorem litValue_setLit (σ : PS) (l : ILit) : (σ.setLit l).litValue l = true := by
  by_cases hpol : polarity l
  <;> by_cases hl : l.index < σ.size
  <;> simp [litValue, varValue, size, setLit, hpol, hl, PSV.negate, Array.getElem_setF]

/-! # New -/

/-- Initialize to an empty partial assignment,
supporting variables in the range `[1, maxVar]`.

The assignment will resize dynamically if it's used with
a variable above the initial `maxVar`. -/

def new (n : Nat) : PS where
  gens := Array.mkArray n 0
  mappings := Array.mkArray n 0
  generation := ⟨1, Nat.one_pos⟩
  maxGen := 0
  sizes_eq := by simp
  le_maxGen := by simp_all [List.mem_replicate]

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

open ReductionResult

/- Reduction without tautology checking -/

-- Evaluate the provided literal under the PS
@[inline, always_inline]
def seval (σ : PS) (l : ILit) : ReductionResult :=
  match σ.litValue l with
  | Sum.inr true => satisfied
  | Sum.inr false => reduced
  | Sum.inl lit => if (l != lit) then reduced else notReduced

-- API-breaking version, go fast
@[inline, always_inline]
def seval' (σ : PS) (l : ILit) : ReductionResult :=
  if hl : l.index < σ.gens.size then
    let gen := σ.gens.get ⟨l.index, hl⟩
    if gen ≥ σ.generation then
      let n := σ.mappings.get ⟨l.index, by rw [σ.sizes_eq] at hl; exact hl⟩
      match n with
      | 0 => if polarity l then satisfied else reduced
      | 1 => if polarity l then reduced else satisfied
      | n => if PSV.toMapped' l != n then reduced else notReduced
    else notReduced
  else notReduced

theorem seval'_eq_seval (σ : PS) (l : ILit) :
    σ.seval' l = σ.seval l := by sorry

@[inline, always_inline]
def sevalM (σ : PS) (reduced? : Bool) (l : ILit) : Except Unit Bool :=
  match σ.litValue l with
  | Sum.inr true => .error ()
  | Sum.inr false => .ok true
  | Sum.inl lit => if (l != lit) then .ok true else .ok reduced?

def reduceM_Except : Except Unit Bool → ReductionResult
  | .ok true => reduced
  | .ok false => notReduced
  | .error _ => satisfied

def reduceM (σ : PS) (C : IClause) : ReductionResult :=
  reduceM_Except <| C.foldlM (init := false) (sevalM σ)

def reduce (σ : PS) (C : IClause) : ReductionResult :=
  let rec loop (i : Nat) (reduced? : Bool) : ReductionResult :=
    if hi : i < Size.size C then
      let lit := Seq.get C ⟨i, hi⟩
      match seval σ lit with
      | satisfied => satisfied
      | notReduced => loop (i + 1) reduced?
      | reduced => loop (i + 1) true
    else
      if reduced? then reduced else notReduced
  termination_by Size.size C - i
  loop 0 false

def LawfulReduce (Red : PS → IClause → ReductionResult) : Prop :=
  ∀ (σ : PS) (C : IClause),
    ((Red σ C = .satisfied) → (C.toPropFun).substL σ.toSubst = ⊤)
  ∧ ((Red σ C = .notReduced) → (C.toPropFun).substL σ.toSubst = C)

theorem foldlM_sevalM_true (σ : PS) (C : IClause) :
    (C.foldlM (sevalM σ) true = .ok true) ∨ -- ∧ ((C.toPropFun).substL σ.toSubst ≠ ⊤)) ∨
    (C.foldlM (sevalM σ) true = .error () ∧ (C.toPropFun).substL σ.toSubst = ⊤) := by
  have ⟨C⟩ := C
  rw [Array.foldlM_eq_foldlM_data]
  induction C with
  | nil => simp [pure, Except.pure]
  | cons l ls ih =>
    match hl : σ.litValue l with
    | Sum.inl l' =>
      simp [sevalM, hl]
      rcases ih with (h | ⟨h₁, h₂⟩)
      · exact Or.inl h
      · right
        use h₁
        simp [h₂]
    | Sum.inr true =>
      simp [sevalM, hl]
      right
      use rfl
      simp [← litValue_eq_substL', hl]
    | Sum.inr false =>
      simp [sevalM, hl]
      rcases ih with (h | ⟨h₁, h₂⟩)
      · exact Or.inl h
      · right
        use h₁
        simp [h₂]

theorem reduceM_Lawful : LawfulReduce reduceM := by
  intro σ C
  have ⟨C⟩ := C
  rw [reduceM, Array.foldlM_eq_foldlM_data]
  induction C with
  | nil => simp [reduceM_Except, pure, Except.pure]
  | cons l ls ih =>
    match hl : σ.litValue l with
    | Sum.inl l' =>
      simp [sevalM, hl]
      by_cases hl : l = l'
      · subst hl; simp [bind, Except.bind]
        simp at ih
        constructor
        <;> intro h
        <;> simp [h] at ih
        <;> simp [ih, ← litValue_eq_substL', hl]
      · simp [hl]
        rcases foldlM_sevalM_true σ ({ data := ls } : IClause) with (hls | ⟨hls, hpf⟩)
        <;> rw [Array.foldlM_eq_foldlM_data] at hls
        <;> simp at hls
        <;> simp [bind, Except.bind, reduceM_Except, hls]
        simp [hpf]
    | Sum.inr true =>
      simp [sevalM, reduceM_Except, hl, ← litValue_eq_substL', bind, Except.bind]
    | Sum.inr false =>
      simp [sevalM, reduceM_Except, hl]
      rcases foldlM_sevalM_true σ ({ data := ls } : IClause) with (hls | hls)
      <;> rw [Array.foldlM_eq_foldlM_data] at hls
      <;> simp at hls
      <;> simp [bind, Except.bind, reduceM_Except, hls]

theorem reduce.loop.cons_aux (σ : PS) (l : ILit) {ls : List ILit} {i j : Nat} :
    j = ls.length - i → reduce.loop σ ⟨l :: ls⟩ (i + 1) = reduce.loop σ ({ data := ls } : IClause) i := by
  intro hj
  ext reduced?
  induction j generalizing reduced? i with
  | zero =>
    have : i ≥ ls.length := Nat.le_of_sub_eq_zero hj.symm
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
    <;> apply ih (Nat.eq_sub_succ_of_succ_eq_sub hj)

theorem reduce.loop.cons (σ : PS) (l : ILit) (ls : List ILit) (i : Nat) :
    reduce.loop σ ⟨l :: ls⟩ (i + 1) = reduce.loop σ ({ data := ls } : IClause) i :=
  @reduce.loop.cons_aux σ l ls i (ls.length - i) rfl

theorem reduce_eq_reduceM_aux (σ : PS) (C : IClause) (reduced? : Bool) :
    reduce.loop σ C 0 reduced? = reduceM_Except (C.foldlM (sevalM σ) reduced?) := by
  have ⟨C⟩ := C
  induction C generalizing σ reduced? with
  | nil =>
    unfold reduce.loop
    simp [pure, Except.pure, reduceM_Except, LeanColls.size]
    cases reduced?
    <;> simp
  | cons l ls ih =>
    rw [reduce.loop, reduceM_Except, Array.foldlM_cons, sevalM]
    split <;> rename _ => hi
    · have h_get_l : Seq.get ({ data := l :: ls } : IClause) ⟨0, hi⟩ = l := rfl
      simp only [reduce.loop.cons, h_get_l, seval]
      match hl : σ.litValue l with
      | Sum.inr true => rfl
      | Sum.inr false => exact ih σ true
      | Sum.inl lit =>
        by_cases h_eq : l = lit
        · simp [h_eq]
          exact ih σ reduced?
        · simp [h_eq]
          exact ih σ true
    · simp [LeanColls.size] at hi

theorem reduce_eq_reduceM (σ : PS) (C : IClause) :
    reduce σ C = reduceM σ C := by
  rw [reduce, reduceM]
  exact reduce_eq_reduceM_aux σ C false

theorem reduce_Lawful : LawfulReduce reduce := by
  intro σ C
  rw [reduce_eq_reduceM]
  exact reduceM_Lawful σ C

#exit

-- CC: Helpful?
/-
theorem litValue_tr_iff_seval_satisfied {σ : PS} {r : Bool} {l : ILit} :
    (σ.litValue l = .tr) ↔ (σ.seval r l = error ()) := by
  simp [seval]; aesop

def reduceRes (res : Except Unit Bool) : ReductionResult :=
  match res with
  | ok true => .reduced
  | ok false => .notReduced
  | error _ => .satisfied

def reduce (σ : PS) (C : IClause) : ReductionResult :=
  reduceRes <| C.foldlM (seval σ) false

theorem reduce_satisfied_iff {σ : PS} {C : IClause} :
    σ.reduce C = .satisfied ↔ (C.toPropFun).substL σ.toSubst = ⊤ := by
  have ⟨C⟩ := C
  rw [reduce, reduceRes, Array.foldlM_eq_foldlM_data]
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
  -/

end monadic

end PS
