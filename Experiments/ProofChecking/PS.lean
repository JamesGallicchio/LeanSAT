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

theorem exists_double {n : Nat} : n % 2 = 0 → ∃ m, n = 2 * m := by
  intro h
  sorry
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

-- API-breaking version
/-
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
-/
@[inline, always_inline]
def seval' (σ : PS) (l : ILit) : ReductionResult :=
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

@[inline]
def seval_fold_fn (σ : PS) (res : ReductionResult) (lit : ILit) : ReductionResult :=
  match res with
  | satisfied => satisfied
  | reduced =>
    match seval σ lit with
    | satisfied => satisfied
    | reduced => reduced
    | notReduced => reduced
  | notReduced =>
    match seval σ lit with
    | satisfied => satisfied
    | reduced => reduced
    | notReduced => notReduced

@[inline]
def seval_fold_fn' (σ : PS) (res : ReductionResult) (lit : ILit) : ReductionResult :=
  match res with
  | satisfied => satisfied
  | reduced =>
    match seval' σ lit with
    | satisfied => satisfied
    | reduced => reduced
    | notReduced => reduced
  | notReduced =>
    match seval' σ lit with
    | satisfied => satisfied
    | reduced => reduced
    | notReduced => notReduced

def seval_fold (σ : PS) (C : IClause) : ReductionResult :=
  C.foldl (init := notReduced) (seval_fold_fn σ)

def seval_fold' (σ : PS) (C : IClause) : ReductionResult :=
  let rec loop (i : Nat) (b : Bool) : ReductionResult :=
    if h : i < C.size then
      match seval σ (C.get ⟨i, h⟩) with
      | satisfied => satisfied
      | reduced => loop (i + 1) true
      | notReduced => loop (i + 1) b
    else
      if b then reduced else notReduced
    termination_by C.size - i
  loop 0 false

def seval_fold'' (σ : PS) (C : IClause) : ReductionResult := Id.run do
  let mut reduced? : Bool := false
  for lit in C do
    match seval σ lit with
    | satisfied => return satisfied
    | reduced => reduced? := true
    | notReduced => continue

  if reduced? then
    return reduced
  else
    return notReduced

theorem seval_fold_eq_seval_fold' (σ : PS) (C : IClause) :
    σ.seval_fold C = σ.seval_fold' C := by
  have ⟨C⟩ := C
  rw [seval_fold, seval_fold']
  stop
  suffices ∀ (res : ReductionResult) (b : Bool), res ≠ satisfied →
    ((res = reduced) ↔ b) → ({ data := C } : IClause).foldl (fun res lit =>
    match res with
    | satisfied => satisfied
    | reduced =>
      match seval σ lit with
      | satisfied => satisfied
      | reduced => reduced
      | notReduced => reduced
    | notReduced =>
      match seval σ lit with
      | satisfied => satisfied
      | reduced => reduced
      | notReduced => notReduced) res 0 = seval_fold'.loop σ { data := C } 0 b by
    sorry
    done
  intro res b hres hb
  induction C generalizing res b with
  | nil =>
    cases res
    <;> cases b
    <;> try simp at hb
    <;> try contradiction
    · simp [seval_fold'.loop]
    · simp [seval_fold'.loop]
    done
  | cons l ls ih =>
    cases res
    · contradiction
    <;> simp
    · rw [Array.foldl_cons]
      simp only
      cases hσ : seval σ l
      · simp only
        done
      done
    done
  done

-- Alternate view of reduction, using indexes into an array
def reduceOnIndexes (σ : PS) (C : IClause) (s e : Nat) : ReductionResult :=
  let min_e := min e C.size
  let rec go (i : Nat) (reduced? : Bool) : ReductionResult :=
    if hi : i < min_e then
      match seval' σ (C.get ⟨i, Nat.lt_of_lt_of_le hi (min_le_right e C.size)⟩) with
      | satisfied => satisfied
      | reduced => go (i + 1) true
      | notReduced => go (i + 1) reduced?
    else
      if reduced? then reduced else notReduced
  termination_by (min e C.size) - i
  go s false

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
