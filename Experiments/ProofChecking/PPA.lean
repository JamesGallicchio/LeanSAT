/-

Persistent partial assignments (PPA).

The data structure underlying the PPA is a resizable array that can be ``cleared''
in O(1) time by bumping a generation number.
Each cell in the array stores a generation number that determines if the
cell is set (i.e. that it is above the data structure's generation number).
Used to implement partial assignments by assuming that all
variables are initially unset (PPA).

Authors: Cayden Codel, Wojciech Nawrocki, James Gallicchio
Carnegie Mellon University
-/

import LeanSAT.Data.Cnf
import LeanSAT.Data.Literal
import LeanSAT.Data.ICnf
import LeanSAT.Model.PropFun

import LeanSAT.Upstream.ToStd
import LeanSAT.Upstream.ToMathlib
import Experiments.ProofChecking.Array

import Mathlib.Data.Nat.Basic

import LeanColls
open LeanColls

open LeanSAT Model Nat
open LitVar ILit IVar LawfulLitVar
open PropFun

lemma Fin.foldl_induction (n) (f : α → Fin n → α) (init : α) (P : α → Fin (n+1) → Prop)
    (hInit : P init 0)
    (hSucc : ∀ a (i : Fin n), P a ⟨i.val, Nat.lt_succ_of_lt i.is_lt⟩ → P (f a i) ⟨i.val+1, Nat.succ_lt_succ i.is_lt⟩) :
    P (Fin.foldl n f init) ⟨n, Nat.lt_succ_self n⟩ :=
  loop init 0 hInit
where
  loop (x : α) (i : Fin (n+1)) (h : P x i) : P (Fin.foldl.loop n f x i.val) ⟨n, Nat.lt_succ_self n⟩ := by
    unfold foldl.loop
    split
    next h =>
      have := loop (f x ⟨i.val, h⟩) ⟨i.val+1, Nat.succ_lt_succ h⟩
      apply this
      apply hSucc
      assumption
    next h =>
      have : i.val = n := Nat.eq_of_le_of_lt_succ (not_lt.mp h) i.is_lt
      simp_rw [← this]
      assumption
  termination_by n - i

lemma Fin.foldl_induction' (n) (f : α → Fin n → α) (init : α) (P : α → Prop)
    (hInit : P init)
    (hSucc : ∀ a i, P a → P (f a i)) :
    P (Fin.foldl n f init) :=
  Fin.foldl_induction n f init (fun a _ => P a) hInit hSucc

lemma Fin.foldl_of_comm (n) (f : α → Fin n → α) (init : α) (i : Fin n)
    (H : ∀ (acc : α) (i₁ i₂ : Fin n), f (f acc i₁) i₂ = f (f acc i₂) i₁) :
    ∃ (acc : α), Fin.foldl n f init = f acc i :=
  i.is_lt |> Fin.foldl_induction n f init (fun res j => i.val < j.val → ∃ (acc : α), res = f acc i)
    (nomatch ·)
    (by
      intro a j ih h
      cases' lt_or_eq_of_le (Nat.lt_succ.mp h) with h
      . have ⟨acc, hAcc⟩ := ih h
        use (f acc j)
        rw [hAcc, H]
      . have : i = j := by ext; assumption
        use a
        rw [this])

/-! # Concise PPA (single array) -/

/-- A Persistent Partial Assignment of truth values to propositional variables.

Assuming the linearity restriction (see below) is met,
the PPA provides a fast representation of partial assignments.
The PPA is allocation-free as long as you initialize it
with the actual maximum variable index in `PPA.new`.
Otherwise, the PPA automatically resizes when a variable out of range is given.
The PPA provides functions for unit propagation and tautology checking.

The PPA is meant to be used persistently and linearly,
i.e., you should keep around exactly one copy of this structure.
Note that ensuring linearity in large functions can be tricky,
especially when `do` notation is used.
The only reliable method at the moment
is to look at the dynamic behavior in a profiler
and ensure that PPA code does not spend lots of time in `lean_copy_expand_array`. -/
structure PPA where
  /-- For each variable, stores the generation value that variable is set for. -/
  assignment : Array Int
  /-- The generation counter is used to avoid clearing the assignment array
      when the assignment is reset.  Instead, we just bump the counter and
      interpret values in the array below the counter as unassigned. -/
  generation : PNat
  /-- The maximum absolute value of any entry in `assignments`. -/
  maxGen : Nat
  le_maxGen : ∀ i ∈ assignment.data, i.natAbs ≤ maxGen

instance : ToString PPA where
  toString τ := String.intercalate " ∧ "
    (τ.assignment.foldl (init := []) (f := fun acc a => s!"{a}" :: acc))

/-! ## Reading values from the PPA -/

namespace PPA

@[reducible] def size (τ : PPA) : Nat := τ.assignment.size

/-- The value of the given variable in the current assignment, if assigned.
    Assignment is determined by comparing the current generation (τ.generation)
    against the generation value stored at that variable's index.
    If not assigned, returns `none`. -/
@[inline, always_inline]
def varValue? (τ : PPA) (v : IVar) : Option Bool :=
  match τ.assignment.get? v.index with
  | none => none
  | some n =>
    if τ.generation ≤ n.natAbs then
      some (0 < n)
    else
      none

/-- The value of the given literal in the current assignment, if assigned.
    Otherwise `none`. -/
@[inline, always_inline]
def litValue? (τ : PPA) (l : ILit) : Option Bool :=
  τ.varValue? (toVar l) |>.map (xor !(polarity l))

/-! ### Lemmas about `litValue?`, `varValue?` -/

@[simp] theorem litValue?_negate (τ : PPA) (l : ILit) :
    τ.litValue? (-l) = (τ.litValue? l).map Bool.not := by
  aesop (add norm unfold litValue?)

-- TODO: Make iff?
theorem litValue?_eq_varValue?_none {τ : PPA} {l : ILit} :
    τ.litValue? l = none → τ.varValue? (toVar l) = none := by
  aesop (add norm unfold litValue?)

theorem litValue?_eq_varValue?_some {τ : PPA} {l : ILit} {b : Bool} :
    τ.litValue? l = some b → τ.varValue? (toVar l) = xor (!b) (polarity l) := by
  aesop (add norm unfold litValue?)

@[simp] theorem litValue?_negate_none_iff {τ : PPA} {l : ILit} :
    τ.litValue? (-l) = none ↔ τ.litValue? l = none := by
  simp [litValue?_negate]

@[simp] theorem litValue?_negate_some_iff {τ : PPA} {l : ILit} {b : Bool} :
    τ.litValue? (-l) = some b ↔ τ.litValue? l = some (!b) := by
  cases b <;> simp [litValue?_negate]

@[simp] theorem litValue?_negate_some_iff' {τ : PPA} {l : ILit} {b : Bool} :
    τ.litValue? (-l) = some !b ↔ τ.litValue? l = some b := by
  cases b <;> simp [litValue?_negate]

theorem lt_size_of_varValue?_some {τ : PPA} {v : IVar} {b : Bool} :
    τ.varValue? v = some b → v.index < τ.size := by
  intro hv
  simp [varValue?, Array.get?] at hv
  rcases Nat.lt_trichotomy v.index τ.size with (hlt | heq | hgt)
  · exact hlt
  · simp [heq] at hv
  · simp [Nat.lt_asymm hgt] at hv

theorem lt_size_of_litValue?_some {τ : PPA} {l : ILit} {b : Bool} :
    τ.litValue? l = some b → (toVar l).index < τ.size := by
  simp [litValue?]
  rintro (⟨hv, _⟩ | ⟨hv, _⟩)
  <;> exact lt_size_of_varValue?_some hv

/-! ### `toPropFun` model -/

/-- The PropFun model for τ is the conjunctin of the variables it satisfies.
    Here, we map any variable set to true or false to the appropriate PropFun. -/
def varToPropFun (τ : PPA) (v : IVar) : PropFun IVar :=
  τ.varValue? v |>.map (if · then .var v else (.var v)ᶜ) |>.getD ⊤

/-- We can also calculate the model over just the indexes in range for τ. -/
def idxToPropFun (τ : PPA) (i : Fin τ.size) : PropFun IVar :=
  τ.varToPropFun ⟨IVar.fromIndex i, succ_pos _⟩

/-- We model the `PPA` as the conjunction of all its literals.
    Note that we cannot fully model the `PPA` as a `PropAssignment`
    because those are required to be total. -/
def toPropFun (τ : PPA) : PropFun IVar :=
  Fin.foldl τ.size (· ⊓ τ.idxToPropFun ·) ⊤

instance : Coe PPA (PropFun IVar) := ⟨toPropFun⟩

theorem satisfies_iff {τ : PPA} {σ : PropAssignment IVar} :
    σ ⊨ ↑τ ↔ ∀ (i : Fin τ.size), σ ⊨ τ.idxToPropFun i := by
  constructor
  . intro hσ i
    have ⟨ϕ, hϕ⟩ := Fin.foldl_of_comm τ.size (· ⊓ τ.idxToPropFun ·) ⊤ i (by intros; simp; ac_rfl)
    rw [toPropFun, hϕ] at hσ
    simp_all
  . intro h
    unfold toPropFun
    apply Fin.foldl_induction' (hInit := PropFun.satisfies_tr)
    intro ϕ i hϕ
    simp [hϕ, h i]

theorem satisfies_iff_vars {τ : PPA} {σ : PropAssignment IVar} :
    σ ⊨ ↑τ ↔ ∀ ⦃v⦄ ⦃b⦄, τ.varValue? v = some b → σ v = b := by
  constructor
  . rintro h v b h'
    have h := satisfies_iff.mp h ⟨IVar.index v, lt_size_of_varValue?_some h'⟩
    simp [idxToPropFun, varToPropFun] at h
    have : ⟨v.val, v.property⟩ = v := rfl
    rw [this, h'] at h
    simp only [this, Option.map_some', Option.getD_some] at h
    cases b <;> simp_all
  . intro h
    apply satisfies_iff.mpr
    intro i
    unfold idxToPropFun varToPropFun
    cases' h' : (varValue? τ _) with b
    . simp
    . have := h h'
      cases b <;> simp_all

theorem satisfies_iff_lits {τ : PPA} {σ : PropAssignment IVar} :
    σ ⊨ ↑τ ↔ ∀ ⦃l⦄, τ.litValue? l = some true → σ ⊨ ↑l := by
  simp_rw [LitVar.satisfies_iff, litValue?]
  constructor
  . intro h l h'
    apply satisfies_iff_vars.mp h
    simp_all
  . intro h
    apply satisfies_iff_vars.mpr
    intro x b
    have := @h (mkPos x)
    have := @h (mkNeg x)
    cases b <;> simp_all

/-- A satisfying assignment for `toPropFun`.
This is an arbitrary extension of `τ` from its domain to all of `IVar`. -/
def toSatAssignment (τ : PPA) : PropAssignment IVar :=
  fun v => τ.varValue? v |>.getD false

-- Like the above def, except the default value given to other vars can be provided
def toSatAssignment' (τ : PPA) (b : Bool) : PropAssignment IVar :=
  fun v => τ.varValue? v |>.getD b

theorem toSatAssignment_satisfies (τ : PPA) : τ.toSatAssignment ⊨ ↑τ := by
  aesop (add norm unfold toSatAssignment, norm satisfies_iff_vars)

theorem toSatAssignment'_satisfies (τ : PPA) (b : Bool) : τ.toSatAssignment' b ⊨ ↑τ := by
  aesop (add norm unfold toSatAssignment', norm satisfies_iff_vars)

theorem toPropFun_ne_bot (τ : PPA) : τ.toPropFun ≠ ⊥ := by
  intro
  have := τ.toSatAssignment_satisfies
  simp_all only [not_satisfies_fls]

theorem varValue?_true_iff {τ : PPA} {v : IVar} :
    τ.varValue? v = some true ↔ τ.toPropFun ≤ .var v := by
  constructor
  · intro h
    apply PropFun.entails_ext.mpr
    simp_all [satisfies_iff_vars]
  · intro h
    have := (PropFun.entails_ext.mp h) _ (toSatAssignment_satisfies τ)
    simp [toSatAssignment] at this
    match hτ : varValue? τ v with
    | none =>       simp [hτ] at this
    | some false => simp [hτ] at this
    | some true =>  rfl

theorem varValue?_false_iff {τ : PPA} {v : IVar} :
    τ.varValue? v = some false ↔ τ.toPropFun ≤ (.var v)ᶜ := by
  constructor
  · intro h
    apply PropFun.entails_ext.mpr
    simp_all [satisfies_iff_vars]
  · intro h
    have := (PropFun.entails_ext.mp h) _ (toSatAssignment'_satisfies τ true)
    simp [toSatAssignment'] at this
    match hτ : varValue? τ v with
    | none =>       simp [hτ] at this
    | some false => rfl
    | some true =>  simp [hτ] at this

theorem not_mem_semVars_of_varValue?_none {τ : PPA} {v : IVar} :
    τ.varValue? v = none → v ∉ τ.toPropFun.semVars := by
  rw [not_mem_semVars]
  intro hv σ b
  simp_rw [satisfies_iff_vars]
  constructor
  <;> intro hσ y b' hy
  <;> have : v ≠ y := fun h => by rw [h, hy] at hv; contradiction
  · rw [← hσ hy, PropAssignment.set_get_of_ne _ _ this]
  · rw [← hσ hy, PropAssignment.set_get_of_ne _ _ this]

theorem varValue?_none_iff {τ : PPA} {v : IVar} :
    τ.varValue? v = none ↔ ¬(τ.toPropFun ≤ .var v) ∧ ¬(τ.toPropFun ≤ (.var v)ᶜ) := by
  constructor
  · intro hNone
    constructor
    · intro hLt
      let σ := τ.toSatAssignment.set v false
      have : σ.agreeOn τ.toPropFun.semVars τ.toSatAssignment := fun y hMem =>
        have : v ≠ y := fun h => τ.not_mem_semVars_of_varValue?_none hNone (h ▸ hMem)
        PropAssignment.set_get_of_ne _ _ this
      have hσ : σ ⊨ τ.toPropFun := (agreeOn_semVars this).mpr τ.toSatAssignment_satisfies
      have : σ ⊭ .var v := by
        simp [satisfies_var, PropAssignment.set_get, not_false_eq_true, σ]
      exact this (entails_ext.mp hLt σ hσ)
    · intro hLt
      let σ := τ.toSatAssignment.set v true
      have : σ.agreeOn τ.toPropFun.semVars τ.toSatAssignment := fun y hMem =>
        have : v ≠ y := fun h => τ.not_mem_semVars_of_varValue?_none hNone (h ▸ hMem)
        PropAssignment.set_get_of_ne _ _ this
      have hσ : σ ⊨ τ.toPropFun := (agreeOn_semVars this).mpr τ.toSatAssignment_satisfies
      have : σ ⊭ (.var v)ᶜ := by
        simp only [PropFun.satisfies_neg, satisfies_var, PropAssignment.set_get,
          not_true_eq_false, not_false_eq_true, σ]
      exact this (entails_ext.mp hLt σ hσ)
  · rintro ⟨h₁, h₂⟩
    match hτ : varValue? τ v with
    | none =>       rfl
    | some true =>  exact absurd (varValue?_true_iff.mp hτ) h₁
    | some false => exact absurd (varValue?_false_iff.mp hτ) h₂

theorem litValue?_true_iff {τ : PPA} {l : ILit} :
    τ.litValue? l = some true ↔ τ.toPropFun ≤ l := by
  simp [litValue?, LitVar.toPropFun]
  cases polarity l <;>
    simp (config := {contextual := true}) [varValue?_false_iff, varValue?_true_iff]

theorem litValue?_false_iff {τ : PPA} {l : ILit} :
    τ.litValue? l = some false ↔ τ.toPropFun ≤ (↑l)ᶜ := by
  simp [litValue?, LitVar.toPropFun]
  cases polarity l <;>
    simp (config := {contextual := true}) [varValue?_false_iff, varValue?_true_iff]

theorem litValue?_none_iff {τ : PPA} {l : ILit} :
    τ.litValue? l = none ↔ ¬(τ.toPropFun ≤ l) ∧ ¬(τ.toPropFun ≤ (↑l)ᶜ) := by
  simp [litValue?, LitVar.toPropFun]
  cases (polarity l) <;>
    simp (config := {contextual := true}) [varValue?_none_iff]
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

theorem varValue?_true_iff_eq_inf {τ : PPA} {v : IVar} :
    τ.varValue? v = some true ↔ τ = τ.toPropFun ⊓ (.var v) := by
  simp only [varValue?_true_iff, left_eq_inf, imp_self]

theorem varValue?_false_iff_eq_inf {τ : PPA} {v : IVar} :
    τ.varValue? v = some false ↔ τ = τ.toPropFun ⊓ (.var v)ᶜ := by
  simp only [varValue?_false_iff, left_eq_inf, imp_self]

theorem litValue?_true_iff_eq_inf {τ : PPA} {l : ILit} :
    τ.litValue? l = some true ↔ τ = τ.toPropFun ⊓ ↑l := by
  simp only [litValue?_true_iff, left_eq_inf]

theorem litValue?_false_iff_eq_inf {τ : PPA} {l : ILit} :
    τ.litValue? l = some false ↔ τ = τ.toPropFun ⊓ (↑l)ᶜ := by
  simp only [litValue?_false_iff, left_eq_inf]

/-! ## Setting values in the PPA -/

/-- Initialize to an empty partial assignment,
supporting variables in the range `[1, maxVar]`.

The assignment will resize dynamically if it's used with
a variable above the initial `maxVar`. -/
def new (maxVar : Nat) : PPA where
  assignment := Array.mkArray maxVar 0
  generation := ⟨1, Nat.one_pos⟩
  maxGen := 0
  le_maxGen i h := by simp_all [List.mem_replicate]

/-- Reset the assignment to an empty one. -/
def reset (τ : PPA) : PPA :=
  { τ with generation := ⟨τ.maxGen + 1, Nat.succ_pos _⟩ }

/-- Clear all temporary assignments at the current generation. -/
def bump (τ : PPA) : PPA :=
  { τ with generation := ⟨τ.generation + 1, Nat.succ_pos _⟩ }

/-- Helper theorem for `setVar*`. -/
theorem setVar_le_maxGen (τ : PPA) (i : Nat) (b : Bool) (gen : Nat) :
    let v : Int := if b then gen else -gen
    ∀ g ∈ (τ.assignment.setF i v 0).data, g.natAbs ≤ max τ.maxGen gen := by
  intro v g hg
  have := Array.mem_setF _ _ _ _ g hg
  rcases this with h | h | h
  . exact le_max_of_le_left (τ.le_maxGen _ h)
  . simp [h]
  . cases b <;> simp [h, v]

/-- Set the given variable to `b` for the current generation. -/
def setVar (τ : PPA) (v : IVar) (b : Bool) : PPA :=
  let g : Int := if b then τ.generation else -τ.generation
  { τ with
    assignment := τ.assignment.setF v.index g 0
    maxGen := Nat.max τ.maxGen τ.generation
    le_maxGen := setVar_le_maxGen τ v.index b τ.generation }

/-- Set the given literal to `true` for the current generation. -/
def setLit (τ : PPA) (l : ILit) : PPA :=
  τ.setVar (toVar l) (polarity l)

/-- Set the given variable to `b` for all generations until `gen`. -/
def setVarUntil (τ : PPA) (v : IVar) (b : Bool) (gen : Nat) : PPA :=
  let g : Int := if b then gen else -gen
  { τ with
    assignment := τ.assignment.setF v.index g 0
    maxGen := Nat.max τ.maxGen gen
    le_maxGen := setVar_le_maxGen τ v.index b gen }

/-- Set the given literal to `true` for all generations until `gen`. -/
def setLitUntil (τ : PPA) (l : ILit) (gen : Nat) : PPA :=
  τ.setVarUntil (toVar l) (polarity l) gen

def setVarFor (τ : PPA) (v : IVar) (b : Bool) (extraBumps : Nat) : PPA :=
  let g : Int := if b then τ.generation + extraBumps else -(τ.generation + extraBumps)
  { τ with
    assignment := τ.assignment.setF v.index g 0
    maxGen := Nat.max τ.maxGen (τ.generation + extraBumps)
    le_maxGen := setVar_le_maxGen τ v.index b (τ.generation + extraBumps) }

def setLitFor (τ : PPA) (l : ILit) (extraBumps : Nat) : PPA :=
  τ.setVarFor (toVar l) (polarity l) extraBumps

/-! Lemmas about the above operations -/

theorem varValue?_bump_none_of_varValue?_none {τ : PPA} {v : IVar} :
    τ.varValue? v = none → τ.bump.varValue? v = none := by
  intro h
  simp [varValue?, bump] at h ⊢
  split at h
  · rfl
  · split
    · rename _ => h_gen
      have := le_of_succ_le h_gen
      simp [this] at h
    · rfl

theorem setVar_eq_setVarFor (τ : PPA) (v : IVar) (b : Bool) :
    τ.setVar v b = τ.setVarFor v b 0 := by
  simp [setVar, setVarFor]

theorem setVarUntil_eq_setVarFor (τ : PPA) (v : IVar) (b : Bool) (gen : Nat) :
    gen ≥ τ.generation → τ.setVarUntil v b gen = τ.setVarFor v b (gen - τ.generation) := by
  intro hgen
  simp [setVarUntil, setVarFor, ← Nat.add_sub_assoc hgen]
  congr
  · rw [← Nat.add_sub_assoc hgen, Nat.add_comm, Nat.add_sub_cancel]
  · have h := Int.mul_add (-1) ((gen : Int) - (τ.generation : Int)) τ.generation
    simp_rw [sub_add_cancel, neg_mul, one_mul] at h
    rw [h]
    aesop

theorem setLit_eq_setLitFor (τ : PPA) (l : ILit) :
    τ.setLit l = τ.setLitFor l 0 := by
  simp [setLit, setLitFor, setVar_eq_setVarFor]

theorem lt_reset_generation (τ : PPA) : ∀ i ∈ τ.reset.assignment.data, i.natAbs < τ.reset.generation := by
  dsimp [reset]
  intro i h
  have := τ.le_maxGen i h
  linarith

theorem lt_new_generation (maxVar : Nat) : ∀ i ∈ (new maxVar).assignment.data, i.natAbs < (new maxVar).generation := by
  intro i h
  simp [new] at h ⊢
  induction' maxVar with maxVar ih
  <;> simp at h
  rcases h with (rfl | h)
  · rfl
  · exact ih h

@[simp]
theorem varValue?_reset (τ : PPA) (v : IVar) : τ.reset.varValue? v = none := by
  unfold varValue?
  split
  . rfl
  . split
    . next n hn h =>
      have : n ∈ τ.reset.assignment.data := by
        simp_rw [Array.get?_eq_getElem?, Array.getElem?_eq_data_get?, List.get?_eq_some] at hn
        have ⟨_, hn⟩ := hn
        rw [← hn]
        apply List.get_mem
      have := τ.lt_reset_generation n this
      linarith
    . rfl

@[simp]
theorem litValue?_reset (τ : PPA) (l : ILit) : (τ.reset).litValue? l = none := by
  simp [litValue?, varValue?_reset]

@[simp]
theorem toPropFun_reset (τ : PPA) : τ.reset.toPropFun = ⊤ := by
  ext; simp [satisfies_iff_vars]

@[simp]
theorem varValue?_new (maxVar : Nat) (v : IVar) : (new maxVar).varValue? v = none := by
  unfold varValue?
  split
  . rfl
  . split
    . next n hn h =>
      have : n ∈ (new maxVar).assignment.data := by
        simp_rw [Array.get?_eq_getElem?, Array.getElem?_eq_data_get?, List.get?_eq_some] at hn
        have ⟨_, hn⟩ := hn
        rw [← hn]
        apply List.get_mem
      have := lt_new_generation maxVar n this
      linarith
    . rfl

@[simp]
theorem litValue?_new (maxVar : Nat) (l : ILit) : (new maxVar).litValue? l = none := by
  simp [litValue?, varValue?_new]

@[simp]
theorem toPropFun_new (maxVar : Nat) : (new maxVar).toPropFun = ⊤ := by
  ext; simp [satisfies_iff_vars]

/-! ### Lemmas about the `setVar`, `setLit` family -/

section setVar

variable (τ : PPA) (v : IVar) (l : ILit) (b : Bool) (bumps : Nat)

@[simp]
theorem varValue?_setVar : (τ.setVar v b).varValue? v = some b := by
  unfold varValue? setVar
  cases b <;> simp [Array.getElem?_setF, τ.generation.property]

theorem varValue?_setVar_of_ne {v v' : IVar} :
    v ≠ v' → ∀ (τ : PPA) (b : Bool), (τ.setVar v b).varValue? v' = τ.varValue? v' := by
  intro hne
  simp [varValue?, setVar, Array.getElem?_setF' (mt PNat.natPred_inj.mp hne)]

@[simp]
theorem varValue?_setLit : (τ.setLit l).varValue? (toVar l) = some (polarity l) := by
  simp [setLit, varValue?_setVar]

@[simp]
theorem litValue?_setLit : (τ.setLit l).litValue? l = some true := by
  simp [litValue?, setLit, varValue?_setVar]

@[simp]
theorem litValue?_setLit_negate : (τ.setLit l).litValue? (-l) = some false := by
  simp [litValue?, setLit, varValue?_setVar]

@[simp]
theorem litValue?_setLit_negate' : (τ.setLit (-l)).litValue? l = some false := by
  simp [litValue?, setLit, varValue?_setVar]

@[simp]
theorem varValue?_setLit_of_ne {l : ILit} {v : IVar} :
    toVar l ≠ v → ∀ (τ : PPA), (τ.setLit l).varValue? v = τ.varValue? v := by
  intro h
  simp [setLit, varValue?_setVar_of_ne h]

theorem litValue?_setLit_of_ne {l l' : ILit} :
    toVar l ≠ toVar l' → ∀ (τ : PPA), (τ.setLit l).litValue? l' = τ.litValue? l' := by
  intro h
  simp [litValue?, varValue?_setLit_of_ne h]

@[simp]
theorem varValue?_setVarFor : (τ.setVarFor v b bumps).varValue? v = some b := by
  unfold varValue? setVarFor
  cases b <;> simp [Array.getElem?_setF, τ.generation.property]
  · constructor
    · rw [← Int.neg_add, Int.natAbs_neg, ← Nat.cast_add, Int.natAbs_ofNat]
      exact Nat.le_add_left _ _
    · linarith
  · constructor
    · rw [← Nat.cast_add, Int.natAbs_ofNat]
      exact Nat.le_add_right _ _
    · have : τ.generation ≤ τ.generation + bumps := Nat.le_add_right (↑τ.generation) bumps
      rw [← Nat.cast_add]
      exact Int.ofNat_pos.mpr (lt_of_lt_of_le ↑τ.generation.property this)

theorem varValue?_setVarFor_of_ne {v v' : IVar} :
    v ≠ v' → ∀ (τ : PPA) (b : Bool) (bumps : Nat),
      (τ.setVarFor v b bumps).varValue? v' = τ.varValue? v' := by
  intro hne
  simp [varValue?, setVarFor, Array.getElem?_setF' (mt PNat.natPred_inj.mp hne)]

@[simp]
theorem varValue?_setLitFor : (τ.setLitFor l bumps).varValue? (toVar l) = some (polarity l) := by
  simp [setLitFor]

@[simp]
theorem litValue?_setLitFor : (τ.setLitFor l bumps).litValue? l = some true := by
  simp [litValue?, setLitFor]

@[simp]
theorem litValue?_setLitFor_negate : (τ.setLitFor l bumps).litValue? (-l) = some false := by
  simp [litValue?, setLitFor]

@[simp]
theorem litValue?_setLitFor_negate' : (τ.setLitFor (-l) bumps).litValue? l = some false := by
  simp [litValue?, setLitFor]

theorem varValue?_setLitFor_of_ne {l : ILit} {v : IVar} : toVar l ≠ v →
    ∀ (τ : PPA) (bumps : Nat), (τ.setLitFor l bumps).varValue? v = τ.varValue? v := by
  intro h
  simp [setLitFor, varValue?_setVarFor_of_ne h]

theorem litValue?_setLitFor_of_ne {l l' : ILit} : toVar l ≠ toVar l' →
    ∀ (τ : PPA) (bumps : Nat), (τ.setLitFor l bumps).litValue? l' = τ.litValue? l' := by
  intro h
  simp [litValue?, varValue?_setLitFor_of_ne h]

/-! ### `toPropFun` model -/

theorem toPropFun_setVar_true_of_none {τ : PPA} {v : IVar} : τ.varValue? v = none →
    (τ.setVar v true).toPropFun = τ.toPropFun ⊓ .var v := by
  intro h
  rw [le_antisymm_iff]
  constructor
  <;> apply entails_ext.mpr
  <;> intro σ hσ
  · rw [satisfies_iff_vars] at hσ
    rw [satisfies_conj, satisfies_iff_vars, satisfies_var]
    constructor
    · intro v' b' hv'
      apply hσ
      by_cases heq : v = v'
      · subst heq
        rw [h] at hv'; contradiction
      · rwa [varValue?_setVar_of_ne heq]
    · apply hσ
      apply varValue?_setVar
  · rw [satisfies_conj, satisfies_iff_vars, satisfies_var] at hσ
    rcases hσ with ⟨hσ₁, hσ₂⟩
    rw [satisfies_iff_vars]
    intro v' b' hv'
    by_cases heq : v = v'
    · subst heq
      rw [varValue?_setVar] at hv'; injection hv'; rename _ => h; subst h
      exact hσ₂
    · rw [varValue?_setVar_of_ne heq] at hv'
      exact hσ₁ hv'

theorem toPropFun_setVar_false_of_none {τ : PPA} {v : IVar} : τ.varValue? v = none →
    (τ.setVar v false).toPropFun = τ.toPropFun ⊓ (.var v)ᶜ := by
  intro h
  rw [le_antisymm_iff]
  constructor
  <;> apply entails_ext.mpr
  <;> intro σ hσ
  · rw [satisfies_iff_vars] at hσ
    rw [satisfies_conj, satisfies_iff_vars]
    constructor
    · intro v' b' hv'
      apply hσ
      by_cases heq : v = v'
      · subst heq
        rw [h] at hv'; contradiction
      · rwa [varValue?_setVar_of_ne heq]
    · simp; apply hσ
      apply varValue?_setVar
  · rw [satisfies_conj, satisfies_iff_vars] at hσ
    rcases hσ with ⟨hσ₁, hσ₂⟩; simp at hσ₂
    rw [satisfies_iff_vars]
    intro v' b' hv'
    by_cases heq : v = v'
    · subst heq
      rw [varValue?_setVar] at hv'; injection hv'; rename _ => h; subst h
      exact hσ₂
    · rw [varValue?_setVar_of_ne heq] at hv'
      exact hσ₁ hv'

theorem toPropFun_setVar_of_some {τ : PPA} {v : IVar} {b : Bool} :
    τ.varValue? v = some b → (τ.setVar v b).toPropFun = τ.toPropFun := by
  intro h
  rw [le_antisymm_iff]
  constructor
  <;> apply entails_ext.mpr
  <;> intro σ hσ
  <;> rw [satisfies_iff_vars] at hσ ⊢
  <;> intro v' b' hv'
  <;> apply hσ
  <;> by_cases heq : v = v'
  · subst heq
    rw [hv'] at h; injection h; rename _ => h; subst h
    apply varValue?_setVar
  · rwa [varValue?_setVar_of_ne heq]
  · subst heq
    rw [varValue?_setVar] at hv'; injection hv'; rename _ => hb; subst hb
    exact h
  · rwa [varValue?_setVar_of_ne heq] at hv'

theorem toPropFun_setLit_of_none {τ : PPA} {l : ILit} :
    τ.litValue? l = none → (τ.setLit l).toPropFun = τ.toPropFun ⊓ l := by
  intro h
  rcases mkPos_or_mkNeg l with (hl | hl)
  <;> rw [hl, setLit]
  <;> have := litValue?_eq_varValue?_none h
  · simp [toPropFun_setVar_true_of_none this]
  · simp [toPropFun_setVar_false_of_none this]

theorem toPropFun_setLit_of_true {τ : PPA} {l : ILit} :
    τ.litValue? l = some true → (τ.setLit l).toPropFun = τ.toPropFun := by
  simp [litValue?, setLit]
  exact toPropFun_setVar_of_some

-- No matter the status of τ.toPropFun, setting the lit adds it to the PPA.
theorem toPropFun_setLit_le (τ : PPA) (l : ILit) :
    (τ.setLit l).toPropFun ≤ l := by
  apply entails_ext.mpr
  intro σ hσ
  rw [satisfies_iff_lits] at hσ
  apply hσ
  apply litValue?_setLit

@[simp]
theorem toPropFun_setVarFor_eq_setVar {τ : PPA} {v : IVar} {b : Bool} {bumps : Nat} :
    (τ.setVarFor v b bumps).toPropFun = (τ.setVar v b).toPropFun := by
  rw [le_antisymm_iff]
  constructor
  <;> apply entails_ext.mpr
  <;> intro σ hσ
  <;> rw [satisfies_iff_vars] at hσ ⊢
  <;> intro v' b' hv'
  <;> apply hσ
  · by_cases heq : v = v'
    · subst heq
      rw [varValue?_setVar] at hv'; injection hv'; rename _ => h; subst h
      apply varValue?_setVarFor
    · rw [varValue?_setVar_of_ne heq] at hv'
      rwa [varValue?_setVarFor_of_ne heq]
  · by_cases heq : v = v'
    · subst heq
      rw [varValue?_setVarFor] at hv'; injection hv'; rename _ => h; subst h
      apply varValue?_setVar
    · rw [varValue?_setVarFor_of_ne heq] at hv'
      rwa [varValue?_setVar_of_ne heq]

@[simp]
theorem toPropFun_setLitFor_eq_setLit {τ : PPA} {l : ILit} {bumps : Nat} :
    (τ.setLitFor l bumps).toPropFun = (τ.setLit l).toPropFun := by
  rw [setLitFor, setLit, toPropFun_setVarFor_eq_setVar]

end setVar /- section -/

/-! # SetFor judgment -/

section isSetFor

variable {τ : PPA} {v : IVar}

def isSet (τ : PPA) (v : IVar) : Prop :=
  τ.varValue? v ≠ none

-- Says that the provided variable is set for n "bumps"
-- Add 1 because setting the variable sets its assignment value to τ.generation, so it's set for 1 bump
def isSetFor (τ : PPA) (v : IVar) : Nat :=
  ((τ.assignment.getD v.index 0).natAbs + 1) - τ.generation.val

theorem isSet_of_varValue?_some {τ : PPA} {v : IVar} :
    τ.varValue? v = some b → isSet τ v := by
  intro h
  simp [isSet, h]

theorem isSetFor_pos_iff : isSetFor τ v > 0 ↔ isSet τ v := by
  simp [isSet, isSetFor, varValue?]
  match hv : τ.assignment[v.index]? with
  | none => simp [hv]
  | some g =>
    simp [hv]
    exact lt_succ

-- CC: Might be useless since we can unroll the definition. Use an `abbrev` instead?
theorem isSet_iff : isSet τ v ↔ τ.varValue? v ≠ none :=
  ⟨id, id⟩

@[simp]
theorem not_isSet_new (maxVar : Nat) (v : IVar) : ¬isSet (new maxVar) v := by
  simp [isSet, varValue?_new]

theorem isSetFor_zero_iff {τ : PPA} {v : IVar} :
    isSetFor τ v = 0 ↔ τ.varValue? v = none := by
  cases hv : τ.assignment[v.index]?
  <;> simp [isSetFor, varValue?, hv]
  · exact Nat.sub_eq_zero_of_le τ.generation.property
  · simp [Nat.sub_eq_zero_iff_le]; rfl

@[simp]
theorem setVar_isSetFor (τ : PPA) (v : IVar) (b : Bool) : isSetFor (τ.setVar v b) v = 1 := by
  simp [isSetFor, setVar]; cases b <;> simp

theorem setVar_isSetFor_of_ne {v v' : IVar} :
    v ≠ v' → ∀ τ, isSetFor (τ.setVar v true) v' = isSetFor τ v' := by
  intro hne
  simp [isSetFor, setVar, Array.getElem?_setF' (mt PNat.natPred_inj.mp hne)]

@[simp]
theorem setLit_isSetFor (τ : PPA) (l : ILit) : isSetFor (τ.setLit l) (toVar l) = 1 :=
  setVar_isSetFor _ _ _

@[simp]
theorem setLit_isSetFor_negate (τ : PPA) (l : ILit) : isSetFor (τ.setLit (-l)) (toVar l) = 1 := by
  simp [setLit]

theorem setLit_isSetFor_of_ne {l₁ l₂ : ILit} :
    toVar l₁ ≠ toVar l₂ → isSetFor (τ.setLit l₁) (toVar l₂) = isSetFor τ (toVar l₂) := by
  intro hne
  simp [isSetFor, setLit, setVar, Array.getElem?_setF' (mt PNat.natPred_inj.mp hne)]

theorem setLit_isSetFor_of_ne' {l : ILit} {v : IVar} :
    toVar l ≠ v → isSetFor (τ.setLit l) v = isSetFor τ v := by
  intro hne
  simp [isSetFor, setLit, setVar, Array.getElem?_setF' (mt PNat.natPred_inj.mp hne)]

@[simp]
theorem setVarFor_isSetFor (τ : PPA) (v : IVar) (b : Bool) (bumps : Nat) :
    isSetFor (τ.setVarFor v b bumps) v = bumps + 1 := by
  simp [isSetFor, setVarFor]; cases b <;> simp
  · rw [← Int.neg_add, Int.natAbs_neg]
    have : Int.natAbs (bumps + τ.generation) = bumps + τ.generation := rfl
    rw [this, add_assoc, add_comm τ.generation.val 1, ← add_assoc, Nat.add_sub_cancel]
  · have : Int.natAbs (τ.generation + bumps) = τ.generation + bumps := rfl
    rw [this, add_comm τ.generation.val _, add_assoc, add_comm τ.generation.val 1, ← add_assoc, Nat.add_sub_cancel]

@[simp]
theorem setLitFor_isSetFor (τ : PPA) (l : ILit) (bumps : Nat) :
    isSetFor (τ.setLitFor l bumps) (toVar l) = (bumps + 1) :=
  setVarFor_isSetFor _ _ _ _

@[simp]
theorem setLitFor_isSetFor_negate (τ : PPA) (l : ILit) (bumps : Nat) :
    isSetFor (τ.setLitFor (-l) bumps) (toVar l) = (bumps + 1) := by
  simp [setLitFor]

theorem setLitFor_isSetFor_of_ne {l₁ l₂ : ILit} :
    toVar l₁ ≠ toVar l₂ → ∀ (bumps : Nat),
      isSetFor (τ.setLitFor l₁ bumps) (toVar l₂) = isSetFor τ (toVar l₂) := by
  intro hne bumps
  simp [isSetFor, setLitFor, setVarFor, Array.getElem?_setF' (mt PNat.natPred_inj.mp hne)]

-- TODO: Standardize names
theorem setLitFor_isSetFor_of_ne' {l : ILit} {v : IVar} :
    toVar l ≠ v → ∀ (bumps : Nat),
      isSetFor (τ.setLitFor l bumps) v = isSetFor τ v := by
  intro hne bumps
  simp [isSetFor, setLitFor, setVarFor, Array.getElem?_setF' (mt PNat.natPred_inj.mp hne)]

@[simp]
theorem isSet_setVar (τ : PPA) (v : IVar) (b : Bool) :
    isSet (τ.setVar v b) v := by
  cases b <;> simp [isSet, setVar, varValue?]

@[simp]
theorem isSet_setLit (τ : PPA) (l : ILit) :
    isSet (τ.setLit l) (toVar l) := by
  cases hpol : polarity l <;> simp [isSet, setLit, setVar, varValue?, hpol]

theorem isSet_setLit_of_ne {l₁ l₂ : ILit} :
    toVar l₁ ≠ toVar l₂ → ∀ τ, isSet (τ.setLit l₁) (toVar l₂) = isSet τ (toVar l₂) := by
  intro hne τ
  simp [isSet, setLit, setVar, varValue?, Array.getElem?_setF' (mt PNat.natPred_inj.mp hne)]

theorem isSet_setLit_of_ne' {l : ILit} {v : IVar} :
    toVar l ≠ v → ∀ τ, isSet (τ.setLit l) v = isSet τ v := by
  intro hne τ
  simp [isSet, setLit, setVar, varValue?, Array.getElem?_setF' (mt PNat.natPred_inj.mp hne)]

@[simp]
theorem isSet_setVarFor (τ : PPA) (v : IVar) (b : Bool) (offset : Nat) :
    isSet (τ.setVarFor v b offset) v := by
  simp [← isSetFor_pos_iff]

@[simp]
theorem isSet_setLitFor (τ : PPA) (l : ILit) (offset : Nat) :
    isSet (τ.setLitFor l offset) (toVar l) := by
  simp [← isSetFor_pos_iff]

theorem isSet_setLitFor_of_ne {l₁ l₂ : ILit} :
    toVar l₁ ≠ toVar l₂ → ∀ τ bumps,
      isSet (τ.setLitFor l₁ bumps) (toVar l₂) = isSet τ (toVar l₂) := by
  intro hne τ bumps
  simp_rw [← isSetFor_pos_iff, setLitFor_isSetFor_of_ne hne]

theorem isSet_setLitFor_of_ne' {l : ILit} {v : IVar} :
    toVar l ≠ v → ∀ τ bumps, isSet (τ.setLitFor l bumps) v = isSet τ v := by
  intro hne τ bumps
  simp_rw [← isSetFor_pos_iff, setLitFor_isSetFor_of_ne' hne]

@[simp]
theorem isSet_reset (τ : PPA) : ∀ (v : IVar), ¬isSet τ.reset v := by
  simp [isSet, varValue?_reset]

@[simp]
theorem isSet_new (maxVar : Nat) : ∀ (v : IVar), ¬isSet (new maxVar) v := by
  simp [isSet, varValue?_new]

@[simp]
theorem isSetFor_bump {τ : PPA} {v : IVar} :
    isSetFor τ.bump v = isSetFor τ v - 1 := by
  simp [isSetFor, bump, ← sub_add_eq, ← Nat.add_sub_add_right]

theorem isSet_of_isSet_bump {τ : PPA} {v : IVar} :
    isSet τ.bump v → isSet τ v := by
  intro h
  rw [← isSetFor_pos_iff] at h ⊢
  simp at h
  exact lt_trans zero_lt_one h

@[simp]
theorem isSetFor_reset (τ : PPA) (v : IVar) : isSetFor τ.reset v = 0 :=
  isSetFor_zero_iff.mpr (varValue?_reset τ v)

-- CC: This is an iff, but only need → for now
theorem varValue?_bump_of_isSetFor_pos {τ : PPA} {v : IVar} :
    isSetFor τ v > 1 → (τ.bump).varValue? v = τ.varValue? v := by
  intro h
  simp [varValue?, bump, isSetFor] at h ⊢
  match hv : τ.assignment[v.index]? with
  | none => rfl
  | some g =>
    simp [hv] at h
    simp
    have : (τ.generation.val) + 1 < g.natAbs + 1 := add_lt_of_lt_sub' h
    have : τ.generation.val + 1 ≤ g.natAbs := lt_succ.mp this
    have : τ.generation.val ≤ g.natAbs := Nat.le_of_lt this
    simp [*]

end isSetFor /- section -/

/-! extended and uniform -/

def extended (τ τ' : PPA) (offset : Nat) : Prop := ∀ (v : IVar),
    (τ.isSet v → τ'.isSetFor v = τ.isSetFor v ∧ τ'.varValue? v = τ.varValue? v)
    ∧ (¬τ.isSet v → τ'.isSet v → τ'.isSetFor v = offset + 1)

def uniform (τ : PPA) (offset : Nat) : Prop :=
  ∀ (v : IVar), τ.isSet v → τ.isSetFor v = offset + 1

@[simp]
theorem extended_refl (τ : PPA) (offset : Nat) : extended τ τ offset := by
  simp [extended]; intro v hcon h; exact absurd h hcon

theorem extended_trans {τ₁ τ₂ τ₃ : PPA} {offset : Nat} :
    extended τ₁ τ₂ offset → extended τ₂ τ₃ offset → extended τ₁ τ₃ offset := by
  intro h₁ h₂ v
  constructor
  · intro hv
    rcases (h₁ v).1 hv with ⟨h_isSet, h_varValue⟩
    rw [← h_isSet, ← h_varValue]
    rw [← isSetFor_pos_iff, ← h_isSet, isSetFor_pos_iff] at hv
    exact (h₂ v).1 hv
  · intro hv₁ hv₃
    by_cases hv₂ : τ₂.isSet v
    · rw [((h₂ v).1 hv₂).1]
      exact ((h₁ v).2 hv₁) hv₂
    · exact (h₂ v).2 hv₂ hv₃

theorem entails_of_extended {τ₁ τ₂ : PPA} {offset : Nat} :
    extended τ₁ τ₂ offset → τ₂.toPropFun ≤ τ₁ := by
  intro hext
  apply entails_ext.mpr
  intro τ hτ₂
  rw [satisfies_iff_vars] at hτ₂ ⊢
  intro v b hv
  have := (hext v).1
  simp [isSet_iff, hv] at this
  exact hτ₂ this.2

theorem extended_setLitFor_of_none {τ : PPA} {l : ILit} :
    τ.litValue? l = none → ∀ offset, extended τ (τ.setLitFor l offset) offset := by
  intro hl offset v
  constructor
  · intro hv
    by_cases hvar : (toVar l) = v
    · rw [isSet_iff] at hv
      have := litValue?_eq_varValue?_none hl
      rw [hvar] at this
      rw [this] at hv
      contradiction
    · simp [isSet_setLitFor_of_ne' hvar, hv, setLitFor_isSetFor_of_ne' hvar,
        varValue?_setLitFor_of_ne hvar]
  · intro hv hlv
    by_cases hvar : (toVar l) = v
    · simp [setLitFor, hvar]
    · simp [isSet_setLitFor_of_ne' hvar] at hlv
      exact absurd hlv hv

@[simp]
theorem uniform_new (maxVar : Nat) (offset : Nat) : uniform (new maxVar) offset := by
  simp [uniform, isSet, isSetFor, varValue?_new]

@[simp]
theorem uniform_reset (τ : PPA) (offset : Nat) : uniform τ.reset offset := by
  simp [uniform, isSet, isSetFor, varValue?_reset]

theorem uniform_bump {τ : PPA} {offset : Nat} : uniform τ offset → uniform τ.bump (offset - 1) := by
  intro h_uni v hv
  have h_set := isSet_of_isSet_bump hv
  have h_setFor := h_uni _ h_set
  simp [h_setFor]
  match offset with
  | zero =>
    rw [Nat.zero_add] at h_setFor
    rw [← isSetFor_pos_iff] at h_set hv
    simp [h_setFor] at hv
  | succ offset => simp

theorem uniform_of_extended_reset {τ₁ τ₂ : PPA} {offset : Nat} :
    extended (τ₁.reset) τ₂ offset → uniform τ₂ offset := by
  simp [extended, uniform]

theorem uniform_of_uniform_of_extended {τ₁ τ₂ : PPA} {offset : Nat} :
    uniform τ₁ offset → extended τ₁ τ₂ offset → uniform τ₂ offset := by
  simp [uniform, extended]
  intro hτ₁ h_ext v hv
  by_cases isSet τ₁ v <;> aesop

-- CC: Note 5/27: the (+2) is necessary for equality, which *is* needed in the checker.
-- If everything set in τ₂ is set only until the next bump, then τ₂'s bump is
-- uniform and is at most constrained as much as τ₁.
theorem uniform_bump_of_uniform_of_extended {τ₁ τ₂ : PPA} {offset : Nat} :
    uniform τ₁ (offset + 1) → extended τ₁ τ₂ 0 →
      uniform τ₂.bump offset ∧ τ₁.toPropFun ≤ τ₂.bump.toPropFun := by
  intro h_uni h_ext
  constructor
  · intro v hv
    have := isSet_of_isSet_bump hv
    by_cases hτ₁ : τ₁.isSet v
    · rcases (h_ext v).1 hτ₁ with ⟨h₁, _⟩
      have := h_uni _ hτ₁
      rw [← h₁] at this
      simp [this]
    · have := (h_ext v).2 hτ₁ this
      simp at this
      simp [← isSetFor_pos_iff, this] at hv
  · refine entails_ext.mpr fun τ hτ => ?_
    rw [satisfies_iff_vars] at hτ ⊢
    intro v b hv
    apply hτ
    rw [← hv]
    clear hv
    symm
    by_cases hτ₁ : τ₁.isSet v
    · rcases (h_ext v).1 hτ₁ with ⟨h₁, h₂⟩
      rw [← h₂]
      have := h_uni _ hτ₁
      rw [← h₁] at this
      have : isSetFor τ₂ v > 1 := by simp [this]
      exact varValue?_bump_of_isSetFor_pos this
    · have := (h_ext v).2 hτ₁
      simp [← isSetFor_pos_iff] at hτ₁
      rw [isSetFor_zero_iff.mp hτ₁]
      simp [isSetFor_pos_iff] at this
      by_cases hτ₂ : isSet τ₂ v
      · replace this := this hτ₂
        apply isSetFor_zero_iff.mp
        simp [this]
      · simp [isSet] at hτ₂
        exact varValue?_bump_none_of_varValue?_none hτ₂

theorem uniform_bump_of_uniform_of_extended' {τ₁ τ₂ : PPA} {offset : Nat} :
    uniform τ₁ (offset + 2) → extended τ₁ τ₂ 0 →
      uniform τ₂.bump (offset + 1) ∧ τ₁.toPropFun = τ₂.bump.toPropFun := by
  intro h_uni h_ext
  constructor
  · intro v hv
    have := isSet_of_isSet_bump hv
    by_cases hτ₁ : τ₁.isSet v
    · rcases (h_ext v).1 hτ₁ with ⟨h₁, _⟩
      have := h_uni _ hτ₁
      rw [← h₁] at this
      simp [this]
    · have := (h_ext v).2 hτ₁ this
      simp at this
      simp [← isSetFor_pos_iff, this] at hv
  · ext τ
    constructor
    · intro hτ₁
      rw [satisfies_iff_vars] at hτ₁ ⊢
      intro v b hv
      apply hτ₁
      rw [← hv]
      clear hv
      symm
      by_cases hv : τ₁.isSet v
      · rcases (h_ext v).1 hv with ⟨h₁, h₂⟩
        rw [← h₂]
        have := h_uni _ hv
        rw [← h₁] at this
        have : isSetFor τ₂ v > 1 := by simp [this]
        exact varValue?_bump_of_isSetFor_pos this
      · have := (h_ext v).2 hv
        simp [← isSetFor_pos_iff] at hv
        rw [isSetFor_zero_iff.mp hv]
        simp [isSetFor_pos_iff] at this
        by_cases hτ₂ : isSet τ₂ v
        · replace this := this hτ₂
          apply isSetFor_zero_iff.mp
          simp [this]
        · simp [isSet] at hτ₂
          exact varValue?_bump_none_of_varValue?_none hτ₂
    · intro hτ₂
      rw [satisfies_iff_vars] at hτ₂ ⊢
      intro v b hv
      apply hτ₂
      rw [← hv]
      clear hv
      by_cases hv : τ₁.isSet v
      · rcases (h_ext v).1 hv with ⟨h₁, h₂⟩
        rw [← h₂]
        have := h_uni _ hv
        rw [← h₁] at this
        have : isSetFor τ₂ v > 1 := by simp [this]
        exact varValue?_bump_of_isSetFor_pos this
      · have := (h_ext v).2 hv
        simp [← isSetFor_pos_iff] at hv
        rw [isSetFor_zero_iff.mp hv]
        simp [isSetFor_pos_iff] at this
        by_cases hτ₂ : isSet τ₂ v
        · replace this := this hτ₂
          apply isSetFor_zero_iff.mp
          simp [this]
        · simp [isSet] at hτ₂
          exact varValue?_bump_none_of_varValue?_none hτ₂

/-! Assuming negated clauses -/

/-- Set `l ↦ ⊥` for each `l ∈ C` and leave the rest of the assignment untouched.
If the current assignment contains literals appearing in `C`, they will be overwritten. -/
def setNegatedClause (τ : PPA) (C : IClause) : PPA :=
  C.foldl (init := τ) (fun τ l => τ.setLit (-l))

def setNegatedClauseUntil (τ : PPA) (C : IClause) (gen : Nat) : PPA :=
  C.foldl (init := τ) (fun τ l => τ.setLitUntil (-l) gen)

def setNegatedClauseFor (τ : PPA) (C : IClause) (extraBumps : Nat) : PPA :=
  C.foldl (init := τ) (fun τ l => τ.setLitFor (-l) extraBumps)

theorem setNegatedClause_eq_setNegatedClauseFor (τ : PPA) (C : IClause) :
    τ.setNegatedClause C = τ.setNegatedClauseFor C 0 := by
  simp [setNegatedClause, setNegatedClauseFor, setLit_eq_setLitFor]

@[simp]
theorem setNegatedClause_empty (τ : PPA) : τ.setNegatedClause #[] = τ := by
  simp [setNegatedClause]

@[simp]
theorem setNegatedClauseUntil_empty (τ : PPA) (gen : Nat) :
    τ.setNegatedClauseUntil #[] gen = τ := by
  simp [setNegatedClauseUntil]

@[simp]
theorem setNegatedClauseFor_empty (τ : PPA) (extraBumps : Nat) :
    τ.setNegatedClauseFor #[] extraBumps = τ := by
  simp [setNegatedClauseFor]


@[simp]
theorem setNegatedClauseFor_cons (τ : PPA) (l : ILit) (ls : List ILit) (bumps : Nat) :
    τ.setNegatedClauseFor { data := l :: ls } bumps =
      (τ.setLitFor (-l) bumps).setNegatedClauseFor { data := ls } bumps := by
  simp_rw [setNegatedClauseFor, Array.foldl_cons]

@[simp]
theorem setNegatedClause_cons (τ : PPA) (l : ILit) (ls : List ILit) :
    τ.setNegatedClause { data := l :: ls } =
      (τ.setLit (-l)).setNegatedClause { data := ls } := by
  rw [setNegatedClause_eq_setNegatedClauseFor]
  exact setNegatedClauseFor_cons _ _ _ _

/-! Assuming negation of clause, in an Exceptional way. -/

def assumeNegatedClause (τ : PPA) (C : IClause) : Except PPA PPA :=
  C.foldlM (init := τ) (fun τ l =>
    match τ.litValue? l with
    | none       => .ok <| τ.setLit (-l)
    | some false => .ok <| τ
    | some true  => .error τ)

-- Assumes the negation of the clause, where unset literals are set to false
-- (i.e., their negations are set to true) with the provided offset. If the
-- provided PPA satisfies the clause, then an error is thrown.
-- Any literal that is initially set to true, it's "bump" value is untouched.
def assumeNegatedClauseForM (τ : PPA) (C : IClause) (bumps : Nat) : Except PPA PPA :=
  C.foldlM (init := τ) (fun τ l =>
    match τ.litValue? l with
    | none       => .ok <| τ.setLitFor (-l) bumps
    | some false => .ok <| τ
    | some true  => .error τ)

-- A potentially faster implementation, that is still in the `Except` monad
-- but which uses a tail-recursive function.
def assumeNegatedClauseFor (τ : PPA) (C : IClause) (bumps : Nat) : Except PPA PPA :=
  let rec loop (i : Nat) (τ : PPA) : Except PPA PPA :=
    if h : i < Size.size C then
      let l := Seq.get C ⟨i, h⟩
      match τ.litValue? l with
      | none       => loop (i + 1) (τ.setLitFor (-l) bumps)
      | some false => loop (i + 1) τ
      | some true  => .error τ
    else
      .ok τ
  termination_by Size.size C - i
  loop 0 τ

section assumeNegatedClause

variable {τ τ' : PPA} {C : IClause} {bumps : Nat}

theorem assumeNegatedClause_eq_assumeNegatedClauseForM (τ : PPA) (C : IClause) :
    τ.assumeNegatedClause C = τ.assumeNegatedClauseForM C 0 := by
  simp [assumeNegatedClause, assumeNegatedClauseForM, setLit_eq_setLitFor]

@[simp]
theorem assumeNegatedClause_empty (τ : PPA) : τ.assumeNegatedClause #[] = .ok τ := by
  simp [assumeNegatedClause]; rfl

@[simp]
theorem assumedNegatedClauseFor_empty (τ : PPA) (bumps : Nat) :
    τ.assumeNegatedClauseForM #[] bumps = .ok τ := by
  simp [assumeNegatedClauseForM]; rfl

@[simp]
theorem assumeNegatedClauseForM_nil (τ : PPA) (bumps : Nat) :
    τ.assumeNegatedClauseForM { data := [] } bumps = .ok τ := by
  simp [assumeNegatedClauseForM]; rfl

def LawfulAssumeNegatedClauseFor (f : PPA → IClause → Nat → Except PPA PPA) : Prop :=
  ∀ (τ τ' : PPA) (C : IClause) (bumps : Nat),
    (f τ C bumps = .error τ' →
      τ.toPropFun ≤ C ∧ extended τ τ' bumps) ∧
    (f τ C bumps = .ok τ' →
      τ'.toPropFun = ↑τ ⊓ (↑C)ᶜ ∧ extended τ τ' bumps)

-- CC: There's an argument that these should be kept in separate lemmas, for usability.
--     There's also argument that they be combined into `Lawful`.
theorem assumeNegatedClauseForM_ok :
    (τ.assumeNegatedClauseForM C bumps) = .ok τ' →
      τ'.toPropFun = ↑τ ⊓ (↑C)ᶜ ∧ extended τ τ' bumps := by
  have ⟨C⟩ := C
  induction C generalizing τ with
  | nil => simp; rintro rfl; simp
  | cons l ls ih =>
    simp [assumeNegatedClauseForM, -Array.size_mk] at ih ⊢
    cases hτ : τ.litValue? l
    <;> simp [hτ]
    <;> rw [← inf_assoc]
    · intro h
      rw [← litValue?_negate_none_iff] at hτ
      rcases @ih (τ.setLitFor (-l) bumps) h with ⟨h₁, h₂⟩
      simp [toPropFun_setLit_of_none hτ] at h₁
      exact ⟨h₁, extended_trans (extended_setLitFor_of_none hτ _) h₂⟩
    · rename Bool => b
      cases b <;> intro h
      · have := @ih τ h
        rw [litValue?_false_iff_eq_inf] at hτ
        rwa [hτ] at this
      · contradiction

theorem assumeNegatedClauseForM_error :
    (τ.assumeNegatedClauseForM C bumps) = .error τ' →
      τ.toPropFun ≤ C ∧ extended τ τ' bumps := by
  have ⟨C⟩ := C
  induction C generalizing τ with
  | nil => simp [toPropFun_ne_bot]
  | cons l ls ih =>
    simp [assumeNegatedClauseForM, -Array.size_mk]
    cases hτ : τ.litValue? l
    <;> simp [hτ]
    <;> intro h
    · rcases ih h with ⟨ih₁, ih₂⟩
      rw [← litValue?_negate_none_iff] at hτ
      simp [toPropFun_setLit_of_none hτ] at ih₁
      exact ⟨sdiff_le_iff.mp ih₁, extended_trans (extended_setLitFor_of_none hτ _) ih₂⟩
    · rename Bool => b
      cases b
      · exact ⟨le_sup_of_le_right (ih h).1, (ih h).2⟩
      · rw [litValue?_true_iff] at hτ
        injection h; rename _ => h; subst h
        exact ⟨le_sup_of_le_left hτ, extended_refl _ _⟩

theorem assumeNegatedClauseForM_Lawful : LawfulAssumeNegatedClauseFor assumeNegatedClauseForM := by
  intro τ τ' C bumps
  exact ⟨assumeNegatedClauseForM_error, assumeNegatedClauseForM_ok⟩

-- Just to simplify things, we include the postcondition from aNCF_ok
theorem assumeNegatedClauseForM_reset_ok {τ τ' : PPA} {C : IClause} {bumps : Nat} :
  (τ.reset.assumeNegatedClauseForM C bumps) = .ok τ' →
    τ'.toPropFun = (C.toPropFun)ᶜ ∧ uniform τ' bumps := by
  intro h
  have := assumeNegatedClauseForM_ok h
  simp at this
  rcases this with ⟨h₁, h₂⟩
  exact ⟨h₁, uniform_of_extended_reset h₂⟩

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

theorem assumeNegatedClauseFor_eq_assumeNegatedClauseForM (τ : PPA) (C : IClause) (bumps : Nat) :
    τ.assumeNegatedClauseFor C bumps = τ.assumeNegatedClauseForM C bumps := by
  have ⟨C⟩ := C
  induction C generalizing τ with
  | nil =>
    simp [assumeNegatedClauseFor]
    unfold assumeNegatedClauseFor.loop
    simp [LeanColls.size]
  | cons l ls ih =>
    rw [assumeNegatedClauseFor, assumeNegatedClauseForM, Array.foldlM_cons,
      assumeNegatedClauseFor.loop]
    split <;> rename _ => hi
    · have h_get : Seq.get ({ data := l :: ls } : IClause) ⟨0, hi⟩ = l := rfl
      simp only [h_get]
      split <;> rename _ => hl
      · rw [assumeNegatedClauseFor.loop.cons]
        exact ih _
      · rw [assumeNegatedClauseFor.loop.cons]
        exact ih _
      · rfl
    · simp [LeanColls.size] at hi

theorem assumeNegatedClauseFor_Lawful : LawfulAssumeNegatedClauseFor assumeNegatedClauseFor := by
  intro τ τ' C bumps
  rw [assumeNegatedClauseFor_eq_assumeNegatedClauseForM]
  exact ⟨assumeNegatedClauseForM_error, assumeNegatedClauseForM_ok⟩

end assumeNegatedClause /- section -/

/-! ## Tautology checking -/

/- Check if the given clause is a tautology.
The current partial assignment is reset,
and the returned assignment is unspecified. -/
/-
def checkTauto (τ : PPA) (C : IClause) : PPA × { b : Bool // b ↔ C.toPropFun = ⊤ } :=
  go 0 ⟨τ.reset, by simp [Clause.toPropFun]⟩
where
  go (i : Nat) (τ : { τ : PPA // τ.toPropFunᶜ = Clause.toPropFun ⟨C.data.take i⟩ })
    : PPA × { b : Bool // b ↔ C.toPropFun = ⊤ } :=
  if hLt : i < C.size then
    let l := C[i]'hLt
    have hCl : Clause.toPropFun ⟨C.data.take (i+1)⟩ = Clause.toPropFun ⟨C.data.take i⟩ ⊔ l := by
      simp [List.take_succ, List.get?_eq_get hLt, Array.getElem_eq_data_get, τ.property]
      stop
      done
    match h : τ.val.litValue? l with
    | some true =>
      (τ.val, ⟨true, by
        have : τ.val.toPropFun ≤ l := litValue?_true_iff.mp h
        have : (↑l)ᶜ ≤ τ.val.toPropFunᶜ := compl_le_compl this
        have : (↑l)ᶜ ≤ C.toPropFun := by
          apply le_trans this
          rw [τ.property]
          apply C.toPropFun_take_le
        have : l ≤ C.toPropFun := C.toPropFun_getElem_le _
        have : ⊤ ≤ C.toPropFun := by
          rw [← sup_compl_eq_top (x := l.toPropFun)]
          apply sup_le <;> assumption
        simp only [top_le_iff.mp this]⟩)
    | some false =>
      go (i + 1) ⟨τ.val.setLit (-l), by
        rw [hCl]
        conv => rhs; lhs; rw [← τ.property]
        rw [← litValue?_negate_some_iff', Bool.not_false] at h
        rw [toPropFun_setLit_of_true h]
        rw [litValue?_negate_some_iff, Bool.not_true, litValue?_false_iff] at h
        rw [left_eq_sup, ← compl_le_compl_iff_le, compl_compl]
        exact h⟩
    | none =>
      go (i + 1) ⟨τ.val.setLit (-l), by
        have : (τ.val.setLit (-l)).toPropFun = τ.val.toPropFun ⊓ (-l).toPropFun := by
          apply toPropFun_setLit_of_none
          simp [τ.val.litValue?_negate l, h]
        simp [*, τ.property]⟩
  else
    (τ.val, ⟨false, by
      simp only [false_iff]
      intro h
      apply τ.val.toPropFun_ne_bot
      have hEq := τ.property
      have : C.data.length ≤ i := by rw [not_lt] at hLt; exact hLt
      have that : C = { data := C.data } := rfl
      simp_rw [C.data.take_length_le this, ← that, h, compl_eq_top] at hEq
      assumption⟩)
termination_by C.size - i -/

/-! ## Unit propagation -/

-- Cayden's alternate formulation of | extended
-- | extended      (l : ILit)
--                (τ' : PPA)
--                (h₁ : C.toPropFun ⊓ τ.toPropFun = τ'.toPropFun)
--                (h₂ : τ.litValue? l = none ∧ τ'.litValue? l = some true)

inductive DepUPResult (τ τ' : PPA) (C : IClause) where
  | contradiction (h : C.toPropFun ⊓ τ.toPropFun = ⊥)
  /-- Under `τ`, `C` became a unit clause `[l]`.
  The assignment was extended by that literal, i.e., `τ' = τ ⊓ l`. -/
  -- Note: I didn't prove that `C' = [l]`.
  | extended      (l : ILit) (hl : l ∈ C.data)
                  (h₁ : τ'.toPropFun = l.toPropFun ⊓ τ.toPropFun)
                  (h₂ : τ.toPropFun ⊓ C.toPropFun ≤ l.toPropFun)
  /-- Clause became satisfied. -/
  | satisfied
  /-- Clause did not become unit, and was not satisfied. -/
  | notUnit

/-- If `C` is satisfied by `τ`, return `satisfied`.
Otherwise compute the reduced clause `C' = {l ∈ C | ¬l ∉ τ}`.
If `C' = [u]` is a unit, extend `τ` by `u` and return `extended`.
If `C'` has become empty (is falsified), return `contradiction`.
If `C'` is not a unit and not falsified, return `notUnit`. -/
/-
def propagateUnit (τ : PPA) (C : IClause) : (τ' : PPA) × DepUPResult τ τ' C :=
  go 0 none Option.all_none (by simp only [not_lt_zero', IsEmpty.forall_iff, implies_true])
where
  /-- If `unit? = some u`, then `u` is a literal in the clause that is not falsified by `τ`.
  It may therefore be the case that `C' = [u]` -/
  go (i : Nat) (unit? : Option ILit) (hUnit : unit?.all fun u => u ∈ C.data ∧ τ.litValue? u = none)
      (hLits : ∀ (j : Fin C.size), j.val < i → unit? = some C[j] ∨ τ.toPropFun ≤ ((C.get j).toPropFun)ᶜ) :
      (τ' : PPA) × DepUPResult τ τ' C :=
    if hi : i < C.size then
      let l := C[i]'hi
      match hl : τ.litValue? l with
      | some true => ⟨τ, .satisfied⟩
      | some false =>
        -- TODO: lots of duplication here
        go (i+1) unit? hUnit (by
          intro j hj
          rcases Nat.lt_or_eq_of_le (Nat.lt_succ.mp hj) with hj | hj
          . exact hLits j hj
          . apply Or.inr
            apply litValue?_false_iff.mp
            simp [hj, hl])
      | none =>
        match hUnit : unit? with
        | .some u =>
          if hEq : u = l then
            go (i+1) (some l) (by simp [C.getElem_mem_data hi, hl]) (by
              intro j hj
              rcases Nat.lt_or_eq_of_le (Nat.lt_succ.mp hj) with hj | hj
              . exact hEq ▸ hLits j hj
              . apply Or.inl
                simp [hEq, hj])
          else
            ⟨τ, .notUnit⟩
        | .none =>
          go (i+1) (some l) (by simp [C.getElem_mem_data hi, hl]) (by
            intro j hj
            rcases Nat.lt_or_eq_of_le (Nat.lt_succ.mp hj) with hj | hj
            . apply Or.inr
              have := hLits j hj
              simpa using this
            . apply Or.inl
              simp [hj])
    else
      match unit? with
      | none =>
        ⟨τ, .contradiction (by
          apply le_bot_iff.mp
          apply entails_ext.mpr
          intro σ hσ
          exfalso
          rcases (satisfies_conj.mp hσ) with ⟨hσC, hστ⟩
          have ⟨l, hl, hσl⟩ := Clause.satisfies_iff.mp hσC
          rw [← Array.mem_data] at hl
          have ⟨k, hk⟩ := Array.mem_data_iff_exists_fin.mp hl
          rw [not_lt] at hi
          have := hLits k (lt_of_lt_of_le k.is_lt hi)
          simp only [false_or] at this
          have := entails_ext.mp this _ hστ
          rw [PropFun.satisfies_neg] at this
          exact this (hk ▸ hσl))⟩
      | some u =>
        ⟨τ.setLit u, .extended u
          (by simp at hUnit; tauto)
          (by
            simp at hUnit
            simp [τ.toPropFun_setLit_of_none hUnit.right, inf_comm])
          (by
            apply entails_ext.mpr
            intro σ hσ
            have ⟨hστ, hσC⟩ := satisfies_conj.mp hσ
            have ⟨l, hl, hσl⟩ := Clause.satisfies_iff.mp hσC
            rw [← Array.mem_data] at hl
            have ⟨i, hi⟩ := Array.mem_data_iff_exists_fin.mp hl
            have := i.is_lt
            have := hLits i (by linarith)
            rcases this with hEq | hτl
            . cases hEq
              rwa [hi]
            . exfalso
              exact (satisfies_neg.mp <| entails_ext.mp hτl _ hστ) (hi ▸ hσl))⟩
  termination_by C.size - i -/

-- Cayden's alternate implementation of unit propagation (TODO: Compare for efficiency)

-- Because unit prop might just want the result of C against τ, and no modify τ,
-- the updated assignment is not returned in the unit case.
inductive UPResult where
  | falsified
  | satisfied
  | unit (l : ILit)
  | multipleUnassignedLiterals

open Except UPResult

/-- Evaluates the literal under the partial substitution. Works in the Exception
    monad so that folding can return early if the clause is satisfied. -/
@[inline, always_inline]
def pevalM (τ : PPA) (unit? : Option ILit) (l : ILit) : Except Bool (Option ILit) :=
  match τ.litValue? l with
  | some true => error true
  | some false => ok unit?
  | none =>
    match unit? with
    | none => ok l
    | some u =>
      if u = l then ok unit?
      -- Assume tautology cannot occur in clause, so two unassiged literals exits early
      else error false

@[inline, always_inline, reducible]
def unitPropM_Except : Except Bool (Option ILit) → UPResult
  | ok none => falsified
  | ok (some lit) => unit lit
  | error true => satisfied
  | error false => multipleUnassignedLiterals

def unitPropM (τ : PPA) (C : IClause) : UPResult :=
  unitPropM_Except <| C.foldlM (pevalM τ) none

/-- A non-monadic implementation of unit propagation. It uses an internal
    tail-recursive function to iterate across the clause, so that early
    exit can be implemented.

    A start and end index can be provided, in case `C` is a larger structure. -/
def unitProp (τ : PPA) (C : IClause) : UPResult :=
  let rec go (i : Nat) (unit? : Option ILit) : UPResult :=
    if hi : i < Size.size C then
      -- This is essentially a clone of `pevalUP` above, except without an Exception monad
      let lit := Seq.get C ⟨i, hi⟩
      match τ.litValue? lit with
      | some true => .satisfied
      | some false => go (i + 1) unit?
      | none =>
        match unit? with
        | none => go (i + 1) (some lit)
        | some u =>
          if u = lit then go (i + 1) unit?
          else .multipleUnassignedLiterals
    else
      match unit? with
      | none => .falsified
      | some l => .unit l
  termination_by Size.size C - i
  go 0 none

/-- A unit propagation function `UP` is lawful if it returns `UPResult`s as expected. -/
def LawfulUP (UP : PPA → IClause → UPResult) : Prop :=
  ∀ (τ : PPA) (C : IClause),
    (UP τ C = .falsified → C.toPropFun ⊓ τ = ⊥)
  ∧ (∀ {l : ILit}, UP τ C = .unit l →
        l ∈ C ∧ τ.litValue? l = none ∧ C.toPropFun ⊓ τ = l.toPropFun ⊓ τ)
  ∧ (UP τ C = .satisfied → τ ≤ C.toPropFun)

theorem LawfulUP_of_eq_of_LawfulUP {UP UP' : PPA → IClause → UPResult} :
    (∀ τ C, UP τ C = UP' τ C) → LawfulUP UP → LawfulUP UP' := by
  intro h_eq h_lawful
  intro τ C
  have := h_lawful τ C
  rw [h_eq τ C] at this
  exact this

-- A lemma for when `pevalM` carries along `some` as its accumulator.
theorem foldlM_pevalM_some {τ : PPA} {unit : ILit} :
  τ.litValue? unit = none → ∀ (C : IClause),
    ((C.foldlM (pevalM τ) (some unit) = ok (some unit) ∧ C.toPropFun ⊓ τ ≤ unit)
    ∨ (C.foldlM (pevalM τ) (some unit) = error true ∧ τ ≤ C.toPropFun)
    ∨ (C.foldlM (pevalM τ) (some unit) = error false)) := by
  intro h_unit C
  have ⟨C⟩ := C
  induction C generalizing τ with
  | nil => simp [pure, Except.pure]
  | cons l ls ih =>
    simp only [Array.foldlM_cons, pevalM]
    match hl : τ.litValue? l with
    | none =>
      by_cases h_eq : l = unit
      · subst h_eq
        simp only [↓reduceIte]
        rcases ih h_unit with (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | h)
        · left; use h₁
          rw [Clause.toPropFun_cons, inf_sup_right]
          exact sup_le inf_le_left h₂
        · right; left; use h₁
          rw [Clause.toPropFun_cons]
          exact le_trans h₂ le_sup_right
        · right; right; use h
      · simp [Ne.symm h_eq]; right; right; rfl
    | some true =>
      right; left; use rfl
      rw [litValue?_true_iff] at hl
      rw [Clause.toPropFun_cons]
      exact le_trans hl le_sup_left
    | some false =>
      rcases ih h_unit with (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | h)
      · left; use h₁
        rw [litValue?_false_iff, le_compl_iff_inf_le_bot, le_bot_iff, inf_comm] at hl
        simp [Clause.toPropFun_cons, inf_sup_right, hl, h₂]
      · right; left; use h₁
        rw [Clause.toPropFun_cons]
        exact le_trans h₂ le_sup_right
      · right; right; use h

theorem unitPropM_LawfulUP : LawfulUP unitPropM := by
  rintro τ ⟨C⟩
  induction C generalizing τ with
  | nil => simp [unitPropM, pure, Except.pure]
  | cons l ls ih =>
    rw [unitPropM, unitPropM_Except, Array.foldlM_cons, pevalM]
    match hl : τ.litValue? l with
    | none =>
      -- CC: Can probably be cleaned up, since the lemma above uses ∨, not →
      rcases foldlM_pevalM_some hl { data := ls } with (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | h)
      · split
        <;> rename _ => h_cons
        <;> try simp only [bind, Except.bind, h₁] at h_cons
        <;> injection h_cons
        · contradiction
        · rename _ => h_lit; injection h_lit; rename _ => h_lit; subst h_lit
          simp [← Array.mem_data, hl, inf_sup_right, h₂]
      · split
        <;> rename _ => h_cons
        <;> try simp only [bind, Except.bind, h₁] at h_cons
        · simp; exact le_sup_of_le_right h₂
        · injection h_cons; contradiction
      · split
        <;> rename _ => h_cons
        <;> try simp only [bind, Except.bind, h] at h_cons
        <;> injection h_cons
        · contradiction
        · simp
    | some true =>
      rw [litValue?_true_iff] at hl
      simp [bind, Except.bind, le_sup_of_le_left hl]
    | some false =>
      simp only [bind, Except.bind]
      rcases ih τ with ⟨h₁, h₂, h₃⟩
      rw [litValue?_false_iff, le_compl_iff_inf_le_bot, le_bot_iff, inf_comm] at hl
      split
      <;> rename _ => h_cons
      · simp only [unitPropM, h_cons, forall_true_left] at h₁
        simp [inf_sup_right, hl, h₁]
      · rename ILit => l'
        simp only [unitPropM, h_cons, forall_true_left] at h₂
        replace h₂ := @h₂ l'
        simp at h₂
        rcases h₂ with ⟨h_mem, hτl', h_le⟩
        simp [← Array.mem_data] at h_mem ⊢
        use Or.inr h_mem, hτl'
        simp [inf_sup_right, h_le, hl]
      · simp only [unitPropM, h_cons, forall_true_left] at h₃
        simp [le_sup_of_le_right h₃]
      · simp

theorem unitProp.go.cons_aux (τ : PPA) (l : ILit) {ls : List ILit} {i j : Nat} :
    j = ls.length - i → unitProp.go τ { data := l :: ls } (i + 1) = unitProp.go τ { data := ls } i := by
  intro hj
  ext unit?
  induction j generalizing τ unit? i with
  | zero =>
    have : i ≥ ls.length := Nat.le_of_sub_eq_zero hj.symm
    unfold go
    simp [LeanColls.size, not_lt.mpr this, not_lt.mpr (succ_le_succ_iff.mpr this)]
  | succ j ih =>
    rw [succ_eq_add_one] at hj
    unfold go
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
    · apply @ih τ (i + 1)
      exact Nat.eq_sub_succ_of_succ_eq_sub hj
    · match unit? with
      | none =>
        apply @ih τ (i + 1)
        exact Nat.eq_sub_succ_of_succ_eq_sub hj
      | some u =>
        by_cases h_eq : u = Seq.get ({ data := ls } : IClause) ⟨i, hi⟩
        · simp only [h_eq]
          apply @ih τ (i + 1)
          exact Nat.eq_sub_succ_of_succ_eq_sub hj
        · simp only [h_eq]; rfl

theorem unitProp.go.cons (τ : PPA) (l : ILit) (ls : List ILit) (i : Nat) :
    unitProp.go τ { data := l :: ls } (i + 1) = unitProp.go τ { data := ls } i :=
  @unitProp.go.cons_aux τ l ls i (ls.length - i) rfl

theorem unitProp_eq_unitPropM_aux (τ : PPA) (C : IClause) (unit? : Option ILit) :
    unitProp.go τ C 0 unit? = unitPropM_Except (C.foldlM (pevalM τ) unit?) := by
  have ⟨C⟩ := C
  induction C generalizing τ unit? with
  | nil =>
    cases unit?
    <;> simp [unitProp.go, unitPropM_Except, LeanColls.size, pure, Except.pure]
  | cons l ls ih =>
    rw [unitProp.go, Array.foldlM_cons, pevalM]
    split <;> rename _ => hi
    · have h_get_l : Seq.get ({ data := l :: ls } : IClause) ⟨0, hi⟩ = l := rfl
      simp only [unitProp.go.cons]
      match hl : τ.litValue? l with
      | none =>
        match unit? with
        | none => exact ih τ (some l)
        | some u =>
          by_cases h_eq : u = l
          <;> simp only [h_get_l, h_eq]
          · exact ih τ (some l)
          · rfl
      | some true => rfl
      | some false => exact ih τ unit?
      done
    · simp [LeanColls.size] at hi

theorem unitProp_eq_unitPropM (τ : PPA) (C : IClause) :
    unitProp τ C = unitPropM τ C := by
  rw [unitProp, unitPropM]
  exact unitProp_eq_unitPropM_aux τ C none

theorem unitProp_LawfulUP : LawfulUP unitProp :=
  LawfulUP_of_eq_of_LawfulUP (fun τ C => (unitProp_eq_unitPropM τ C).symm) unitPropM_LawfulUP

end PPA
