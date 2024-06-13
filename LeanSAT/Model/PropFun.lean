/-
Copyright (c) 2024 The LeanSAT Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: Wojciech Nawrocki
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Lattice

import LeanSAT.Model.PropForm

namespace LeanSAT.Model

/-! # Propositional Formulas mod Equivalence

This file defines the type of propositional formulas over
a set `ν` of variables, quotiented by strong equivalence.

We show that they form a Boolean algebra
with ordering given by semantic entailment.
This allows us to use Mathlib's lattice notation & lemmas.

-/

open PropForm in
instance PropFun.setoid (ν : Type u) : Setoid (PropForm ν) where
  r := equivalent
  iseqv := {
    refl  := equivalent_refl
    symm  := equivalent.symm
    trans := equivalent.trans
  }

/-- A propositional function is a propositional formula up to semantic equivalence. -/
def PropFun ν := Quotient (PropFun.setoid ν)

namespace PropFun

/-- Applied backwards,
this reduces an equivalence between two syntactic formulas
to an equality between the functions they denote. -/
theorem exact {φ₁ φ₂ : PropForm ν} : @Eq (PropFun ν) ⟦φ₁⟧ ⟦φ₂⟧ → PropForm.equivalent φ₁ φ₂ :=
  Quotient.exact

theorem sound {φ₁ φ₂ : PropForm ν} : PropForm.equivalent φ₁ φ₂ → @Eq (PropFun ν) ⟦φ₁⟧ ⟦φ₂⟧ :=
  @Quotient.sound _ (PropFun.setoid ν) _ _

def var (x : ν) : PropFun ν := ⟦.var x⟧

instance : Coe ν (PropFun ν) := ⟨.var⟩

def tr : PropFun ν := ⟦.tr⟧

def fls : PropFun ν := ⟦.fls⟧

def neg : PropFun ν → PropFun ν :=
  Quotient.map (.neg ·) (by
    intro _ _ h τ
    simp [h τ])

def conj : PropFun ν → PropFun ν → PropFun ν :=
  Quotient.map₂ (.conj · ·) (by
    intro _ _ h₁ _ _ h₂ τ
    simp [h₁ τ, h₂ τ])

def disj : PropFun ν → PropFun ν → PropFun ν :=
  Quotient.map₂ (.disj · ·) (by
    intro _ _ h₁ _ _ h₂ τ
    simp [h₁ τ, h₂ τ])

def impl : PropFun ν → PropFun ν → PropFun ν :=
  Quotient.map₂ (.impl · ·) (by
    intro _ _ h₁ _ _ h₂ τ
    simp [h₁ τ, h₂ τ])

def biImpl : PropFun ν → PropFun ν → PropFun ν :=
  Quotient.map₂ (.biImpl · ·) (by
    intro _ _ h₁ _ _ h₂ τ
    simp [h₁ τ, h₂ τ])

/-! Evaluation -/

/-- The unique extension of `τ` from variables to propositional functions. -/
def eval (τ : PropAssignment ν) : PropFun ν → Bool :=
  Quotient.lift (PropForm.eval τ) (fun _ _ h => h τ)

@[simp]
theorem eval_mk (τ : PropAssignment ν) (φ : PropForm ν) :
    eval τ ⟦φ⟧ = φ.eval τ :=
  rfl

@[simp]
theorem eval_var (τ : PropAssignment ν) (x : ν) : eval τ (var x) = τ x := by
  simp [eval, var]

@[simp]
theorem eval_tr (τ : PropAssignment ν) : eval τ tr = true := by
  simp [eval, tr]

@[simp]
theorem eval_fls (τ : PropAssignment ν) : eval τ fls = false := by
  simp [eval, fls]

@[simp]
theorem eval_neg (τ : PropAssignment ν) (φ : PropFun ν) : eval τ (neg φ) = !(eval τ φ) := by
  have ⟨φ, h⟩ := Quotient.exists_rep φ
  simp [← h, eval, neg]

@[simp]
theorem eval_conj (τ : PropAssignment ν) (φ₁ φ₂ : PropFun ν) :
    eval τ (conj φ₁ φ₂) = (eval τ φ₁ && eval τ φ₂) := by
  have ⟨φ₁, h₁⟩ := Quotient.exists_rep φ₁
  have ⟨φ₂, h₂⟩ := Quotient.exists_rep φ₂
  simp [← h₁, ← h₂, conj, eval]

@[simp]
theorem eval_disj (τ : PropAssignment ν) (φ₁ φ₂ : PropFun ν) :
    eval τ (disj φ₁ φ₂) = (eval τ φ₁ || eval τ φ₂) := by
  have ⟨φ₁, h₁⟩ := Quotient.exists_rep φ₁
  have ⟨φ₂, h₂⟩ := Quotient.exists_rep φ₂
  simp [← h₁, ← h₂, eval, disj]

@[simp]
theorem eval_impl (τ : PropAssignment ν) (φ₁ φ₂ : PropFun ν) :
    eval τ (impl φ₁ φ₂) = (eval τ φ₁) ⇨ (eval τ φ₂) := by
  have ⟨φ₁, h₁⟩ := Quotient.exists_rep φ₁
  have ⟨φ₂, h₂⟩ := Quotient.exists_rep φ₂
  simp [← h₁, ← h₂, eval, impl]

@[simp]
theorem eval_biImpl (τ : PropAssignment ν) (φ₁ φ₂ : PropFun ν) :
    eval τ (biImpl φ₁ φ₂) = (eval τ φ₁ = eval τ φ₂) := by
  have ⟨φ₁, h₁⟩ := Quotient.exists_rep φ₁
  have ⟨φ₂, h₂⟩ := Quotient.exists_rep φ₂
  simp [← h₁, ← h₂, eval, biImpl]

/-! Satisfying assignments -/

def satisfies (τ : PropAssignment ν) (φ : PropFun ν) : Prop :=
  φ.eval τ = true

/-- This instance is scoped so that when `PropFun` is open,
`τ ⊨ φ` implies `φ : PropFun _` via the `outParam`. -/
scoped instance : SemanticEntails (PropAssignment ν) (PropFun ν) where
  entails := PropFun.satisfies

open SemanticEntails renaming entails → sEntails

instance (τ : PropAssignment ν) (φ : PropFun ν) : Decidable (τ ⊨ φ) :=
  match h : φ.eval τ with
    | true => isTrue h
    | false => isFalse fun h' => nomatch h.symm.trans h'

@[ext]
theorem ext : (∀ (τ : PropAssignment ν), τ ⊨ φ₁ ↔ τ ⊨ φ₂) → φ₁ = φ₂ := by
  have ⟨φ₁, h₁⟩ := Quotient.exists_rep φ₁
  have ⟨φ₂, h₂⟩ := Quotient.exists_rep φ₂
  simp only [← h₁, ← h₂]
  intro h
  apply Quotient.sound ∘ PropForm.equivalent_ext.mpr
  apply h

theorem ext_iff {φ₁ φ₂ : PropFun ν}
  : φ₁ = φ₂ ↔ (∀ (τ : PropAssignment ν), τ ⊨ φ₁ ↔ τ ⊨ φ₂) :=
  ⟨fun h _ => iff_of_eq (congrArg _ h), ext⟩

/-! Semantic entailment -/

instance {τ : PropAssignment ν} : Decidable (τ ⊨ φ) :=
  inferInstanceAs (Decidable (φ.eval τ = true))

def entails (φ₁ φ₂ : PropFun ν) : Prop :=
  ∀ (τ : PropAssignment ν), φ₁.eval τ ≤ φ₂.eval τ

@[simp]
theorem entails_mk {φ₁ φ₂ : PropForm ν} : entails ⟦φ₁⟧ ⟦φ₂⟧ ↔ PropForm.entails φ₁ φ₂ :=
  ⟨id, id⟩

theorem entails_ext {φ₁ φ₂ : PropFun ν} :
    entails φ₁ φ₂ ↔ (∀ (τ : PropAssignment ν), τ ⊨ φ₁ → τ ⊨ φ₂) := by
  have ⟨φ₁, h₁⟩ := Quotient.exists_rep φ₁
  have ⟨φ₂, h₂⟩ := Quotient.exists_rep φ₂
  simp only [← h₁, ← h₂, entails_mk]
  exact PropForm.entails_ext

theorem entails_refl (φ : PropFun ν) : entails φ φ :=
  fun _ => le_rfl
theorem entails.trans : entails φ₁ φ₂ → entails φ₂ φ₃ → entails φ₁ φ₃ :=
  fun h₁ h₂ τ => le_trans (h₁ τ) (h₂ τ)
theorem entails.antisymm : entails φ ψ → entails ψ φ → φ = ψ := by
  intro h₁ h₂
  ext τ
  exact ⟨entails_ext.mp h₁ τ, entails_ext.mp h₂ τ⟩

theorem entails_tr (φ : PropFun ν) : entails φ tr :=
  fun _ => le_top
theorem fls_entails (φ : PropFun ν) : entails fls φ :=
  fun _ => bot_le

theorem entails_disj_left (φ₁ φ₂ : PropFun ν) : entails φ₁ (disj φ₁ φ₂) :=
  fun _ => by simp only [eval_disj]; exact le_sup_left
theorem entails_disj_right (φ₁ φ₂ : PropFun ν) : entails φ₂ (disj φ₁ φ₂) :=
  fun _ => by simp only [eval_disj]; exact le_sup_right
theorem disj_entails : entails φ₁ φ₃ → entails φ₂ φ₃ → entails (disj φ₁ φ₂) φ₃ :=
  fun h₁ h₂ τ => by simp only [eval_disj]; exact sup_le (h₁ τ) (h₂ τ)

theorem conj_entails_left (φ₁ φ₂ : PropFun ν) : entails (conj φ₁ φ₂) φ₁ :=
  fun _ => by simp only [eval_conj]; exact inf_le_left
theorem conj_entails_right (φ₁ φ₂ : PropFun ν) : entails (conj φ₁ φ₂) φ₂ :=
  fun _ => by simp only [eval_conj]; exact inf_le_right
theorem entails_conj : entails φ₁ φ₂ → entails φ₁ φ₃ → entails φ₁ (conj φ₂ φ₃) :=
  fun h₁ h₂ τ => by simp only [eval_conj]; exact le_inf (h₁ τ) (h₂ τ)

theorem entails_disj_conj (φ₁ φ₂ φ₃ : PropFun ν) :
    entails (conj (disj φ₁ φ₂) (disj φ₁ φ₃)) (disj φ₁ (conj φ₂ φ₃)) :=
  fun _ => by simp only [eval_conj, eval_disj]; exact le_sup_inf

theorem conj_neg_entails_fls (φ : PropFun ν) : entails (conj φ (neg φ)) fls :=
  fun τ => by simp only [eval_conj, eval_neg]; exact BooleanAlgebra.inf_compl_le_bot (eval τ φ)

theorem tr_entails_disj_neg (φ : PropFun ν) : entails tr (disj φ (neg φ)) :=
  fun τ => by simp only [eval_disj, eval_neg]; exact BooleanAlgebra.top_le_sup_compl (eval τ φ)

theorem impl_eq (φ ψ : PropFun ν) : impl φ ψ = disj ψ (neg φ) := by
  ext τ
  simp only [sEntails, satisfies, eval_impl, eval_disj, eval_neg]
  rfl

/-! From this point onwards we use lattice notation for `PropFun`s
in order to get the mathlib laws for free. -/

instance : BooleanAlgebra (PropFun ν) where
  le := entails
  top := tr
  bot := fls
  compl := neg
  sup := disj
  inf := conj
  himp := impl
  le_refl := entails_refl
  le_trans := @entails.trans _
  le_antisymm := @entails.antisymm _
  le_top := entails_tr
  bot_le := fls_entails
  le_sup_left := entails_disj_left
  le_sup_right := entails_disj_right
  sup_le _ _ _ := disj_entails
  inf_le_left := conj_entails_left
  inf_le_right := conj_entails_right
  le_inf _ _ _ := entails_conj
  le_sup_inf := entails_disj_conj
  inf_compl_le_bot := conj_neg_entails_fls
  top_le_sup_compl := tr_entails_disj_neg
  himp_eq := impl_eq

@[simp]
theorem satisfies_mk {τ : PropAssignment ν} {φ : PropForm ν} : τ ⊨ ⟦φ⟧ ↔ (open PropForm in τ ⊨ φ) :=
  ⟨id, id⟩

@[simp]
theorem satisfies_var {τ : PropAssignment ν} {x : ν} : τ ⊨ var x ↔ τ x := by
  simp [sEntails, satisfies]

@[simp]
theorem satisfies_set {τ : PropAssignment ν} [DecidableEq ν] : τ.set x ⊤ ⊨ var x := by
  simp

@[simp]
theorem satisfies_tr {τ : PropAssignment ν} : τ ⊨ ⊤ :=
  by simp [sEntails, satisfies, Top.top]

@[simp]
theorem not_satisfies_fls {τ : PropAssignment ν} : τ ⊭ ⊥ :=
  fun h => nomatch h

@[simp]
theorem satisfies_neg {τ : PropAssignment ν} : τ ⊨ (φᶜ) ↔ τ ⊭ φ := by
  simp [sEntails, satisfies, HasCompl.compl]

@[simp]
theorem satisfies_conj {τ : PropAssignment ν} : τ ⊨ φ₁ ⊓ φ₂ ↔ τ ⊨ φ₁ ∧ τ ⊨ φ₂ := by
  simp [sEntails, satisfies, Inf.inf]

@[simp]
theorem satisfies_disj {τ : PropAssignment ν} : τ ⊨ φ₁ ⊔ φ₂ ↔ τ ⊨ φ₁ ∨ τ ⊨ φ₂ := by
  simp [sEntails, satisfies, Sup.sup]

@[simp]
theorem satisfies_impl {τ : PropAssignment ν} : τ ⊨ φ₁ ⇨ φ₂ ↔ (τ ⊨ φ₁ → τ ⊨ φ₂) := by
  simp only [sEntails, satisfies, eval_impl, HImp.himp]
  cases (eval τ φ₁) <;> simp [himp_eq]

theorem satisfies_impl' {τ : PropAssignment ν} : τ ⊨ φ₁ ⇨ φ₂ ↔ τ ⊭ φ₁ ∨ τ ⊨ φ₂ := by
  simp only [sEntails, satisfies, eval_impl, HImp.himp]
  cases (eval τ φ₁) <;> simp [himp_eq]

@[simp]
theorem satisfies_biImpl {τ : PropAssignment ν} : τ ⊨ biImpl φ₁ φ₂ ↔ (τ ⊨ φ₁ ↔ τ ⊨ φ₂) := by
  simp [sEntails, satisfies]

instance : Nontrivial (PropFun ν) where
  exists_pair_ne := by
    use ⊤, ⊥
    intro h
    have : ∀ (τ : PropAssignment ν), τ ⊨ ⊥ ↔ τ ⊨ ⊤ := fun _ => h ▸ Iff.rfl
    simp only [not_satisfies_fls, satisfies_tr, iff_true] at this
    apply this (fun _ => true)

theorem eq_top_iff {φ : PropFun ν} : φ = ⊤ ↔ ∀ (τ : PropAssignment ν), τ ⊨ φ :=
  ⟨fun h => by simp [h], fun h => by ext; simp [h]⟩

theorem eq_bot_iff {φ : PropFun ν} : φ = ⊥ ↔ ∀ (τ : PropAssignment ν), τ ⊭ φ :=
  ⟨fun h => by simp [h], fun h => by ext; simp [h]⟩

theorem biImpl_eq_impls (φ ψ : PropFun ν) : biImpl φ ψ = (φ ⇨ ψ) ⊓ (ψ ⇨ φ) := by
  ext τ
  aesop

@[simp] theorem biImpl_top_left (φ : PropFun ν) : biImpl ⊤ φ = φ := by
  ext τ; aesop
@[simp] theorem biImpl_top_right (φ : PropFun ν) : biImpl φ ⊤ = φ := by
  ext τ; aesop

@[simp] theorem biImpl_bot_left (φ : PropFun ν) : biImpl ⊥ φ = φᶜ := by
  ext τ; aesop
@[simp] theorem biImpl_bot_right (φ : PropFun ν) : biImpl φ ⊥ = φᶜ := by
  ext τ; aesop

-- CC: Some additional simplifications, for reasoning about ≤
theorem inf_le_iff_compl_sup {φ₁ φ₂ φ₃ : PropFun ν} : φ₁ ⊓ φ₂ ≤ φ₃ ↔ φ₁ ≤ φ₂ᶜ ⊔ φ₃ :=
  BooleanAlgebra.inf_le_iff_le_compl_sup

theorem inf_compl_le_iff_le_sup {φ₁ φ₂ φ₃ : PropFun ν} : φ₁ ⊓ φ₂ᶜ ≤ φ₃ ↔ φ₁ ≤ φ₂ ⊔ φ₃ :=
  BooleanAlgebra.inf_compl_le_iff_le_sup

theorem le_iff_inf_compl_le_bot {φ₁ φ₂ : PropFun ν} : φ₁ ≤ φ₂ ↔ φ₁ ⊓ φ₂ᶜ ≤ ⊥ :=
  BooleanAlgebra.le_iff_inf_compl_le_bot

theorem le_compl_iff_inf_le_bot {φ₁ φ₂ : PropFun ν} : φ₁ ≤ φ₂ᶜ ↔ φ₁ ⊓ φ₂ ≤ ⊥ :=
  BooleanAlgebra.le_compl_iff_inf_le_bot

theorem le_iff_inf_compl_eq_bot {φ₁ φ₂ : PropFun ν} : φ₁ ≤ φ₂ ↔ φ₁ ⊓ φ₂ᶜ = ⊥ :=
  BooleanAlgebra.le_iff_inf_compl_eq_bot

theorem le_compl_iff_inf_eq_bot {φ₁ φ₂ : PropFun ν} : φ₁ ≤ φ₂ᶜ ↔ φ₁ ⊓ φ₂ = ⊥ :=
  BooleanAlgebra.le_compl_iff_inf_eq_bot

theorem ne_top_left_of_disj_ne_top {φ₁ φ₂ : PropFun ν} : φ₁ ⊔ φ₂ ≠ ⊤ → φ₁ ≠ ⊤ := by
  intro h; aesop

theorem ne_top_right_of_disj_ne_top {φ₁ φ₂ : PropFun ν} : φ₁ ⊔ φ₂ ≠ ⊤ → φ₂ ≠ ⊤ := by
  intro h; aesop

theorem ne_top_of_disj_ne_top {φ₁ φ₂ : PropFun ν} : φ₁ ⊔ φ₂ ≠ ⊤ → φ₁ ≠ ⊤ ∧ φ₂ ≠ ⊤ :=
  fun h => ⟨ne_top_left_of_disj_ne_top h, ne_top_right_of_disj_ne_top h⟩

theorem var.inj [DecidableEq ν] : (var (ν := ν)).Injective := by
  intro v1 v2 h
  rw [ext_iff] at h
  have := h (fun v => v = v1)
  aesop

@[simp]
theorem var_eq_var [DecidableEq ν] (v v' : ν) : var v = var v' ↔ v = v' := by
  constructor
  · intro; apply var.inj; assumption
  · aesop

theorem eq_compl_iff_neq {φ₁ φ₂ : PropFun ν} : φ₁ = (φ₂)ᶜ → φ₁ ≠ φ₂ := by
  rintro rfl h; rw [ext_iff] at h; simp at h

@[simp]
theorem var_ne_var_compl [DecidableEq ν] (v1 v2 : ν) : var v1 ≠ (var v2)ᶜ := by
  intro h
  rw [ext_iff] at h
  have := h (fun v => v = v1 || v = v2)
  simp at this

@[simp]
theorem var_compl_ne_var [DecidableEq ν] (v1 v2 : ν) : (var v1)ᶜ ≠ (var v2) := by
  intro h
  rw [ext_iff] at h
  have := h (fun v => v = v1 || v = v2)
  simp at this

theorem var_ne_top (v : ν) : var v ≠ ⊤ := by
  simp [ext_iff]; exact ⟨(fun _ => false), rfl⟩

theorem var_ne_bot (v : ν) : var v ≠ ⊥ := by
  simp [ext_iff]; exact ⟨(fun _ => true), rfl⟩

/-! Lemmas to push `Quotient.mk` inwards. -/

-- TODO: custom simp set?

@[simp]
theorem mk_var (x : ν) : ⟦.var x⟧ = var x := rfl

@[simp]
theorem mk_tr : @Eq (PropFun ν) ⟦.tr⟧ ⊤ := rfl

@[simp]
theorem mk_fls : @Eq (PropFun ν) ⟦.fls⟧ ⊥ := rfl

@[simp]
theorem mk_neg (φ : PropForm ν) : @Eq (PropFun ν) ⟦.neg φ⟧ (⟦φ⟧)ᶜ := rfl

@[simp]
theorem mk_conj (φ₁ φ₂ : PropForm ν) : @Eq (PropFun ν) ⟦.conj φ₁ φ₂⟧ (⟦φ₁⟧ ⊓ ⟦φ₂⟧) := rfl

@[simp]
theorem mk_disj (φ₁ φ₂ : PropForm ν) : @Eq (PropFun ν) ⟦.disj φ₁ φ₂⟧ (⟦φ₁⟧ ⊔ ⟦φ₂⟧) := rfl

@[simp]
theorem mk_impl (φ₁ φ₂ : PropForm ν) : @Eq (PropFun ν) ⟦.impl φ₁ φ₂⟧ (⟦φ₁⟧ ⇨ ⟦φ₂⟧) := rfl

@[simp]
theorem mk_biImpl (φ₁ φ₂ : PropForm ν) : @Eq (PropFun ν) ⟦.biImpl φ₁ φ₂⟧ (biImpl ⟦φ₁⟧ ⟦φ₂⟧) := rfl

/-! ### All/any -/

def all (a : Multiset (PropFun ν)) : PropFun ν :=
  Multiset.inf a

def any (a : Multiset (PropFun ν)) : PropFun ν :=
  Multiset.sup a

@[simp] theorem satisfies_all (a : Multiset (PropFun ν)) (τ : PropAssignment ν)
  : τ ⊨ all a ↔ ∀ i ∈ a, τ ⊨ i := by
  induction a using Multiset.induction with
  | empty => simp [all]
  | cons => simp_all [all]

@[simp] theorem satisfies_any (a : Multiset (PropFun ν)) (τ : PropAssignment ν)
  : τ ⊨ any a ↔ ∃ i ∈ a, τ ⊨ i := by
  induction a using Multiset.induction with
  | empty => simp [any]
  | cons => simp_all [any]

@[simp] theorem any_zero : any (0 : Multiset (PropFun ν)) = ⊥ := by simp [any]
@[simp] theorem all_zero : all (0 : Multiset (PropFun ν)) = ⊤ := by simp [all]

/-! # satisfiable and eqsat -/

def satisfiable (φ : PropFun ν) : Prop :=
  ∃ (τ : PropAssignment ν), τ ⊨ φ

def eqsat (φ₁ φ₂ : PropFun ν) : Prop :=
  satisfiable φ₁ ↔ satisfiable φ₂

@[symm]
def eqsat.symm {φ₁ φ₂ : PropFun ν} : eqsat φ₁ φ₂ ↔ eqsat φ₂ φ₁ :=
  ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

@[trans]
def eqsat.trans {φ₁ φ₂ φ₃ : PropFun ν} : eqsat φ₁ φ₂ → eqsat φ₂ φ₃ → eqsat φ₁ φ₃ :=
  fun h₁ h₂ => ⟨fun h => h₂.1 (h₁.1 h), fun h => h₁.2 (h₂.2 h)⟩

def bot_not_satisfiable : ¬satisfiable (⊥ : PropFun ν) := by
  intro h
  rcases h with ⟨τ, h⟩
  exact nomatch h

theorem not_satisfiable_iff_eq_bot {F : PropFun ν} : ¬satisfiable F ↔ F = ⊥ := by
  simp [satisfiable]; aesop

theorem eq_bot_of_eqsat {F C : PropFun ν} : eqsat F (F ⊓ C) → (F ⊓ C) = ⊥ → F = ⊥ := by
  rintro ⟨h₁, _⟩ hFC
  rw [hFC] at h₁
  have := mt h₁ bot_not_satisfiable
  exact not_satisfiable_iff_eq_bot.mp (mt h₁ bot_not_satisfiable)

theorem eqsat_of_entails {F C : PropFun ν} : F ≤ C → eqsat F (F ⊓ C) := by
  intro h_entails
  simp only [eqsat, satisfiable, ge_iff_le, satisfies_conj]
  exact ⟨fun ⟨τ, hτ⟩ => ⟨τ, hτ, h_entails τ hτ⟩, fun ⟨τ, hτ, _⟩ => ⟨τ, hτ⟩⟩

namespace Notation
open PropForm.Notation

declare_syntax_cat propfun

syntax "[propfun| " propfun " ]" : term

syntax:max "{ " term:45 " }" : propfun
syntax:max "(" propfun ")" : propfun

syntax:40 " ¬" propfun:41 : propfun
syntax:35 propfun:36 " ∧ " propfun:35 : propfun
syntax:30 propfun:31 " ∨ " propfun:30 : propfun
syntax:25 propfun:26 " → " propfun:25 : propfun
syntax:20 propfun:21 " ↔ " propfun:20 : propfun

macro_rules
| `([propfun| {$t:term} ]) => `(show PropFun _ from $t)
| `([propfun| ($f:propfun) ]) => `([propfun| $f ])
| `([propfun| ¬ $f:propfun ]) => `(([propfun| $f ])ᶜ)
| `([propfun| $f1 ∧ $f2 ]) => `([propfun| $f1 ] ⊓ [propfun| $f2 ])
| `([propfun| $f1 ∨ $f2 ]) => `([propfun| $f1 ] ⊔ [propfun| $f2 ])
| `([propfun| $f1 → $f2 ]) => `([propfun| $f1 ] ⇨ [propfun| $f2 ])
| `([propfun| $f1 ↔ $f2 ]) => `(PropFun.biImpl [propfun| $f1 ] [propfun| $f2 ])

example (a b c : ν) : PropFun ν :=
  [propfun| {a} ∧ ¬{b} ∧ {c} ]

end Notation
