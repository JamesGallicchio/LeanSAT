/-
Copyright (c) 2024 The LeanSAT Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: Wojciech Nawrocki
-/

import Mathlib.Tactic.Linarith
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Setoid.Basic

/-! Stuff that seems like it should be in std or mathlib. -/

/-! Std.Logic or Std.Bool? -/

@[simp] theorem Bool.bnot_eq_bnot (a b : Bool) :
  ((!a) = !b) ↔ (a = b) := by cases a <;> cases b <;> decide
@[simp] theorem Bool.eq_true_iff_eq_true (a b : Bool) :
  (a = true ↔ b = true) ↔ (a = b) := by cases a <;> cases b <;> decide
@[simp] theorem Bool.eq_false_iff_eq_false (a b : Bool) :
  (a = false ↔ b = false) ↔ (a = b) := by cases a <;> cases b <;> decide

theorem Bool.bnot_eq (a b : Bool) :
  ((!a) = b) ↔ ¬(a = b) := by cases a <;> cases b <;> decide
theorem Bool.eq_bnot (a b : Bool) :
  (a = (!b)) ↔ ¬(a = b) := by cases a <;> cases b <;> decide

/-- Notation typeclass for semantic entailment `⊨`. -/
class SemanticEntails (α : Type u) (β : outParam $ Type v) where
  entails : α → β → Prop

infix:51 " ⊨ " => SemanticEntails.entails
infix:51 " ⊭ " => fun M φ => ¬(M ⊨ φ)

/-! Nat -/

theorem Nat.eq_or_lt_of_lt_succ {m n : Nat} : m < n + 1 → m = n ∨ m < n := by
  intro h
  rcases eq_or_lt_of_le (Nat.le_of_lt_succ h) with (rfl | h)
  · exact Or.inl rfl
  · exact Or.inr h

-- Mostly used for backwards-induction proofs
theorem Nat.eq_sub_succ_of_succ_eq_sub {k n m : Nat} : k + 1 = n - m → k = n - (m + 1) := by
  rw [← Nat.sub_sub]
  intro hk
  rw [← hk, Nat.add_sub_cancel]

/-! Int -/

theorem Int.eq_zero_of_lt_neg_iff_lt (i : Int) : (0 < -i ↔ 0 < i) → i = 0 := by
  intro h
  by_cases hLt : 0 < i
  . have := h.mpr hLt; linarith
  . have : ¬ 0 < -i := fun h₂ => hLt (h.mp h₂); linarith

instance : HAdd PNat Nat PNat where
  hAdd | ⟨a,h⟩, b => ⟨a+b, Nat.add_pos_left h _⟩

/- Credit Kyle Miller, Timo Carlin-Burns, Eric Weiser for these lemmas: -/
section Quotients
def Quotient.toTrunc {α : Sort*} [s : Setoid α] (q : Quotient s) : Trunc { a // ⟦a⟧ = q } :=
  Quotient.recOn q (fun a ↦ Trunc.mk ⟨a, rfl⟩) (fun _ _ _ ↦ Trunc.eq ..)

def Quotient.elim {α β : Sort*} [s : Setoid α] (q : Quotient s)
    (f : (a : α) → ⟦a⟧ = q → β) (h : ∀ a b ha hb, f a ha = f b hb)
    : β :=
  q.toTrunc.lift (fun x ↦ f x.val x.prop) (fun _ _ ↦ h ..)

theorem Quotient.elim_mk {α β : Sort*} [s : Setoid α] (a : α)
    (f : (b : α) → (⟦b⟧ : Quotient s) = ⟦a⟧ → β) (h : ∀ a b ha hb, f a ha = f b hb)
  : ⟦a⟧.elim f h = f a rfl := by
  simp [elim]
  apply Trunc.lift_mk

def Multiset.elim {α β : Type*} (s : Multiset α) (f : (L : List α) → L = s → β)
    (h : ∀ a b ha hb, f a ha = f b hb) : β :=
  Quotient.elim s f h

theorem Multiset.elim_mk {α β : Type*} (L : List α)
    (f : (L' : List α) → (⟦L'⟧ : Multiset α) = ⟦L⟧ → β) (h : ∀ a b ha hb, f a ha = f b hb)
  : elim ⟦L⟧ f h = f L rfl := by
  simp [elim]
  apply Trunc.lift_mk

theorem Multiset.elim_eq_forall {α β : Type*} {s : Multiset α} {f : (L : List α) → L = s → β} {h}
    (motive : Prop) (hmotive : ∀ {L hL}, Multiset.elim s f h = f L hL → motive) : motive := by
  induction s using Quotient.inductionOn with | _ L =>
  exact hmotive rfl

-- CC: Can probably be stated more elegantly / might not want to Mathlib
theorem Fin.succFin_of_ne {n : Nat} {i : Fin n} :
  i.val + 1 ≠ n → i.val + 1 < n := by
  intro hi
  have := i.isLt
  rcases eq_or_lt_of_le (Nat.succ_le_of_lt this) with (h | h)
  · exact absurd h hi
  · exact h

abbrev Finset.elim {α β : Type*} (s : Finset α) (f : (L : List α) → L = s.val → β)
    (h : ∀ a b ha hb, f a ha = f b hb) : β :=
  Multiset.elim s.val f h

theorem Finset.elim_eq_forall {α β : Type*} {s : Finset α} {f : (L : List α) → L = s.val → β} {h}
    (motive : Prop) (hmotive : ∀ {L hL}, Finset.elim s f h = f L hL → motive) : motive := by
  rcases s with ⟨s,h⟩
  induction s using Quotient.inductionOn with | _ L =>
  exact hmotive rfl

/-- Given a function over the (complete set of distinct) elements of a fintype,
  and a proof the function is constant, produce the value of that function. -/
def Fintype.elim_elems [Fintype V]
      (f : (L : List V) → (∀ v, v ∈ L) → List.Nodup L → β)
      (h : ∀ L1 h1 h11 L2 h2 h22, f L1 h1 h11 = f L2 h2 h22)
      : β :=
  Fintype.elems.elim
    (fun L hL =>
      f L
        (by intro; rw [←Multiset.mem_coe, hL]; simp [Fintype.complete])
        (by rw [←Multiset.coe_nodup, hL]; apply Finset.nodup))
    (by intros; apply h)

theorem Fintype.elim_elems_eq_forall [Fintype V] (f : (L : List V) → _ → _ → β) {h} {C : Prop}
    (h' : ∀ L h1 h2, Fintype.elim_elems f h = f L h1 h2 → C)
    : C
  := by
  apply Multiset.elim_eq_forall (motive := C)
  intro L hL hM
  apply h'
  apply hM

end Quotients

theorem Finset.biUnion_union [DecidableEq α] [DecidableEq β] (s1 s2 : Finset α) (f : α → Finset β)
  : Finset.biUnion (s1 ∪ s2) f = ((Finset.biUnion s1 f) ∪ Finset.biUnion s2 f)
  := by
  ext b
  simp only [mem_biUnion, mem_union]
  constructor
  · rintro ⟨a,b|b⟩
    · refine Or.inl ⟨a,?_⟩
      simp only [and_self, *]
    · refine Or.inr ⟨a,?_⟩
      simp only [and_self, *]
  · rintro (⟨a,b,c⟩|⟨a,b,c⟩)
      <;> refine ⟨a, ?_⟩
    · simp only [and_self, true_or, *]
    · simp only [and_self, or_true, *]

def Finset.getUnique (xs : Finset α) (h : ∃ x, xs = {x}) : α :=
  xs.elim (fun L _hL =>
    match L with
    | [] => by
      exfalso; cases h; simp_all
      apply Multiset.not_mem_zero
      rw [_hL]
      apply Multiset.mem_singleton.mpr
      rfl
    | x::_ => x
    ) (by
    intro a b ha hb
    rcases h with ⟨x,rfl⟩
    simp at ha hb
    cases ha; cases hb
    simp)

@[simp] theorem Finset.getUnique_eq (xs : Finset α) (h) (v)
  : Finset.getUnique xs h = v ↔ xs = {v}
  := by
  rcases h with ⟨x,rfl⟩
  simp [getUnique]
  apply elim_eq_forall
  intro L hL heq
  rw [heq]; clear heq
  simp at hL; cases hL
  simp

@[simp] theorem Finset.getUnique_mem (xs : Finset α) (h) (y : Finset α)
  : Finset.getUnique xs h ∈ y ↔ xs ⊆ y := by
  generalize hv : getUnique xs h = v
  simp at hv
  simp [hv]

open List in
theorem List.Perm.find?_unique {f : α → Bool}
    (hunique : ∀ a1 a2, f a1 → f a2 → a1 = a2) (h : a ~ b)
  : a.find? f = b.find? f := by
  induction h with
  | nil => simp
  | cons => simp [find?]; split <;> simp [*]
  | swap =>
    simp [find?]; split <;> split <;> simp
    apply hunique; repeat assumption
  | trans =>
    simp_all

def Multiset.find? (f : α → Bool) (xs : Multiset α)
      (h : ∀ a1 a2, f a1 = true → f a2 = true → a1 = a2) : Option α :=
  xs.lift (·.find? f) (by
    intro a b perm
    simp
    apply perm.find?_unique h
  )

@[simp] theorem Multiset.find?_eq_some (xs : Multiset α)
  : xs.find? f h = some x ↔ x ∈ xs ∧ f x := by
  have ⟨L,hL⟩ := xs.exists_rep; cases hL
  simp [-quot_mk_to_coe, find?]
  simp
  constructor
  · intro h
    simp [List.find?_some h, List.find?_mem h]
  · rintro ⟨h1,h2⟩
    induction h1 <;> simp [List.find?, *]
    split
    · simp; apply h <;> assumption
    · rfl

@[simp] theorem Multiset.find?_eq_none (xs : Multiset α)
  : xs.find? f h = none ↔ ∀ x ∈ xs, f x = false := by
  have ⟨L,hL⟩ := xs.exists_rep; cases hL
  simp only [find?, Quotient.lift_mk, List.find?_eq_none, Bool.not_eq_true]
  simp only [quot_mk_to_coe, mem_coe]

@[simp] theorem Setoid.prod.pair {a1 a2 : α} {b1 b2 : β} [sa : Setoid α] [sb : Setoid β]
  : @HasEquiv.Equiv _ (@instHasEquiv _ (Setoid.prod sa sb)) (a1,b1) (a2,b2)
    ↔ a1 ≈ a2 ∧ b1 ≈ b2 := by
  constructor <;> (intro h; cases h; constructor <;> assumption)

def Quotient.prod (q1 : Quotient s1) (q2 : Quotient s2) : Quotient (s1.prod s2) :=
  q1.lift
    (fun a1 => q2.lift (fun a2 => ⟦(a1,a2)⟧) (by
      intro a b hab; simp
      simp [hab]
      rw [←eq]
      ))
    (by
      have ⟨q1,hq1⟩ := q1.exists_rep; cases hq1
      have ⟨q2,hq2⟩ := q2.exists_rep; cases hq2
      intro a b hab
      simp [hab]
      rw [←eq])

@[simp] theorem Quotient.prod_mk [sa : Setoid α] [sb : Setoid β] (a : α) (b : β)
  : Quotient.prod ⟦ a ⟧ ⟦ b ⟧ = Quotient.mk (s := sa.prod sb) (a,b) := by
  simp [prod]

@[simp] theorem Quotient.prod_eq_mk [sa : Setoid α] [sb : Setoid β]
    (aa : Quotient sa) (bb : Quotient sb) (a : α) (b : β)
  : Quotient.prod aa bb = Quotient.mk (s := sa.prod sb) (a,b) ↔ aa = ⟦ a ⟧ ∧ bb = ⟦ b ⟧ := by
  rcases aa.exists_rep with ⟨a',rfl⟩
  rcases bb.exists_rep with ⟨b',rfl⟩
  simp [Setoid.prod]

def Finset.mapEquiv [DecidableEq α'] (s : Finset α) (f : α ↪ α') : s ≃ s.map f where
  toFun := fun ⟨x,hx⟩ => ⟨f x, by simp [hx]⟩
  invFun := fun ⟨x',hx'⟩ =>
    ⟨ s.filter (f · = x') |>.getUnique (by
        simp at hx'
        have ⟨x,hx⟩ := hx'
        use x
        ext x₀; simp; aesop)
    , by simp ⟩
  left_inv := by
    rintro ⟨x,hx⟩
    simp; ext x₀; simp (config := {contextual := true}) [hx]
  right_inv := by
    rintro ⟨x',hx'⟩
    simp at hx' ⊢
    rcases hx' with ⟨x,hx,rfl⟩
    congr; simp
    ext x₀; simp (config := {contextual := true}) [hx]

@[simp] theorem Finset.mapEquiv_app [DecidableEq α'] (s : Finset α) (f : α ↪ α') (x : s)
  : (Finset.mapEquiv s f) x = f x := rfl

@[simp] theorem Finset.mapEquiv_symm_eq [DecidableEq α'] (s : Finset α) (f : α ↪ α') (x : s.map f) (y : α)
  : (Finset.mapEquiv s f).symm x = y ↔ x.val = f y := by
  rcases x with ⟨x,hx⟩
  simp [mapEquiv]
  simp at hx; rcases hx with ⟨y',h1,rfl⟩
  simp [eq_singleton_iff_unique_mem]
  aesop

@[simp] theorem Finset.eq_mapEquiv_symm [DecidableEq α'] (s : Finset α) (f : α ↪ α') (x : s.map f) (y : α)
  : y = (Finset.mapEquiv s f).symm x ↔ f y = x := by
  rw [eq_comm]; simp; apply eq_comm

theorem Finset.app_mapEquiv_symm [DecidableEq α'] (f') (s : Finset α) (f : α ↪ α') (x : s.map f)
  : f' = f.1 → f' ((Finset.mapEquiv s f).symm x) = x.val := by
  rintro rfl; rcases x with ⟨x,hx⟩
  simp at hx; rcases hx with ⟨y,_,rfl⟩
  simp

@[simp] theorem Finset.mapEquiv_of_app [DecidableEq α'] (s : Finset α) (f : α ↪ α') (x) (h)
  : (Finset.mapEquiv s f).symm ⟨f x, h⟩ = ⟨x,by simp at h; exact h⟩ := by
  simp [mapEquiv]; rw [eq_singleton_iff_unique_mem]
  simpa using h

@[simp] theorem Finset.mem_univ' (x : α) : x ∈ (@Finset.univ α I) :=
  Fintype.complete x

def Fintype.invFun [DecidableEq α'] [Fintype α] (f : α ↪ α') : Finset.univ.map f ≃ α :=
  (Finset.mapEquiv Finset.univ f).symm.trans
    ⟨Subtype.val, (Subtype.mk · <| by simp), by intro; simp, by intro; simp⟩

@[simp] theorem Fintype.invFun_eq [Fintype α] [DecidableEq α'] (f : α ↪ α') (x : Finset.univ.map f) (y : α)
  : Fintype.invFun f x = y ↔ x.val = f y := by simp [invFun]

@[simp] theorem Fintype.eq_invFun [Fintype α] [DecidableEq α'] (f : α ↪ α') (x : Finset.univ.map f) (y : α)
  : y = Fintype.invFun f x ↔ f y = x.val := by simp [invFun]

@[simp] theorem Fintype.invFun_app [Fintype α] [DecidableEq α'] (f : α ↪ α') (f') (x) (h)
  : f' = f.1 → Fintype.invFun f ⟨f' x, h⟩ = x := by rintro rfl; simp

theorem Fintype.app_invFun [Fintype α] [DecidableEq α'] (f : α ↪ α') (f') (x)
  : f' = f.1 → f' (Fintype.invFun f x) = x := by
    rintro rfl; simp [invFun, Finset.app_mapEquiv_symm]

@[simp] theorem Fintype.invFun_val_eq [Fintype α] [DecidableEq α'] (f : α ↪ α') (x : Finset.univ.map f) (y : α)
  : (Fintype.invFun f x) = y ↔ x.val = f y := by simp [invFun]

theorem Fintype.invFun_eq_invFun [Fintype α] [DecidableEq α'] (f f' : α ↪ α') (x y)
  : Fintype.invFun f x = Fintype.invFun f' y ↔ ∃ a, x = f a ∧ y = f' a := by
  simp [invFun]
  constructor
  · intro h; refine ⟨_, ?_, h.symm⟩
    simp [Finset.app_mapEquiv_symm]
  · rintro ⟨a,h,h'⟩
    simp_all

@[simp] theorem PNat.val_eq_val (x y)
  : PNat.val x = PNat.val y ↔ x = y := by
  simp [PNat.val, Subtype.val_inj]

@[simp] theorem PNat.natPred_succ (n)
  : PNat.natPred n + 1 = n := by
  match n with
  | ⟨_+1,_⟩ => simp

def Array.finRange (n : Nat) : Array (Fin n) :=
  ⟨List.finRange n⟩

@[simp] theorem Array.mem_finRange {n} (x : Fin n) : x ∈ finRange n := by
  simp [finRange, mem_def]

@[simp] theorem Array.finRange_data (n) : (Array.finRange n).data = List.finRange n := rfl

@[simp] theorem top : ⊤ := by trivial

@[simp] theorem not_bot : ¬⊥ := fun x => nomatch x

namespace BooleanAlgebra

variable {α : Type _} [BooleanAlgebra α] {a b c : α}

-- CC TODO: Generalize? add to some library? simplify proof in terms of other ops?
--          For example, inf_of_le_left uses the [Semilattice] typeclass.
-- CC Q: Is this the right namespace? usually these lemmas are at root namespace
theorem inf_le_iff_le_compl_sup : a ⊓ b ≤ c ↔ a ≤ bᶜ ⊔ c := by
  constructor
  · intro h
    have : bᶜ ⊔ (a ⊓ b) ≤ bᶜ ⊔ c := sup_le_sup_left h bᶜ
    replace := le_trans le_sup_inf this
    simp only [compl_sup_eq_top, ge_iff_le, le_top, inf_of_le_left, sup_le_iff, le_sup_left,
      true_and] at this
    exact this
  · intro h
    rw [sup_comm] at h
    have : a ⊓ b ≤ (c ⊔ bᶜ) ⊓ b := inf_le_inf_right b h
    simp [inf_sup_right] at this
    exact this

theorem inf_compl_le_iff_le_sup : a ⊓ bᶜ ≤ c ↔ a ≤ b ⊔ c := by
  conv => rhs; rhs; lhs; rw [← compl_compl b]
  exact BooleanAlgebra.inf_le_iff_le_compl_sup

theorem le_iff_inf_compl_le_bot : a ≤ b ↔ a ⊓ bᶜ ≤ ⊥ := by
  conv => lhs; rhs; rw [← compl_compl b]
  have : bᶜᶜ = bᶜᶜ ⊔ ⊥ := by exact (sup_bot_eq _).symm
  rw [this]
  exact inf_le_iff_le_compl_sup.symm

theorem le_compl_iff_inf_le_bot : a ≤ bᶜ ↔ a ⊓ b ≤ ⊥ := by
  conv => rhs; lhs; rhs; rw [← compl_compl b]
  exact le_iff_inf_compl_le_bot

theorem le_iff_inf_compl_eq_bot : a ≤ b ↔ a ⊓ bᶜ = ⊥ := by
  rw [← le_bot_iff]; exact le_iff_inf_compl_le_bot

end BooleanAlgebra
