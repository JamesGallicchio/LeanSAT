/-
Copyright (c) 2024 The LeanSAT Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import LeanSAT.Model.PropVars
import LeanSAT.Model.OfFun
import Mathlib.Data.Finset.Preimage

namespace LeanSAT.Model


/-! ## Substitution

This file defines operations on [PropForm] and [PropFun] for
substituting the variables in a formula with other variables,
or in general with other formulas.

The main definitions are:
- [PropForm.subst], [PropFun.subst]
- [PropForm.substOne], [PropFun.substOne]
- [PropForm.map], [PropFun.map]
- [PropForm.pmap], [PropFun.pmap]
-/

/-! ### `subst` -/

open PropFun in
def PropAssignment.subst (f : ν → PropFun ν') (τ : PropAssignment ν') : PropAssignment ν :=
  fun v => τ ⊨ f v

/-! # PropForm -/

namespace PropForm

def subst (p : PropForm ν₁) (f : ν₁ → PropForm ν₂) : PropForm ν₂ :=
  match p with
  | .var l => f l
  | .tr => .tr
  | .fls => .fls
  | .neg φ => .neg (φ.subst f)
  | .conj φ₁ φ₂ => .conj (φ₁.subst f) (φ₂.subst f)
  | .disj φ₁ φ₂ => .disj (φ₁.subst f) (φ₂.subst f)
  | .impl φ₁ φ₂ => .impl (φ₁.subst f) (φ₂.subst f)
  | .biImpl φ₁ φ₂ => .biImpl (φ₁.subst f) (φ₂.subst f)

section subst

variable (f f₁ : ν₁ → PropForm ν₂) (f₂ : ν₂ → PropForm ν₃) (φ φ₁ φ₂ : PropForm ν₁)

@[simp] theorem subst_fls  : subst (.fls : PropForm ν₁) f = .fls                     := rfl
@[simp] theorem subst_tr   : subst (.tr : PropForm ν₁) f = .tr                       := rfl
@[simp] theorem subst_disj : subst (.disj φ₁ φ₂) f = .disj (subst φ₁ f) (subst φ₂ f) := rfl
@[simp] theorem subst_conj : subst (.conj φ₁ φ₂) f = .conj (subst φ₁ f) (subst φ₂ f) := rfl
@[simp] theorem subst_neg  : subst (.neg φ) f = .neg (subst φ f)                     := rfl

theorem subst_assoc : (subst (subst φ f₁) f₂) = subst φ (fun v => subst (f₁ v) f₂) := by
  induction φ <;> simp [subst, *]

theorem vars_subst [DecidableEq ν₁] [DecidableEq ν₂]
  : vars (φ.subst f) = (vars φ).biUnion (fun v1 => vars (f v1)) := by
  induction φ <;> simp [subst, Finset.biUnion_union, *]

@[simp]
theorem satisfies_subst {φ : PropForm ν₁} {f} {τ : PropAssignment ν₂}
    : τ ⊨ φ.subst f ↔ τ.subst (⟦f ·⟧) ⊨ φ := by
  induction φ <;> simp [subst, PropAssignment.subst, *]; rw [PropFun.satisfies_mk]

-- CC: Standardize use of (⟦⟧ = ⟦⟧) vs. `equivalent`? Rn we use the former.
theorem subst_congr {φ₁ φ₂} (hφ : (⟦φ₁⟧ : PropFun _) = ⟦φ₂⟧)
    : ∀ (σ : ν₁ → PropForm ν₂), (⟦φ₁.subst σ⟧ : PropFun _) = ⟦φ₂.subst σ⟧ := by
  intro σ
  apply PropFun.ext
  intro τ
  rw [Quotient.eq] at hφ
  -- CC: `simp_rw` gives an error here. James claims the newest version of Lean fixes this bug.
  rw [PropFun.satisfies_mk, PropFun.satisfies_mk, satisfies_subst, satisfies_subst,
      ← PropFun.satisfies_mk, ← PropFun.satisfies_mk, Quotient.sound hφ]

end subst /- section -/

/-! ### `substOne` -/

def substOne [DecidableEq ν] (φ : PropForm ν) (v : ν) (ψ : PropForm ν) : PropForm ν :=
  φ.subst (fun v' => if v' = v then ψ else .var v')

section substOne

variable [DecidableEq ν] (φ φ₁ φ₂ : PropForm ν) (v : ν) (ψ ψ₁ ψ₂ : PropForm ν)

theorem satisfies_substOne {φ : PropForm ν} {v} {τ : PropAssignment ν}
    : τ ⊨ φ.substOne v ψ ↔ τ.set v (τ ⊨ ψ) ⊨ φ := by
  simp [substOne]
  apply iff_of_eq; congr
  ext v
  simp [PropAssignment.subst, PropAssignment.set]
  split <;> simp
  exact PropFun.satisfies_mk

theorem substOne_congr {φ₁ φ₂ ψ₁ ψ₂} (v : ν)
    (hφ : (⟦φ₁⟧ : PropFun _) =  ⟦φ₂⟧) (hψ : (⟦ψ₁⟧ : PropFun _) = ⟦ψ₂⟧)
    : (⟦ φ₁.substOne v ψ₁ ⟧ : PropFun _) = ⟦ φ₂.substOne v ψ₂ ⟧ := by
  apply PropFun.ext
  intro τ
  rw [PropFun.satisfies_mk, PropFun.satisfies_mk]
  simp [substOne]
  rw [← PropFun.satisfies_mk, ← PropFun.satisfies_mk, hφ]
  apply iff_of_eq; congr; ext v
  simp [PropAssignment.subst]
  split
  · rw [hψ]
  · simp

theorem vars_substOne : (PropForm.substOne φ v ψ).vars ⊆ (φ.vars \ {v}) ∪ ψ.vars := by
  induction φ with
  | var =>
      intro v hv; simp [subst, substOne] at hv ⊢
      split at hv
      · simp [hv]
      · simp at hv; subst_vars; simp [*]
  | tr  => simp
  | fls => simp
  | neg φ₁ ih => simp; exact ih
  | disj φ₁ φ₂ ih₁ ih₂
  | conj φ₁ φ₂ ih₁ ih₂
  | impl φ₁ φ₂ ih₁ ih₂
  | biImpl φ₁ φ₂ ih₁ ih₂ =>
    intro v hv; simp at *
    cases hv
    · have := ih₁ ‹_›
      simp at this; rcases this with ⟨a,b⟩|c <;> simp [*]
    · have := ih₂ ‹_›
      simp at this; rcases this with ⟨a,b⟩|c <;> simp [*]

end substOne /- section -/

end PropForm

/-! # PropFun -/

namespace PropFun

-- A computable, lifting version of `PropFun.subst` below.
-- `PropForm.subst` maps a substitution function over the atoms of a PropForm.
-- `substL` lifts the same substitution over PropForms into one over PropFuns.
def substL (φ : PropFun ν₁) (f : ν₁ → PropForm ν₂) : PropFun ν₂ :=
  φ |> Quotient.lift (⟦PropForm.subst · f⟧)
    (fun _ _ h => PropForm.subst_congr (Quotient.eq.mpr h) f)

section substL

variable (f : ν₁ → PropForm ν₂) (φ₁ φ₂ : PropFun ν₁) (v : ν₁)

@[simp] theorem substL_distrib : substL ⟦v⟧ f = ⟦f v⟧ := rfl
@[simp] theorem substL_bot : substL ⊥ f = ⊥ := rfl
@[simp] theorem substL_top : substL ⊤ f = ⊤ := rfl

@[simp] theorem substL_disj : substL (φ₁ ⊔ φ₂) f = substL φ₁ f ⊔ substL φ₂ f := by
  have ⟨φ₁, hφ₁⟩ := φ₁.exists_rep; cases hφ₁
  have ⟨φ₂, hφ₂⟩ := φ₂.exists_rep; cases hφ₂
  rfl

@[simp] theorem substL_conj : substL (φ₁ ⊓ φ₂) f = substL φ₁ f ⊓ substL φ₂ f := by
  have ⟨φ₁, hφ₁⟩ := φ₁.exists_rep; cases hφ₁
  have ⟨φ₂, hφ₂⟩ := φ₂.exists_rep; cases hφ₂
  rfl

@[simp] theorem substL_neg : substL (neg φ) f = neg (substL φ f) := by
  have ⟨φ, hφ⟩ := φ.exists_rep; cases hφ
  rfl

@[simp] theorem substL_compl : substL φᶜ f = (substL φ f)ᶜ := by
  have ⟨φ, hφ⟩ := φ.exists_rep; cases hφ
  rfl

@[simp] theorem satisfies_substL {φ : PropFun ν₁} {f} {τ : PropAssignment ν₂} :
    τ ⊨ φ.substL f ↔ τ.subst (⟦f ·⟧) ⊨ φ := by
  have ⟨φ, hφ⟩ := φ.exists_rep; cases hφ
  simp [substL]
  rw [satisfies_mk, satisfies_mk, PropForm.satisfies_subst]

end substL /- section -/

noncomputable
def subst (φ : PropFun ν₁) (f : ν₁ → PropFun ν₂) : PropFun ν₂ :=
  φ.prod (Quotient.choice f)
  |>.lift (fun (p,f) => ⟦ p.subst f ⟧) (by
    rintro ⟨p1,f1⟩ ⟨p2,f2⟩ hab
    simp at *
    rcases hab with ⟨hp,hf⟩
    ext τ; rw [PropFun.satisfies_mk, PropFun.satisfies_mk]
    simp
    have : ∀ x, ⟦f1 x⟧ = ⟦f2 x⟧ := fun x => Quotient.eq.mpr (hf x)
    simp [this]
    apply PropForm.equivalent_ext.mp hp
  )

section subst

variable (φ φ₁ φ₂ : PropFun ν₁) (f f₁ : ν₁ → PropFun ν₂) (τ : PropAssignment ν₂) (v : ν₁)

@[simp]
theorem satisfies_subst {φ : PropFun ν₁} {f} {τ : PropAssignment ν₂}
    : τ ⊨ φ.subst f ↔ τ.subst f ⊨ φ := by
  unfold subst
  generalize hq : φ.prod (Quotient.choice f) = q
  rcases q.exists_rep with ⟨⟨p, f'⟩, rfl⟩
  simp [Quotient.lift_mk (s := .prod _ _)]
  rw [satisfies_mk, PropForm.satisfies_subst, ← satisfies_mk]
  rw [Quotient.prod_eq_mk] at hq
  rcases hq with ⟨rfl,hq⟩
  apply iff_of_eq; congr; apply congrFun; apply congrArg
  funext x; simp [Quotient.choice] at hq
  have := Quotient.sound (hq x)
  simp at this
  exact this.symm

-- CC: Unsure how to prove for fancy `subst`.
@[simp] theorem subst_distrib : subst ⟦v⟧ f = f v := by
  ext; simp [PropAssignment.subst]

@[simp] theorem subst_bot : subst ⊥ f = ⊥ := rfl
@[simp] theorem subst_top : subst ⊤ f = ⊤ := rfl

@[simp] theorem subst_disj : subst (φ₁ ⊔ φ₂) f = subst φ₁ f ⊔ subst φ₂ f := by
  have ⟨φ₁, hφ₁⟩ := φ₁.exists_rep; cases hφ₁
  have ⟨φ₂, hφ₂⟩ := φ₂.exists_rep; cases hφ₂
  rfl

@[simp] theorem subst_conj : subst (φ₁ ⊓ φ₂) f = subst φ₁ f ⊓ subst φ₂ f := by
  have ⟨φ₁, hφ₁⟩ := φ₁.exists_rep; cases hφ₁
  have ⟨φ₂, hφ₂⟩ := φ₂.exists_rep; cases hφ₂
  rfl

@[simp] theorem subst_neg : subst (neg φ) f = neg (subst φ f) := by
  have ⟨φ, hφ⟩ := φ.exists_rep; cases hφ
  rfl

theorem semVars_subst [DecidableEq ν₁] [DecidableEq ν₂]
    {φ} {f : ν₁ → PropFun ν₂}
  : semVars (PropFun.subst φ f) ⊆ (semVars φ).biUnion (fun v1 => semVars (f v1)) := by
  intro v2 hv2
  -- dig through the quotients & definitions
  unfold subst at hv2
  rw [Finset.mem_biUnion]
  have ⟨p,hp⟩ := φ.exists_rep; cases hp
  generalize hf' : Quotient.choice f = f' at hv2
  have ⟨f'', hf''⟩ := f'.exists_rep; cases hf''
  simp [Quotient.lift_mk (s := .prod _ _)] at hv2
  -- get assignments for which v2 is meaningful
  rw [mem_semVars] at hv2; rcases hv2 with ⟨τ,hsat,hunsat⟩
  -- now we can use `PropForm.satisfies_subst`
  rw [satisfies_mk] at hsat hunsat
  simp at hsat hunsat
  -- eliminate references to f'' by rewriting back to f
  have : ∀ x, ⟦f'' x⟧ = f x := by
    simp [Quotient.choice, piSetoid, instHasEquiv, Setoid.r] at hf'
    intro x; have := sound (hf' x); simp at this; simp [this]
  simp [this] at hsat hunsat; clear this hf' f''
  -- any two disagreeing assignments give you a semantic variable
  rw [← satisfies_mk] at hsat hunsat
  have ⟨x,h1,h2⟩ := exists_semVar hsat hunsat; clear hsat hunsat
  use x; simp [h2]; clear h2
  -- push info around
  rw [mem_semVars]
  simp [PropAssignment.subst] at h1
  by_cases h : τ ⊨ f x
  · use τ; simp [h] at h1; simp [*]
  · simp [h] at h1
    refine ⟨_, h1, ?_⟩
    simp [h]

end subst /- section -/

def substOne [DecidableEq ν] (ψ : PropFun ν) (v : ν) (φ : PropFun ν) : PropFun ν :=
  ψ.lift (fun ψ => φ.lift (fun φ => ⟦ψ.substOne v φ⟧) (by
      intro a b h
      ext τ
      simp
      rw [PropForm.substOne_congr]
      · simp
      · apply PropFun.sound h
      )
    ) (by
    intro a b h
    ext τ
    simp
    apply iff_of_eq; congr
    ext φ
    apply PropForm.substOne_congr
    · apply PropFun.sound h
    · simp
    )

section substOne

@[simp]
theorem satisfies_substOne [DecidableEq ν] {φ ψ : PropFun ν} {v : ν} {τ : PropAssignment ν}
    : τ ⊨ ψ.substOne v φ ↔ τ.set v (τ ⊨ φ) ⊨ ψ := by
  have ⟨ψ,hψ⟩ := ψ.exists_rep; cases hψ
  have ⟨φ,hφ⟩ := φ.exists_rep; cases hφ
  simp [substOne]; rw [satisfies_mk, satisfies_mk]
  rw [PropForm.satisfies_substOne]
  rfl

end substOne /- section -/

end PropFun

/-! ### `map` -/

namespace PropForm

@[simp]
def map (f : ν₁ → ν₂) : PropForm ν₁ → PropForm ν₂
| .var l => .var (f l)
| .tr => .tr
| .fls => .fls
| .neg φ => .neg (map f φ)
| .conj φ₁ φ₂ => .conj (map f φ₁) (map f φ₂)
| .disj φ₁ φ₂ => .disj (map f φ₁) (map f φ₂)
| .impl φ₁ φ₂ => .impl (map f φ₁) (map f φ₂)
| .biImpl φ₁ φ₂ => .biImpl (map f φ₁) (map f φ₂)

section map

variable (f : ν₁ → ν₂) (φ φ₁ φ₂ : PropForm ν₁)

@[simp]
theorem vars_map [DecidableEq ν₁] [DecidableEq ν₂] : vars (φ.map f) = φ.vars.image f := by
  induction φ <;> simp [*, Finset.image_union]

theorem satisfies_map {φ : PropForm ν₁} {f} {τ : PropAssignment ν₂}
    : τ ⊨ φ.map f ↔ (τ.map f) ⊨ φ := by
  induction φ <;> (simp [map, PropAssignment.map] at *) <;> (simp [*])

@[simp]
theorem semVars_map [DecidableEq ν₁] [DecidableEq ν₂] [Fintype ν₁]
      {f : ν₁ → ν₂} (hf : f.Injective) (φ : PropForm ν₁)
    : PropFun.semVars ⟦φ.map f⟧ = (PropFun.semVars ⟦φ⟧).map ⟨f,hf⟩ := by
  ext v2; simp
  constructor
  · intro h
    have isVar : v2 ∈ vars (map f φ) := semVars_subset_vars _ h
    simp at isVar
    rcases isVar with ⟨v1, _, rfl⟩
    simp [hf.eq_iff]
    have := by rw [PropFun.mem_semVars] at h; exact h
    rcases this with ⟨τ,hpos,hneg⟩
    rw [PropFun.satisfies_mk] at hpos hneg
    simp [satisfies_map] at hpos hneg
    rw [PropAssignment.map_set (finj := hf)] at hneg
    rw [PropFun.mem_semVars]
    use PropAssignment.map f τ
    simp
    rw [PropFun.satisfies_mk, PropFun.satisfies_mk]; simp [*]
  . rintro ⟨v1,hv1,rfl⟩
    rw [PropFun.mem_semVars] at hv1 ⊢
    rcases hv1 with ⟨τ,hpos,hneg⟩
    rw [PropFun.satisfies_mk] at hpos hneg
    have ⟨σ,h⟩ := τ.exists_preimage ⟨f,hf⟩
    cases h; simp at hpos hneg
    use σ
    dsimp
    rw [PropFun.satisfies_mk, PropFun.satisfies_mk]
    simp [satisfies_map, hpos]
    rw [PropAssignment.map_set]
    · exact hneg
    · assumption

end map /- section -/

end PropForm

namespace PropFun

def map (f : ν₁ → ν₂) (φ : PropFun ν₁) : PropFun ν₂ :=
  φ.lift (⟦ PropForm.map f · ⟧) (by
    intro a b h
    simp
    ext τ
    rw [PropFun.satisfies_mk, PropFun.satisfies_mk]
    simp [PropForm.satisfies_map]
    rw [← PropFun.satisfies_mk, ← PropFun.satisfies_mk, Quotient.eq.mpr h]
  )

section map

@[simp]
theorem satisfies_map {φ : PropFun ν₁} {f} {τ : PropAssignment ν₂}
    : τ ⊨ φ.map f ↔ (τ.map f) ⊨ φ := by
  let ⟨ϕ,hϕ⟩ := φ.toTrunc.out
  cases hϕ
  simp [map]
  rw [satisfies_mk, satisfies_mk]
  apply PropForm.satisfies_map

theorem semVars_map [DecidableEq ν₁] [DecidableEq ν₂] [Fintype ν₁]
    (f : ν₁ → ν₂) (φ : PropFun ν₁) (hf : f.Injective)
    : (φ.map f).semVars = φ.semVars.map ⟨f,hf⟩ := by
  let ⟨ϕ,hϕ⟩ := φ.toTrunc.out; cases hϕ
  simp [map, *, PropForm.semVars_map]

variable (f : ν₁ → ν₂) (φ φ₁ φ₂ : PropFun ν₁)

@[simp] theorem map_var (v : ν₁) : map f (.var v) = .var (f v) := rfl
@[simp] theorem map_tr  : map f ⊤ = ⊤ := rfl
@[simp] theorem map_fls : map f ⊥ = ⊥ := rfl
@[simp] theorem map_neg  : map f (φᶜ) = (map f φ)ᶜ := by ext; simp
@[simp] theorem map_conj : map f (φ₁ ⊓ φ₂) = (map f φ₁ ⊓ map f φ₂) := by ext; simp
@[simp] theorem map_disj : map f (φ₁ ⊔ φ₂) = (map f φ₁ ⊔ map f φ₂) := by ext; simp
@[simp] theorem map_impl : map f (φ₁ ⇨ φ₂) = (map f φ₁ ⇨ map f φ₂) := by ext; simp
@[simp] theorem map_biImpl : map f (biImpl φ₁ φ₂) = .biImpl (map f φ₁) (map f φ₂) := by ext; simp

end map /- section -/

end PropFun
