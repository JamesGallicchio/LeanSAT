/-
Copyright (c) 2024 The LeanSAT Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import LeanSAT.Model.PropFun
import LeanSAT.Model.PropVars

namespace LeanSAT.Model

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

end LeanSAT.Model
