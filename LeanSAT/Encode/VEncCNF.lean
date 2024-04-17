/-
Copyright (c) 2024 The LeanSAT Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import LeanSAT.Encode.EncCNF
import LeanSAT.Model.PropPred
import Mathlib.Tactic.LiftLets

open LeanColls

/-! ## Verified Encodings

This file defines `VEncCNF`,
the main type for building *verified* encodings to CNF.
This augments the regular `EncCNF` with the ability to specify
and verify what a particular `EncCNF` value actually encodes.
-/

namespace LeanSAT.Encode

open Model EncCNF

namespace EncCNF

/-- `e` encodes proposition `P` -/
def encodesProp (e : EncCNF ν α) (P : PropPred ν) : Prop :=
  aux e.1
where aux (e' : StateM _ α) :=
  ∀ s,
    let s' := (e' s).2
    s'.vMap = s.vMap ∧
    s'.assumeVars = s.assumeVars ∧
    -- TODO(JG): should we weaken this to equisatisfiability?
    ∀ (τ : PropAssignment ν), s'.interp τ ↔ s.interp τ ∧ (open PropPred in τ ⊨ (↑s.assumeVars)ᶜ ⇨ P)

/-- If `e` encodes `P`, then `P` is satisfiable iff `e.toICnf` is satisfiable -/
theorem encodesProp_equisatisfiable [IndexType ν] [LawfulIndexType ν]
          (e : EncCNF ν α) (P : PropPred ν) (h : encodesProp e P)
  : (∃ τ : PropAssignment ν   , open PropPred in τ ⊨ P) ↔
    (∃ τ : PropAssignment IVar, open PropFun  in τ ⊨ e.toICnf.toPropFun) := by
  simp [toICnf, run, StateT.run]
  generalize hls : LawfulState.new' _ _ = ls
  have := h ls
  generalize hls' : e.1 ls = ls' at this
  rcases ls' with ⟨a,ls'⟩
  simp only at this ⊢
  rcases this with ⟨-,-,h3⟩
  rw [←hls] at h3
  simp [LawfulState.new', State.new, Clause.toPropFun] at h3
  clear hls' hls
  simp_rw [← h3]
  simp [LawfulState.interp]
  aesop

attribute [aesop unsafe apply] le_trans

theorem bind_encodesProp (e1 : EncCNF ν α) (f : α → EncCNF ν β)
  : e1.encodesProp P → (∀ s, (f (e1.1 s).1).encodesProp Q) →
    (e1 >>= f).encodesProp (P ⊓ Q)
  := by
  intro hP hQ s
  simp [encodesProp, encodesProp.aux] at hP hQ
  -- specialize hypotheses to the first state `s`
  rcases e1 with ⟨e1,he1⟩
  replace hP := hP s
  replace hQ := hQ s
  simp [Bind.bind, StateT.bind] at hP hQ ⊢
  replace he1 := he1 s
  -- give name to the next state `s'`
  generalize hs' : e1 s = s' at *
  rcases s' with ⟨a,s'⟩
  simp at *
  -- give name to the next state machine
  generalize he2 : (f a) = e2 at *
  rcases e2 with ⟨e2,he2⟩
  -- specialize hypotheses to this state `s'`
  replace hQ := hQ s'
  simp at *
  -- give name to the next state `s''`
  generalize hs'' : e2 s' = s'' at *
  rcases s'' with ⟨b,s''⟩
  open PropPred in --necessary because simp doesn't simp thru scoped instances not in scope
  simp at hP hQ ⊢
  -- once again we ♥ aesop
  aesop

@[simp] theorem encodesProp_pure (a : α) : encodesProp (pure a : EncCNF ν α) ⊤ := by
  intro s; simp [Pure.pure, StateT.pure]

end EncCNF

/-- The verified encoding monad. -/
def VEncCNF (ν) (α : Type u) (P : PropPred ν) :=
  { e : EncCNF ν α // e.encodesProp P }

namespace VEncCNF

instance : CoeHead (VEncCNF ν α P) (EncCNF ν α) := ⟨(·.1)⟩

theorem toICnf_equisatisfiable [IndexType ν] [LawfulIndexType ν] (v : VEncCNF ν α P) :
    (∃ τ : PropAssignment _, open PropFun in τ ⊨ v.val.toICnf.toPropFun) ↔
    (∃ τ : PropAssignment ν, open PropPred in τ ⊨ P)
  := by
  rw [v.val.encodesProp_equisatisfiable _ v.property]

def mapProp {P P' : PropPred ν} (h : P = P') : VEncCNF ν α P → VEncCNF ν α P' :=
  fun ⟨e,he⟩ => ⟨e, h ▸ he⟩

def newCtx (name : String) (inner : VEncCNF ν α P) : VEncCNF ν α P :=
  ⟨EncCNF.newCtx name inner, inner.2⟩

open PropPred in
protected def pure (a : α) : VEncCNF ν α ⊤ :=
  ⟨ Pure.pure a
  , by intro s; simp [Pure.pure, StateT.pure]⟩

def addClause (C : Clause (Literal ν)) : VEncCNF ν Unit C :=
  ⟨EncCNF.addClause C, by
    intro s
    generalize he : (EncCNF.addClause C).1 s = e
    rcases e with ⟨_,s'⟩
    simp [EncCNF.addClause] at he; cases he
    simp; simp [SemanticEntails.entails, himp, compl, LawfulState.addClause, State.addClause]
    ⟩

open PropPred in
/-- runs `e`, adding `ls` to each generated clause -/
def unlessOneOf (ls : Array (Literal ν)) (ve : VEncCNF ν α P)
    : VEncCNF ν α (fun τ => (∀ l ∈ ls, τ ⊭ ↑l) → τ ⊨ P) :=
  ⟨EncCNF.unlessOneOf ls ve, by
    -- TODO: terrible, slow proof
    intro s
    rcases ve with ⟨ve,hve⟩
    simp only [StateT.run] at hve ⊢
    generalize he : (EncCNF.unlessOneOf ls ve).1 s = e
    rcases e with ⟨a,s'⟩; dsimp
    simp only [EncCNF.unlessOneOf] at he
    generalize hsprev : EncCNF.LawfulState.mk .. = sprev at he
    generalize he' : ve.1 sprev = e
    rcases e with ⟨a',s''⟩
    have := hve sprev
    clear hve
    simp only [he'] at he this
    clear he'
    cases he; cases hsprev
    simp at this ⊢
    rcases s'' with ⟨⟨s''a,s''b,s''c⟩,s''d,s''e,s''f⟩
    rcases s with ⟨⟨sa,sb,sc⟩,sd,se,sf⟩
    simp
    cases this
    subst_vars
    simp only [EncCNF.LawfulState.interp] at *
    simp_all
    clear! s''f s''e s''d se sd
    rintro _ _ rfl
    simp [Clause.satisfies_iff, not_or, PropPred.satisfies_def]
  ⟩

open PropPred in
def assuming (ls : Array (Literal ν)) (e : VEncCNF ν α P)
    : VEncCNF ν α (fun τ => (∀ l ∈ ls, τ ⊨ ↑l) → P τ) :=
  unlessOneOf (ls.map (- ·)) e |>.mapProp (by
    funext τ
    simp [Clause.satisfies_iff, Array.mem_def]
  )

open PropFun in
set_option pp.proofs.withType false in
@[inline]
def withTemps (n) {P : PropAssignment (ν ⊕ Fin n) → Prop}
    (ve : VEncCNF (ν ⊕ Fin n) α P) :
    VEncCNF ν α (fun τ => ∃ σ, τ = σ.map Sum.inl ∧ P σ) :=
  ⟨EncCNF.withTemps _ ve.1, by
    intro ls_pre ls_post'
    -- give various expressions names and specialize hypotheses
    have def_ls_post : ls_post' = Prod.snd _ := rfl
    generalize ls_post' = ls_post at *; clear ls_post'
    generalize def_ls_post_pair : (EncCNF.withTemps n ve.1).1 ls_pre = ls_post_pair
      at def_ls_post
    unfold EncCNF.withTemps at def_ls_post_pair
    simp (config := {zeta := false}) at def_ls_post_pair
    lift_lets at def_ls_post_pair
    extract_lets vMap vMapInj assumeVars at def_ls_post_pair
    split at def_ls_post_pair
    next a ls_post_temps def_pair =>
    generalize_proofs h
    subst def_ls_post_pair
    simp [vMap, assumeVars] at def_ls_post; clear vMap assumeVars
    generalize def_ls_pre_temps : LawfulState.withTemps ls_pre = ls_pre_temps
    rw [def_ls_pre_temps] at def_pair
    -- extract relationship between ls_pre_temps and ls_post_temps
    have ls_temps_nextVar := ve.1.2 ls_pre_temps
    simp [def_pair] at ls_temps_nextVar
    have ls_temps_satisfies := ve.2 ls_pre_temps
    simp [def_pair] at ls_temps_satisfies
    clear def_pair
    rcases ls_temps_satisfies with ⟨hvmap, hassume, h⟩
    -- now we prove the goals
    subst ls_post
    simp
    rw [LawfulState.interp_withoutTemps]
    · simp_rw [h]
      subst ls_pre_temps
      simp
      clear h hassume hvmap ls_temps_nextVar def_pair ls_post_temps vMapInj
      intro τ
      constructor
      · aesop
      · rintro ⟨h1,h2⟩
        rcases (inferInstance : Decidable (τ ⊨ ls_pre.assumeVars.toPropFun)) with h | h
        . rcases h2 h with ⟨σ, rfl, _⟩
          use σ; simp
          tauto
        . let σ : PropAssignment (ν ⊕ Fin n) := fun | .inl x => τ x | _ => false
          use σ
          have : τ = PropAssignment.map Sum.inl σ := funext fun x => by simp only [PropAssignment.get_map]
          tauto
    · aesop
  ⟩

protected def bind (e1 : VEncCNF ν α P) (e2 : α → VEncCNF ν β Q) : VEncCNF ν β (P ⊓ Q) :=
  VEncCNF.mapProp (show P ⊓ (Q ⊓ ⊤) = (P ⊓ Q) by simp)
    ⟨ do let a ← e1; return ← e2 a
    , by
      simp
      apply bind_encodesProp _ _ e1.2
      intro s
      exact (e2 (e1.1.1 s).1).2
    ⟩

/-- Sequences two encodings together, i.e. a conjunction of the encodings.

For sequencing many encodings together, see `seq[ ... ]` syntax
-/
def seq (e1 : VEncCNF ν Unit P) (e2 : VEncCNF ν β Q) : VEncCNF ν β (fun τ => P τ ∧ Q τ) :=
  VEncCNF.bind e1 (fun () => e2)

scoped syntax "seq[ " term,+ " ]" : term

macro_rules
| `(seq[$as:term,*]) => do
  as.getElems.foldrM (β := Lean.TSyntax `term)
    (fun a acc => `(seq $a $acc))
    (← `(VEncCNF.pure ()))

@[inline]
def all [ToList C α] [Fold C α] [Fold.ToList C α]
    (c : C) {P : α → PropPred ν} (f : (a : α) → VEncCNF ν Unit (P a))
  : VEncCNF ν Unit (fun τ => ∀ a ∈ toList c, P a τ) :=
  ⟨ Fold.foldM c (fun () x => f x) ()
  , by
    have ⟨L,hPerm,h⟩ :=
      Fold.foldM_eq_foldM_toList (m := EncCNF ν) c
    simp_rw [← hPerm.mem_iff]; clear hPerm
    rw [h]; clear h
    induction L with
    | nil   => simp; apply encodesProp_pure
    | cons hd tl ih =>
      simp
      apply bind_encodesProp
      · have := (f hd).2
        simpa using this
      · aesop⟩

def forAll [IndexType α] [LawfulIndexType α] {P : α → PropPred ν} (f : (a : α) → VEncCNF ν Unit (P a))
  : VEncCNF ν Unit (fun τ => ∀ a, P a τ) :=
  all (IndexType.univ α) f
  |>.mapProp (by simp)

-- Cayden TODO: Unit could possibly made to be β instead? Generalize later.
-- One would think that P could be of type {P : PropFun ν}. But Lean timed out synthesizing that
def guard (p : Prop) [Decidable p] {P : p → PropPred ν}
      (f : (h : p) → VEncCNF ν Unit (P h))
  : VEncCNF ν Unit (if h : p then P h else ⊤) :=
  ⟨ do if h : p then f h
  , by
    by_cases h : p
    · simp [h]; simpa using (f h).2
    · simp [h]
  ⟩

def ite (p : Prop) [Decidable p] {P : p → PropPred ν} {Q : ¬p → PropPred ν}
    (f : (h : p) → VEncCNF ν Unit (P h))
    (g : (h : ¬p) → VEncCNF ν Unit (Q h))
  : VEncCNF ν Unit (if h : p then P h else Q h) :=
  ⟨ if h : p then f h
             else g h
  , by
    by_cases h : p <;> simp [h]
    · simpa using (f h).2
    · simpa using (g h).2⟩

open PropFun in
section

variable
  [Fold Ch (Literal ν)] [Fold Cc (Literal ν)]
  [ToList Ch (Literal ν)] [ToList Cc (Literal ν)]
  [Fold.ToList Ch (Literal ν)] [Fold.ToList Cc (Literal ν)]
  [Membership (Literal ν) Ch] [Membership (Literal ν) Cc]
  [Mem.ToList Ch (Literal ν)] [Mem.ToList Ch (Literal ν)]

def andImplyOr
    (hyps : Ch) (conc : Cc)
  : VEncCNF ν Unit (fun τ => (∀ h ∈ hyps, τ ⊨ ↑h) → (∃ c ∈ conc, τ ⊨ ↑c)) :=
  addClause (
    (View.of hyps).map LitVar.negate ++ View.of conc
    |> Insert.into (Array _))
  |> mapProp (by
    ext τ
    simp [Clause.satisfies_iff, PropPred.satisfies_def]
    conv => lhs; rhs; ext; rw [Insert.mem_into_iff]
    constructor
    · aesop
    · intro h
      by_cases h' : ∀ a ∈ hyps, τ ⊨ LitVar.toPropFun a
      · aesop
      · aesop)

def andImply (hyps : Array (Literal ν)) (conc : Literal ν)
  : VEncCNF ν Unit (fun τ => (∀ h ∈ hyps, τ ⊨ ↑h) → τ ⊨ ↑conc) :=
  andImplyOr hyps #[conc]
  |> mapProp (by simp [any])

def implyOr (hyp : Literal ν) (conc : Array (Literal ν))
  : VEncCNF ν Unit (fun τ => τ ⊨ ↑hyp → ∃ c ∈ conc, τ ⊨ ↑c) :=
  andImplyOr #[hyp] conc
  |> mapProp (by simp [all])

def orImplyOr (hyps : Array (Literal ν)) (conc : Array (Literal ν))
  : VEncCNF ν Unit (fun τ => (∃ h ∈ hyps, τ ⊨ ↑h) → (∃ c ∈ conc, τ ⊨ ↑c)) :=
  all hyps (fun hyp => andImplyOr #[hyp] conc)
  |> mapProp (by
    funext τ
    simp [-List.mapM,Clause.satisfies_iff, ← Mem.ToList.mem_iff_mem_toList]
  )

def orImply (hyps : Array (Literal ν)) (conc : Literal ν)
  : VEncCNF ν Unit (fun τ => (∃ h ∈ hyps, τ ⊨ ↑h) → τ ⊨ ↑conc) :=
  orImplyOr hyps #[conc]
  |> mapProp (by simp [any])

def andImplyAnd (hyps : Array (Literal ν)) (concs : Array (Literal ν))
  : VEncCNF ν Unit (fun τ => (∀ h ∈ hyps, τ ⊨ ↑h) → (∀ c ∈ concs, τ ⊨ ↑c)) :=
  all concs (fun conc => andImplyOr hyps #[conc])
  |> mapProp (by
    ext τ
    simp [Clause.satisfies_iff, ← Mem.ToList.mem_iff_mem_toList]
    aesop
  )

def implyAnd (hyp : Literal ν) (concs : Array (Literal ν))
  : VEncCNF ν Unit (fun τ => τ ⊨ ↑hyp → (∀ c ∈ concs, τ ⊨ ↑c)) :=
  andImplyAnd #[hyp] concs
  |> mapProp (by simp [all])

def orImplyAnd (hyps : Array (Literal ν)) (concs : Array (Literal ν))
  : VEncCNF ν Unit (fun τ => (∃ h ∈ hyps, τ ⊨ ↑h) → (∀ c ∈ concs, τ ⊨ ↑c)) :=
  all hyps (fun hyp =>
    all concs (fun conc =>
      andImplyOr #[hyp] #[conc]
    )
  )
  |> mapProp (by
    ext τ
    simp [Clause.satisfies_iff, ← Mem.ToList.mem_iff_mem_toList]
    aesop
  )

def imply (v1 v2 : Literal ν)
  : VEncCNF ν Unit (· ⊨ ↑v1 ⇨ ↑v2) :=
  andImplyOr #[v1] #[v2]
  |> mapProp (by simp [all,any])

def biImpl (v1 v2 : Literal ν)
  : VEncCNF ν Unit (fun τ => τ ⊨ ↑v1 ↔ τ ⊨ ↑v2) :=
  seq (imply v1 v2) (imply v2 v1)
  |> mapProp (by aesop)

def defConj (v : Literal ν) (vs : Array (Literal ν))
  : VEncCNF ν Unit (fun τ => τ ⊨ ↑v ↔ (∀ v ∈ vs, τ ⊨ ↑v)) :=
  seq (implyAnd v vs) (andImply vs v)
  |> mapProp (by aesop)

def defDisj (v : Literal ν) (vs : Array (Literal ν))
  : VEncCNF ν Unit (fun τ => τ ⊨ ↑v ↔ (∃ v ∈ vs, τ ⊨ ↑v)) :=
  seq (implyOr v vs) (orImply vs v)
  |> mapProp (by aesop)

end
