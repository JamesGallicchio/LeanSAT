import LeanSAT.AuxDefs
import LeanSAT.CNF

namespace LeanSAT

def Clause.satisfied (c : Clause) (a : Assn) := c.eval a = true
def Formula.satisfied (f : Formula) (a : Assn) := f.eval a = true

theorem Clause.satisfied_iff_exists_lit_true (c : Clause) (a : Assn)
  : c.satisfied a ↔ ∃ l, (l ∈ c.lits) ∧ a.litTrue l = true
  := List.any_eq_true

theorem Formula.satisfied_iff_clauses_satisfied (f : Formula) (a : Assn)
  : f.satisfied a ↔ ∀ c ∈ f.clauses, c.satisfied a
  := by simp [satisfied, eval, Clause.satisfied]

def Clause.equiv (c1 c2 : Clause) := ∀ a, c1.satisfied a ↔ c2.satisfied a

def Formula.equiv (f1 f2 : Formula) := ∀ a, f1.satisfied a ↔ f2.satisfied a

def Formula.equiSat (c1 c2 : Formula) := c1.satisfiable ↔ c2.satisfiable

section Hidden

-- Example

def c1 : Formula := 0 ∧ 1
def c2 : Formula := 0

example : (¬ Formula.equiv c1 c2) ∧ Formula.equiSat c1 c2
  := by
  constructor
  . let a : Assn := Std.HashMap.ofList [(0, true), (1, false)]
    refine fun contra => (?_ : ¬ _) (contra a)
    have : c1.eval a = false := by
      simp [c1, Formula.eval, Formula.clauses, OfNat.ofNat, Clause.eval]
    have : c2.eval a = true := by
      simp [c2, Formula.eval, Formula.clauses, OfNat.ofNat, Clause.eval]
    simp only [Formula.satisfied, *]
  . unfold Formula.equiSat
    have : c1.satisfiable := by
      refine ⟨Std.HashMap.ofList [(0,true), (1,true)], ?_⟩
      simp [c1, Formula.eval, Formula.clauses, OfNat.ofNat, Clause.eval]
    have : c2.satisfiable := by
      refine ⟨Std.HashMap.ofList [(0,true)], ?_⟩
      simp [c2, Formula.eval, Formula.clauses, OfNat.ofNat, Clause.eval]
    simp only [*]
end Hidden

def Clause.is_taut (c : Clause) := ∃ v, (.pos v ∈ c.lits) ∧ (.neg v ∈ c.lits) 

theorem Clause.taut_congr {c1 c2 : Clause}
  (h1 : c1.is_taut) (h : c1.equiv c2)
  : c2.is_taut := by
  have ⟨v,hvp,hvn⟩ := h1
  sorry

theorem Clause.equiv_iff_same_lits (c1 c2) 
  : Clause.equiv c1 c2 ↔ (∀ v, l ∈ c1.lits ↔ l ∈ c2.lits)
  := by
  simp [Clause.equiv]
  constructor <;> intro h
  . intro l
    revert c1 c2
    suffices ∀ _ _ _, (_ → _) from
      fun c1 c2 h => ⟨this c1 c2 h, this c2 c1 (fun a => (h a).symm)⟩
    intro c1 c2 h hl
    let a : Assn := c1.lits.map (fun l' =>
      if l = l' then
        (l.var, l.isPos)
      else
        (l.var, l.isNeg)) |> Std.HashMap.ofList
    have : c1.eval a = true := by
      sorry
    have ⟨l', hl'_mem, hl'_true⟩ :=
      (eval_true_iff_true_lit_mem c2 a).mp (h a ▸ this)
    have : l = l' := by
      cases l'
        <;> simp at hl'_true
        <;> have ⟨a,ha1,ha2⟩ := hl'_true
        <;> simp at ha1 ha2
      . simp? [Clause.eval] at hl'_true
    simp [*]
  . intro a
    sorry

theorem Formula.equiSat_of_equiv (c1 c2)
  : Formula.equiv c1 c2 → Formula.equiSat c1 c2
  := by
  intro h_equiv
  simp [equiv] at h_equiv
  simp [equiSat, satisfiable]
  constructor <;> intro h
  . match h with
    | ⟨a, h⟩ =>
    rw [h_equiv] at h
    exact ⟨a,h⟩
  . match h with
    | ⟨a, h⟩ =>
    rw [←h_equiv] at h
    exact ⟨a,h⟩

theorem Formula.equiv_refl (f)
  : Formula.equiv f f
  := by
  simp [equiv]



theorem eval_unit_to_assn
  : Formula.eval a ⟨⟨[l]⟩ :: cs⟩ = Formula.eval (a.hasFalse) ⟨cs⟩
  := by
  sorry


inductive ClauseReduceRes
| sat | unsat | unit (l : Literal) | reduced (c : Clause) | unchanged
deriving Repr

inductive FormulaReduceRes
| unsat | reduced (newUnits : List Literal) (f : Formula) | unchanged
deriving Repr


def unitsToAssn (us : List Literal) : Assn :=
  fun v =>
    match us.find? (·.var = v) with
    | none => none
    | some l => l.isPos

instance : Append Assn where
  append a1 a2 := fun v => a1 v |>.orElse fun () => a2 v

def Clause.unitProp (a : Assn) : Clause → ClauseReduceRes
| ⟨lits⟩ =>
  if lits.any (a.litTrue) then .sat else
  let rem := lits.filter (not <| a.litFalse ·)
  match rem with
  | [] => .unsat
  | [l] => .unit l
  | ls =>
    if ls = lits then .unchanged else .reduced ⟨ls⟩

theorem Clause.sizeOf_unitProp_reduced (a c c')
  : Clause.unitProp a c = .reduced c' → SizeOf.sizeOf c' < SizeOf.sizeOf c
  := by
  intro h
  cases c; case mk lits =>
  simp [unitProp] at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  cases h
  simp [Clause._sizeOf_inst, Nat.add_comm 1, Nat.add_one]
  apply Nat.succ_lt_succ
  apply List.sizeOf_filter_lt_of_ne
  assumption

/-- One iteration of unit propagation,
returns list of new units & reduced formula -/
def Formula.unitPropAux (a : Assn) : Formula → FormulaReduceRes
| ⟨clauses⟩ =>
  let rec loop : List Clause → FormulaReduceRes
  | [] => .unchanged
  | c::tl =>
    match loop tl with
    | .unsat => .unsat
    | .reduced us ⟨cs⟩ =>
      match c.unitProp a with
      | .sat => .reduced us ⟨cs⟩
      | .unsat => .unsat
      | .unit l => .reduced (l::us) ⟨cs⟩
      | .reduced c => .reduced us ⟨c::cs⟩
      | .unchanged => .reduced us ⟨c::cs⟩
    | .unchanged =>
      match c.unitProp a with
      | .sat => .reduced [] ⟨tl⟩
      | .unsat => .unsat
      | .unit l => .reduced [l] ⟨tl⟩
      | .reduced c => .reduced [] ⟨c::tl⟩
      | .unchanged => .unchanged
  loop clauses

theorem Formula.sizeOf_unitPropAux_reduced (a f us f')
  : Formula.unitPropAux a f = .reduced us f' → sizeOf f' < sizeOf f
  := by
  intro h
  cases f; next clauses =>
  simp [unitPropAux] at h
  induction clauses generalizing us f' <;> simp [unitPropAux.loop] at h
  split at h <;> try contradiction
  next hd tl ih res us' cs h_loop =>
    clear res
    split at h <;> first | contradiction | cases h
    next res h_hd =>
      clear res h_hd
      have := ih _ _ h_loop
      clear ih h_loop us a
      simp [_sizeOf_inst] at this ⊢
      apply Nat.lt_trans this
      apply Nat.add_lt_add_left
      rw [Nat.add_comm, Nat.add_comm 1, Nat.add_one, Nat.add_succ]
      apply Nat.succ_le_succ
      apply Nat.le_add_right
    next res l h_hd =>
      clear res h_hd l
      have := ih _ _ h_loop
      clear ih h_loop us'
      simp [_sizeOf_inst] at this ⊢
      apply Nat.lt_trans this
      apply Nat.add_lt_add_left
      rw [Nat.add_comm, Nat.add_comm 1, Nat.add_one, Nat.add_succ]
      apply Nat.succ_le_succ
      apply Nat.le_add_right
    next res hd' h_hd =>
      clear res
      have h_tl := ih _ _ h_loop
      have h_hd' := Clause.sizeOf_unitProp_reduced _ _ _ h_hd
      clear ih h_loop h_hd us a
      simp [_sizeOf_inst] at h_tl ⊢
      apply Nat.add_lt_add_left
      simp [Nat.add_comm 1]; simp [Nat.add_assoc]
      apply Nat.add_lt_add <;> assumption
    next res h_hd =>
      clear res h_hd
      have := ih _ _ h_loop
      clear ih h_loop us a
      simp [_sizeOf_inst] at this ⊢
      apply Nat.add_lt_add_left (Nat.add_lt_add_left _ _)
      apply Nat.lt_of_succ_lt_succ
      simp [Nat.succ_eq_add_one, Nat.add_comm]
      assumption
  next hd tl ih res h_loop =>
    clear res ih
    split at h <;> first | contradiction | cases h
    next res h_hd =>
      clear res h_hd h_loop
      simp [_sizeOf_inst]
      apply Nat.add_lt_add_left
      rw [Nat.add_comm, Nat.add_comm 1, Nat.add_one, Nat.add_succ]
      apply Nat.succ_le_succ
      apply Nat.le_add_right
    next res hd' h_hd =>
      clear res hd' h_hd h_loop
      simp [_sizeOf_inst]
      apply Nat.add_lt_add_left
      rw [Nat.add_comm, Nat.add_comm 1, Nat.add_one, Nat.add_succ]
      apply Nat.succ_le_succ
      apply Nat.le_add_right
    next res hd' h_hd =>
      clear res
      simp [_sizeOf_inst]
      apply Nat.add_lt_add_left (Nat.add_lt_add_right (Nat.add_lt_add_left _ _) _)
      apply Clause.sizeOf_unitProp_reduced _ _ _ h_hd

def Formula.unitProp (f : Formula) : FormulaReduceRes :=
  let rec loop (f : Formula) (a : Assn) :=
    match h : f.unitPropAux a with
    | .unsat => .unsat
    | .reduced us f' =>
      have : sizeOf f' < sizeOf f :=
        sizeOf_unitPropAux_reduced _ _ _ _ h
      match loop f' (unitsToAssn us) with
      | .unsat            => .unsat
      | .reduced us' f''  => .reduced (us ++ us') f''
      | .unchanged        => .reduced us f'
    | .unchanged => .unchanged
  loop f (fun _ => none)
termination_by loop f _ => sizeOf f



theorem Formula.unitProp_unsat (a f)
  : Formula.unitProp f = .unsat → eval a f = false
  := by
  intro h
  match f with
  | ⟨clauses⟩ =>
  induction clauses
  . simp [unitProp] at h
    unfold unitProp.loop at h
    split at h <;> contradiction
  case cons hd tl ih =>
  simp
  sorry

theorem Formula.unitProp_reduced (f us f' a)
  : Formula.unitProp f = .reduced us f' → eval (unitsToAssn us ++ a) f = false
  := by
  intro h
  sorry

def FormulaReduceRes.toFormula : FormulaReduceRes → Option Formula
| .unsat => some ⟨[.empty]⟩
| .reduced us f => some <| (⟨us.map (· : Literal → Clause)⟩) ∧ f
| .unchanged => none

theorem Formula.unitProp_preserves_equiv (f : Formula)
  : (f.unitProp.toFormula.getD f).equiv f
  := by
  simp [Option.getD]
  split
  case h_2 f o ff h =>
    exact f.equiv_refl
  case h_1 f o ff f' h =>
  clear o ff
  simp [equiv]
  intro a
  simp [FormulaReduceRes.toFormula] at h
  split at h <;> first | contradiction | cases h
  next res h =>
    clear res
    conv =>
      lhs
      simp [eval, List.all, List.foldr, Clause.eval, Clause.empty, List.any]
    apply Eq.symm
    apply Formula.unitProp_unsat
    assumption
  next res us f' h =>
    clear res
    
    sorry

def Formula.admitsRAT (c : Clause) (f : Formula) : Bool :=
  f.clauses.all (fun d =>
    !d.contains || )
