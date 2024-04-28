-- CC: An attempt to get parsing faster, given that the Except monad can be expensive
def parseLSRLine'_aux (pivot : Option ILit) (line : SRAdditionLine) (mode : SRParsingMode) : List String → Except String (SRAdditionLine × SRParsingMode)
  | [] => ok (line, mode)
  | atom :: atoms =>
  -- No matter what, the string should be a number, so parse it as an int
  match atom.toInt? with
  | none => throw s!"Atom {atom} didn't parse to a number"
  | some n =>
    if hn : n = 0 then
      match mode with
      | .clause =>
        -- We don't have a witness, so we insert the pivot into the witness and continue, if the clause isn't empty
        match pivot with
        | none => parseLSRLine'_aux pivot line .upHints atoms
        | some pivot => parseLSRLine'_aux pivot { line with witnessLits := line.witnessLits.push pivot } .upHints atoms
      | .witnessLits => parseLSRLine'_aux pivot line .upHints atoms
      | .witnessMappedReady => parseLSRLine'_aux pivot line .upHints atoms
      | .witnessMappedHalfway _ => throw s!"Only got half a substitution mapping when ending a witness"
      | .upHints => parseLSRLine'_aux pivot line .lineDone atoms
      | .ratHints index hints =>
          parseLSRLine'_aux pivot { line with
            ratHintIndexes := line.ratHintIndexes.push index,
            ratHints := line.ratHints.push hints,
            ratSizesEq := by simp [line.ratSizesEq] } .lineDone atoms
      | .lineDone => throw s!"Addition line continued after last ending 0"
      | .err str => throw str
    else
      match mode with
      | .clause =>
        match pivot with
        | none => throw "No pivot provided for the clause"
        | some pivot =>
          if n = pivot.val then
            -- Seeing the pivot again means we're parsing a witness
            parseLSRLine'_aux pivot { line with witnessLits := line.witnessLits.push ⟨n, hn⟩ } .witnessLits atoms
          else
            -- It's not the pivot (and it's not 0), so add it to the clause
            parseLSRLine'_aux pivot { line with clause := line.clause.push ⟨n, hn⟩ } .clause atoms
      | .witnessLits =>
        match pivot with
        | none => throw "No pivot provided for the witness"
        | some pivot =>
          if n = pivot.val then
            -- Seeing the pivot again means we're parsing the substitution mappings
            parseLSRLine'_aux pivot line .witnessMappedReady atoms
          else
            parseLSRLine'_aux pivot { line with witnessLits := line.witnessLits.push ⟨n, hn⟩ } .witnessLits atoms
      | .witnessMappedReady =>
        match pivot with
        | none => throw "No pivot provided for the witness"
        | some pivot =>
          if n = pivot.val then
            throw s!"Saw pivot again in substitution mapping"
          else
            if n < 0 then
              throw s!"First of a substitution mapping must be positive"
            else
              parseLSRLine'_aux pivot line (.witnessMappedHalfway ⟨n.natAbs, Int.natAbs_pos.mpr hn⟩) atoms
      | .witnessMappedHalfway v =>
        parseLSRLine'_aux pivot {line with
          witnessMaps := line.witnessMaps.push v |>.push ⟨n, hn⟩,
          witnessMapsMod := by simp [add_assoc, Nat.add_mod_right, line.witnessMapsMod] } .witnessMappedReady atoms
      | .upHints =>
        if n < 0 then
          match pivot with
          | none => throw "Can't have RAT hints for empty clauses"
          | _ =>
            -- This is our first RAT hint - start building it
            parseLSRLine'_aux pivot line (.ratHints (n.natAbs - 1) #[]) atoms
        else
          parseLSRLine'_aux pivot { line with upHints := line.upHints.push (n.natAbs - 1) } .upHints atoms
      | .ratHints index hints =>
        if n < 0 then
          -- This is a new RAT hint - add the old one
          parseLSRLine'_aux pivot { line with
            ratHintIndexes := line.ratHintIndexes.push index,
            ratHints := line.ratHints.push hints,
            ratSizesEq := by simp [line.ratSizesEq] } (.ratHints (n.natAbs - 1) #[]) atoms
        else
          parseLSRLine'_aux pivot line (.ratHints index (hints.push (n.natAbs - 1))) atoms
      | .lineDone => throw s!"Addition line continued after last ending 0"
      | .err str => throw str

def parseLSRLine' (maxId : Nat) (s : String) : Except String (Nat × (SRAdditionLine ⊕ SRDeletionLine)) :=
  match s.splitOn " " with
  | [] => throw "Empty line"
  | [_] => throw s!"Single atom line: {s}, with id {maxId}"
  | (id :: hd :: tls) =>
    match hd with
    | "d" =>
      -- Check to make sure the maxId is (non-strictly) monotonically increasing
      match id.toNat? with
      | none => throw "Line ID is not a number"
      | some id =>
        if id < maxId then
          throw "Deletion line id is not increasing"
        else
          match tls.foldlM (fun arr str =>
            match str.toNat? with
            | none => throw (throw s!"{str} was not a number")
            | some 0 => throw (return arr)
            | some (n + 1) => return arr.push n) #[] with
          | ok _ => throw "Zero not found on deletion line"
          | error e => return ⟨max id maxId, .inr (SRDeletionLine.mk (← e))⟩
    | _ =>
      -- We have an addition line, so the maxId should strictly increase
      match id.toNat? with
      | none => throw "Line ID is not a number"
      | some id =>
        if id ≤ maxId then
          throw s!"Addition line id is not increasing: parsed {id}, max {maxId}"
        else
          match hd.toInt? with
          | none => throw "Pivot is not a number"
          | some n =>
            let line := SRAdditionLine.new
            if hn : n = 0 then
              match parseLSRLine'_aux none line .upHints tls with
              | error str => throw str
              | ok ⟨line, mode⟩ =>
                if mode != .lineDone then
                  throw "Addition line for empty clause didn't end with 0"
                else
                  return ⟨id, .inl line⟩
            else
              match parseLSRLine'_aux (some ⟨n, hn⟩) { line with clause := line.clause.push ⟨n, hn⟩ } .clause tls with
              | error str => throw str
              | ok ⟨line, mode⟩ =>
                if mode != .lineDone then
                  throw "Addition line didn't end with 0"
                else
                  return ⟨id, .inl line⟩

-- A unit propagation function `UP` is lawful if it returns `MUPResult`s as expected. -/
def LawfulUP (UP : PPA → IClause → MUPResult) : Prop :=
  ∀ (τ : PPA) (C : IClause),
    (UP τ C = .falsified → C.toPropFun ⊓ τ = ⊥)
  ∧ (∀ {l : ILit}, UP τ C = .unit l →
        l ∈ C ∧ τ.litValue? l = none ∧ C.toPropFun ⊓ τ ≤ l.toPropFun ⊓ τ)
  ∧ (UP τ C = .satisfied → τ ≤ C.toPropFun)

theorem LawfulUP_of_eq_of_LawfulUP {UP UP' : PPA → IClause → MUPResult} :
    (∀ τ C, UP τ C = UP' τ C) → LawfulUP UP → LawfulUP UP' := by
  intro h_eq h_lawful
  intro τ C
  have := h_lawful τ C
  rw [h_eq τ C] at this
  exact this

private def pevalM_SatisfiesM_motive (τ : PPA) (C : IClause) : ℕ → Option ILit → Prop
  | idx, none => ∀ ⦃i : Fin C.size⦄, i < idx → τ.litValue? C[i] = some false
  | idx, some lit => lit ∈ C.data ∧ τ.litValue? lit = none ∧
      (∀ ⦃j : Fin C.size⦄, j < idx → C[j] ≠ lit → τ.litValue? C[j] = some false)

theorem foldlM_pevalM_some {τ : PPA} {unit : ILit} :
  τ.litValue? unit = none → ∀ (C : IClause),
    ((C.foldlM (pevalM τ) (some unit) = ok (some unit) ∧ C.toPropFun ⊓ τ ≤ unit)
    ∨ (C.foldlM (pevalM τ) (some unit) = error true ∧ τ ≤ C.toPropFun)
    ∨ (C.foldlM (pevalM τ) (some unit) = error false)) := by
  intro h_unit C
  have ⟨C⟩ := C
  induction' C with l ls ih generalizing τ
  · simp [pure, Except.pure]
  · simp only [Array.foldlM_cons, pevalM]
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
  induction' C with l ls ih generalizing τ
  · simp [unitPropM, pure, Except.pure]
  · rw [unitPropM, Array.foldlM_cons, pevalM]
    match hl : τ.litValue? l with
    | none =>
      simp only
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
      simp [bind, Except.bind]
      rw [litValue?_true_iff] at hl
      exact le_sup_of_le_left hl
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

#exit

theorem unitPropM_LawfulUP : LawfulUP unitPropM := by
  intro τ C
  have h_SM := C.SatisfiesM_foldlM (init := (none : Option ILit)) (f := pevalM τ)
    (motive := pevalM_SatisfiesM_motive τ C)
    (h0 := by simp [pevalM_SatisfiesM_motive])
    (hf := by
      unfold pevalM_SatisfiesM_motive
      simp only [SatisfiesM_Except_eq, getElem_fin]
      intro i box ih
        -- CC: Is this proof more compact if I use pattern-matching with intro?
      intro
      | none, hbox =>
        intro j hj
        unfold pevalM at hbox
        cases h_tau : τ.litValue? C[i.val] with
        | none =>
          simp [h_tau] at hbox
          cases h_box : box with
          | none => simp [h_box] at hbox
          | some lit => by_cases h_lit : lit = C[i.val] <;> simp [h_box, h_lit] at hbox
        | some b =>
          cases h_box : box with
          | none =>
            subst h_box
            rcases lt_or_eq_of_le (le_of_lt_succ hj) with (h | h)
            · exact ih h
            · cases b
              · replace h := Fin.ext h; subst h; exact h_tau
              · simp [h_tau] at hbox
          | some lit => by_cases h_lit : lit = C[i.val] <;> cases b <;> simp [h_tau, h_box, h_lit] at hbox
      | some lit, hbox =>
        unfold pevalM at hbox
        cases h_tau : τ.litValue? C[i.val] with
        | none =>
          simp [h_tau] at hbox
          cases h_box : box with
          | none =>
            subst h_box
            simp at hbox
            use Array.mem_data_iff_exists_fin.mpr ⟨i, hbox⟩, hbox ▸ h_tau
            intro j hj₁ hj₂
            rcases lt_or_eq_of_le (le_of_lt_succ hj₁) with (h | h)
            · exact ih h
            · simp at ih
              replace h := Fin.ext h; subst h; rw [hbox] at hj₂; contradiction
          | some l =>
            subst h_box
            by_cases hl : l = C[i.val]
            · simp [hl] at hbox
              rw [hbox] at hl
              subst hl
              rcases ih with ⟨hl₁, hl₂, ih⟩
              use hl₁, hl₂
              intro j hj₁ hj₂
              rcases lt_or_eq_of_le (le_of_lt_succ hj₁) with (h | h)
              · exact ih h hj₂
              · replace h := Fin.ext h; subst h; rw [hbox] at hj₂; contradiction
            · simp [hl] at hbox
        | some b =>
          cases b
          · simp [h_tau] at hbox
            subst hbox
            rcases ih with ⟨hlit₁, hlit₂, ih⟩
            use hlit₁, hlit₂
            intro j hj₁ hj₂
            rcases lt_or_eq_of_le (le_of_lt_succ hj₁) with (h | h)
            · exact ih h hj₂
            · replace h := Fin.ext h; subst h; exact h_tau
          · simp [h_tau] at hbox)
  unfold unitPropM
  match hUP : C.foldlM (pevalM τ) none with
  | ok none =>
    simp
    have := SatisfiesM_Except_eq.mp h_SM none hUP
    simp [pevalM_SatisfiesM_motive, -getElem_fin] at this
    rw [← le_bot_iff]
    refine entails_ext.mpr fun τ' hτ' => ?_
    -- CC: Is there a way to do this with a single tactic?
    rw [satisfies_conj] at hτ'; rcases hτ' with ⟨hττ', hCτ'⟩
    rw [Clause.satisfies_iff] at hCτ'; rcases hCτ' with ⟨lit, hlit, hτ'lit⟩
    rw [← Array.mem_data] at hlit
    rcases Array.mem_data_iff_exists_fin.mp hlit with ⟨i, hi⟩
    have := @this i
    rw [hi, litValue?_false_iff] at this
    exact absurd hτ'lit (PropFun.satisfies_neg.mp (entails_ext.mp this τ' hττ'))
  | ok (some lit) =>
    simp
    have := SatisfiesM_Except_eq.mp h_SM (some lit) hUP
    simp [pevalM_SatisfiesM_motive, -getElem_fin] at this
    rcases this with ⟨hlit₁, hlit₂, hlit₃⟩
    rw [← Array.mem_data]
    use hlit₁, hlit₂
    refine entails_ext.mpr fun τ' hτ' => ?_
    rw [satisfies_conj] at hτ'; rcases hτ' with ⟨hCτ', hττ'⟩
    rw [Clause.satisfies_iff] at hCτ'; rcases hCτ' with ⟨lit', hlit', hτ'lit'⟩
    by_cases hlits_eq : lit = lit'
    · subst hlits_eq
      exact hτ'lit'
    · rw [← Array.mem_data] at hlit'
      rcases Array.mem_data_iff_exists_fin.mp hlit' with ⟨i, rfl⟩
      have := hlit₃ (Ne.symm hlits_eq)
      rw [← litValue?_negate_some_iff', Bool.not_false] at this
      rw [satisfies_iff_lits] at hττ'
      have := hττ' this
      rw [toPropFun_neg, PropFun.satisfies_neg] at this
      exact absurd hτ'lit' this
  | error true => simp
  | error false => simp

theorem unitProp_LawfulUP (s e : Nat) : LawfulUP (unitProp' s e) := by
  refine LawfulUP_of_eq_of_LawfulUP ?_ unitPropM_LawfulUP
  intro τ C

  done

#exit
 /-
   unfold unitProp unitPropRes
  intro h_falsified
  split at h_falsified
  <;> try simp at h_falsified
  clear h_falsified
  rename (foldUP τ C = ok none) => h
  refine entails_ext.mpr fun τ' hτ' => ?_
  rw [satisfies_conj] at hτ'
  rcases hτ' with ⟨hττ', hCτ'⟩
  have ⟨lit, hlit, hτ'lit⟩ := Clause.satisfies_iff.mp hCτ'
  rw [← Array.mem_data] at hlit
  have hlv := SatisfiesM_Except_eq.mp (SatisfiesM_UP τ C) none h lit hlit
  clear h hCτ' hlit
  have := satisfies_iff_vars.mp hττ'
  replace hτ'lit := LitVar.satisfies_iff.mp hτ'lit
  cases hpol : polarity lit
  <;> simp [hpol] at hτ'lit
  <;> simp [litValue?, hpol] at hlv
  <;> rw [this hlv] at hτ'lit
  <;> contradiction
 -/
  --unfold unitPropM
  --suffices
  generalize h_unit? : none = unit?
  induction' C with l ls ih generalizing τ unit?
  · simp [unitPropM, pure, Except.pure, ← h_unit?]
  · match hl : τ.litValue? l with
    | none =>
      done

    done
  done

#exit

/-- The "Bool" is true if satisfied, false if not. -/
def pevalUP (τ : PPA) (unit? : Option ILit) (l : ILit) : Except Bool (Option ILit) :=
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

def foldUP (τ : PPA) (C : IClause) := C.foldlM (pevalUP τ) none

def unitPropRes (res : Except Bool (Option ILit)) : MUPResult :=
  match res with
  | ok none => .falsified
  | ok (some lit) => .unit lit
  | error true => .satisfied
  | error false => .multipleUnassignedLiterals

def unitProp (τ : PPA) (C : IClause) : MUPResult :=
  unitPropRes (foldUP τ C)

-- Alternate view of unit propagation, using indexes into an array
def unitPropOnIndexes (τ : PPA) (C : IClause) (s e : Nat) : MUPResult :=
  let min_e := min e C.size
  let rec go (i : Nat) (unit? : Option ILit) : MUPResult :=
    if hi : i < min_e then
      -- This is essentially a clone of `pevalUP` above, except without an Exception monad
      let lit := C.get ⟨i, Nat.lt_of_lt_of_le hi (min_le_right e C.size)⟩
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
  termination_by (min e C.size) - i
  go s none




#exit



theorem SatisfiesM_UP (τ : PPA) (C : IClause) :
    SatisfiesM (fun
      -- If there are no unassigned literals, then all should be false
      | none => ∀ l ∈ C.data, τ.litValue? l = some false
      | some lit => lit ∈ C.data ∧ τ.litValue? lit = none ∧
          (∀ l ∈ C.data, l ≠ lit → τ.litValue? l = some false)) (foldUP τ C) := by
  have := C.SatisfiesM_foldlM (init := (none : Option ILit)) (f := pevalUP τ)
    (motive := motive_fn τ C)
    (h0 := by simp [motive_fn]) -- Why do I have to define it right above? Putting it inline with (motive :=) had sorryAx problems
    (hf := by
      unfold motive_fn
      simp only [SatisfiesM_Except_eq, getElem_fin]
      intro i box ih
        -- Cayden question: Is this proof more compact if I use pattern-matching with intro?
      intro
      | none, hbox =>
        intro j hj
        unfold pevalUP at hbox
        cases h_tau : τ.litValue? C[i.val] with
        | none =>
          simp [h_tau] at hbox
          cases h_box : box with
          | none => simp [h_box] at hbox
          | some lit => by_cases h_lit : lit = C[i.val] <;> simp [h_box, h_lit] at hbox
        | some b =>
          cases h_box : box with
          | none =>
            subst h_box
            rcases lt_or_eq_of_le (le_of_lt_succ hj) with (h | h)
            · exact ih h
            · cases b
              · replace h := Fin.ext h; subst h; exact h_tau
              · simp [h_tau] at hbox
          | some lit => by_cases h_lit : lit = C[i.val] <;> cases b <;> simp [h_tau, h_box, h_lit] at hbox
      | some lit, hbox =>
        unfold pevalUP at hbox
        cases h_tau : τ.litValue? C[i.val] with
        | none =>
          simp [h_tau] at hbox
          cases h_box : box with
          | none =>
            subst h_box
            simp at hbox
            use Array.mem_data_iff_exists_fin.mpr ⟨i, hbox⟩, hbox ▸ h_tau
            intro j hj₁ hj₂
            rcases lt_or_eq_of_le (le_of_lt_succ hj₁) with (h | h)
            · exact ih h
            · simp at ih
              replace h := Fin.ext h; subst h; rw [hbox] at hj₂; contradiction
          | some l =>
            subst h_box
            by_cases hl : l = C[i.val]
            · simp [hl] at hbox
              rw [hbox] at hl
              subst hl
              rcases ih with ⟨hl₁, hl₂, ih⟩
              use hl₁, hl₂
              intro j hj₁ hj₂
              rcases lt_or_eq_of_le (le_of_lt_succ hj₁) with (h | h)
              · exact ih h hj₂
              · replace h := Fin.ext h; subst h; rw [hbox] at hj₂; contradiction
            · simp [hl] at hbox
        | some b =>
          cases b
          · simp [h_tau] at hbox
            subst hbox
            rcases ih with ⟨hlit₁, hlit₂, ih⟩
            use hlit₁, hlit₂
            intro j hj₁ hj₂
            rcases lt_or_eq_of_le (le_of_lt_succ hj₁) with (h | h)
            · exact ih h hj₂
            · replace h := Fin.ext h; subst h; exact h_tau
          · simp [h_tau] at hbox)
  apply SatisfiesM.imp this
  intro
  | none =>
    intro h l hl
    rcases Array.mem_data_iff_exists_fin.mp hl with ⟨i, rfl⟩
    exact h i.isLt
  | some lit =>
    simp [motive_fn]
    intro hlit₁ hlit₂ ih
    use hlit₁, hlit₂
    intro l hl₁ hl₂
    rcases Array.mem_data_iff_exists_fin.mp hl₁ with ⟨i, rfl⟩
    exact ih hl₂

-- Cayden TODO/Q: Allow for [pattern_match] on ResultT? What is [unbox]?
-- Cayden Q: when aesop can't solve something, why does [aesop?] not give anything?
theorem contradiction_of_UP_falsified {τ : PPA} {C : IClause} :
    τ.unitProp C = .falsified → τ.toPropFun ⊓ C.toPropFun ≤ ⊥ := by
  unfold unitProp unitPropRes
  intro h_falsified
  split at h_falsified
  <;> try simp at h_falsified
  clear h_falsified
  rename (foldUP τ C = ok none) => h
  refine entails_ext.mpr fun τ' hτ' => ?_
  rw [satisfies_conj] at hτ'
  rcases hτ' with ⟨hττ', hCτ'⟩
  have ⟨lit, hlit, hτ'lit⟩ := Clause.satisfies_iff.mp hCτ'
  rw [← Array.mem_data] at hlit
  have hlv := SatisfiesM_Except_eq.mp (SatisfiesM_UP τ C) none h lit hlit
  clear h hCτ' hlit
  have := satisfies_iff_vars.mp hττ'
  replace hτ'lit := LitVar.satisfies_iff.mp hτ'lit
  cases hpol : polarity lit
  <;> simp [hpol] at hτ'lit
  <;> simp [litValue?, hpol] at hlv
  <;> rw [this hlv] at hτ'lit
  <;> contradiction

-- Is it better to say that ¬(τ ≤ l), or that τ.litValue? l = none?
theorem extended_of_UP_unit {τ : PPA} {C : IClause} {l : ILit} :
    τ.unitProp C = .unit l →
      l ∈ C ∧
      τ.litValue? l = none ∧
      C.toPropFun ⊓ τ.toPropFun ≤ l.toPropFun ⊓ τ := by
  unfold unitProp unitPropRes
  intro h_unit
  split at h_unit
  <;> try simp at h_unit
  rename ILit => lit; subst h_unit
  rename (foldUP τ C = ok (some lit)) => h
  have hlv := SatisfiesM_Except_eq.mp (SatisfiesM_UP τ C) (some lit) h
  clear h
  rcases hlv with ⟨hlit, hτlit, ih⟩
  rw [← Array.mem_data]
  use hlit, hτlit
  refine entails_ext.mpr fun τ' hτ' => ?_
  rw [satisfies_conj] at hτ'; rcases hτ' with ⟨hCτ', hττ'⟩
  rw [satisfies_iff_lits] at hττ'
  rw [Clause.satisfies_iff] at hCτ'; rcases hCτ' with ⟨m, hm, hmτ'⟩
  by_cases heq : m = lit
  · subst heq
    rw [← satisfies_iff_lits] at hττ'
    rw [satisfies_conj]
    exact ⟨hmτ', hττ'⟩
  · rw [← Array.mem_data] at hm
    replace ih := ih _ hm heq
    have := litValue?_negate τ m
    simp only [ih, Option.map_some', Bool.not_false] at this
    have := hττ' this
    simp at this
    exact absurd hmτ' this

end monadic /- section -/

end PPA
