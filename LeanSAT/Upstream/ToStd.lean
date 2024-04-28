/-
Copyright (c) 2024 The LeanSAT Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio, Cayden Codel
-/

import Std

def List.enum' (L : List α) : List (Fin L.length × α) :=
  let rec go (rest : List α) (i : Nat)
              (h : i + rest.length = L.length) :=
    match rest, h with
    | [], _ => []
    | (x :: xs), h =>
      (⟨i, (h.symm ▸ Nat.lt_add_of_pos_right (Nat.zero_lt_succ _))⟩, x)
      :: go xs (i+1) (by
        simp [←h, Nat.add_succ, Nat.succ_add])
  go L 0 (by simp)

theorem List.mem_set : ∀ {l : List α} {i : Nat} {a a' : α},
    a' ∈ l.set i a → a' ∈ l ∨ a' = a
  | nil, _, _, _, h => Or.inl h
  | cons _ bs, 0, _, _, h => by
    simp only [set, mem_cons] at h ⊢
    cases h
    · right; assumption
    · left; right; assumption
  | cons b bs, Nat.succ n, _, _, h => by
    simp only [set, mem_cons] at h ⊢
    cases h
    . left; left; assumption
    · rename _ => h
      cases mem_set h
      · left; right; assumption
      · right; assumption

def Fin.pred? : Fin n → Option (Fin n)
| ⟨0, _⟩ => none
| ⟨i+1,h⟩ => some ⟨i, Nat.le_of_succ_le h⟩

/-- if i > 0, then i-1, else none -/
def Fin.predCast : Fin n → Option (Fin n.pred)
| ⟨0, _⟩ => none
| ⟨i+1,h⟩ => some ⟨i, Nat.le_pred_of_lt h⟩

/-- if i < Fin.last n then i, else none -/
-- NOTE: in mathlib, castPred : Fin (n + 2) → Fin (n + 1)
def Fin.castPred' (i : Fin n) : Option (Fin n.pred) :=
  match n with
  | 0 => i.elim0
  | n+1 =>
    if h : ↑i = n
    then none
    else some ⟨i, by simp; exact Nat.lt_of_le_of_ne (Nat.le_of_succ_le_succ i.isLt) h⟩

def Fin.succ? : {n : Nat} → Fin n → Option (Fin n)
| 0, i => i.elim0
| n+1, ⟨i,_⟩ =>
  if h : i < n
  then some ⟨i+1, Nat.succ_le_succ h⟩
  else none

def Function.iterate (f : α → α) : Nat → (α → α)
| 0 => id
| n+1 => iterate f n ∘ f

/-! Array -/

def Array.init (n : Nat) (f : Fin n → α) : Array α := Id.run do
  let mut A := Array.mkEmpty n
  for h:i in [0:n] do
    A := A.push (f ⟨i,h.2⟩)
  return A

def Array.initM [Monad m] (n : Nat) (f : Fin n → m α) : m (Array α) := do
  let mut A := Array.mkEmpty n
  for h:i in [0:n] do
    A := A.push (← f ⟨i,h.2⟩)
  return A

theorem Array.init_zero : Array.init 0 f = #[] := by
  simp [init, Id.run, forIn', Std.Range.forIn']
  unfold Std.Range.forIn'.loop
  simp

theorem Array.init_succ {f : Fin n.succ → α}
  : Array.init n.succ f = (
      Array.init n (fun i => f ⟨i,Nat.lt_trans i.isLt (by exact Nat.le_refl _)⟩)
    ).push (f ⟨n, by exact Nat.le_refl _⟩)
  := by
  simp [init, Id.run, forIn', Std.Range.forIn']
  suffices ∀ i (hi : i ≤ n) o (_ : o.size = n-i),
    Std.Range.forIn'.loop (m := Id) 0 n.succ 1
      (fun i h r => ForInStep.yield (push r (f ⟨i, h.2⟩)))
      i.succ (n-i)
      (Nat.zero_le _)
      o
    = push (Std.Range.forIn'.loop (m := Id) 0 n 1
      (fun i h r => ForInStep.yield (push r (f ⟨i, Nat.le_step h.2⟩)))
      i (n-i)
      (Nat.zero_le _)
      o) (f ⟨n, Nat.lt_succ_self n⟩)
    by
    have := this n (Nat.le_refl _) #[] (by simp)
    simp at this
    exact this
  intro i hi o ho
  induction i generalizing o with
  | zero =>
    unfold Std.Range.forIn'.loop
    unfold Std.Range.forIn'.loop
    simp
  | succ i ih =>
    conv => lhs; unfold Std.Range.forIn'.loop
    conv => rhs; unfold Std.Range.forIn'.loop
    simp
    have hn := Nat.sub_lt_of_pos_le (Nat.succ_pos _) hi
    have hn' : n - Nat.succ i < Nat.succ n := Nat.le_step hn
    simp [hn, hn']
    have : n - Nat.succ i + 1 = n - i := by
      simp [Nat.sub_succ]
      rw [Nat.add_one, Nat.succ_pred_eq_of_pos (Nat.zero_lt_sub_of_lt hi)]
    suffices ∀ j, j = n - Nat.succ i + 1 →
      Std.Range.forIn'.loop (m := Id)  _ _ _ _ _ j (Nat.zero_le _) _
      = push (Std.Range.forIn'.loop (m := Id) _ _ _ _ _ j (Nat.zero_le _) _) _
      from this _ rfl
    intro j hj
    rw [this] at hj
    cases hj
    apply ih
    exact Nat.le_of_lt hi
    simp [ho, this]

@[simp] theorem Array.mem_push (A : Array α) (x y : α)
  : y ∈ A.push x ↔ y ∈ A ∨ y = x := by
  simp [push, Array.mem_def]

@[simp]
theorem Array.size_init : (Array.init n f).size = n := by
  induction n
  . simp [size, init_zero]
  . next ih =>
    simp [init_succ]; exact ih

@[simp]
theorem Array.get_init {i : Nat} {h} : (Array.init n f)[i]'h = f ⟨i, @size_init n _ f ▸ h⟩ := by
  induction n generalizing i with
  | zero => simp at h; exact False.elim <| Nat.not_lt_zero _ h
  | succ n ih =>
    simp [init_succ, get_push]
    split
    next h =>
      have := @ih (fun i => f ⟨i,Nat.lt_trans i.isLt (by exact Nat.le_refl _)⟩) i (by simp; assumption)
      simp at this ⊢
      rw [this]
    next h' =>
      simp at h'
      have : i = n := Nat.le_antisymm
        (Nat.le_of_succ_le_succ (by rw [size_init] at h; exact h))
        h'
      cases this
      congr

def Array.pop? (A : Array α) :=
  match A.back? with
  | none => none
  | some a => some (A.pop, a)

@[simp] theorem Array.size_pop?
  : A.pop? = some (A', a) → size A' + 1 = size A
  := by rcases A with ⟨h,t⟩
          <;> simp [pop?, back?, getElem?, pop]
        rintro rfl
        simp

def Array.maxBy (f : α → β) [Max β] (A : Array α) : Option β :=
  if h : A.size > 0 then
    let b0 := f A[0]
    some <| A.foldl (start := 1) (max · <| f ·) b0
  else
    none

theorem Array.mkArray_succ (n : Nat) (a : α) :
    Array.mkArray (n + 1) a = #[a] ++ (Array.mkArray n a) := by
  apply Array.ext'; simp

theorem Array.mkArray_succ' (n : Nat) (a : α) :
    Array.mkArray (n + 1) a = (Array.mkArray n a).push a := by
  apply Array.ext'
  simp [mkArray_data, List.replicate]
  induction n with
  | zero => rfl
  | succ n ih => simp; exact ih

@[simp] theorem Array.foldl_empty (f : β → α → β) (init : β) (start stop : Nat) :
    Array.foldl f init #[] start stop = init := by
  simp [foldl, foldlM, Id.run]
  by_cases h : stop = 0
  · simp [h, foldlM.loop]
  · simp [h]; simp [foldlM.loop]

@[simp] theorem Array.foldl_nil (f : β → α → β) (init : β) (start stop : Nat) :
    Array.foldl f init { data := [] } start stop = init :=
  Array.foldl_empty f init start stop

@[simp] theorem Array.foldl_cons (f : β → α → β) (init : β) (a : α) (as : List α) :
    Array.foldl f init { data := a :: as } 0 (size { data := a :: as }) =
      Array.foldl f (f init a) { data := as } 0 (size { data := as }) := by
  simp only [foldl_eq_foldl_data]; rfl

@[simp] theorem Array.foldl_append (f : β → α → β) (init : β) (A B : Array α) :
    Array.foldl f init (A ++ B) 0 (size (A ++ B)) =
      Array.foldl f (Array.foldl f init A 0 (size A)) B 0 (size B) := by
  have ⟨A⟩ := A
  have ⟨B⟩ := B
  simp only [foldl_eq_foldl_data, append_data]
  exact List.foldl_append _ _ _ _

@[simp] theorem Array.foldlM_empty {m : Type v → Type w} [Monad m] (f : β → α → m β)
    (init : β) (start stop : Nat) :
    Array.foldlM f init #[] start stop = pure init := by
  simp [foldlM, Id.run]
  by_cases h : stop = 0
  · simp [h, foldlM.loop]
  · simp [h]; simp [foldlM.loop]

@[simp] theorem Array.foldlM_nil {m : Type v → Type w} [Monad m] (f : β → α → m β)
    (init : β) (start stop : Nat) :
    Array.foldlM f init { data := [] } start stop = pure init :=
  Array.foldlM_empty f init start stop

@[simp] theorem Array.foldlM_cons {m : Type v → Type w} [Monad m] (f : β → α → m β)
    (init : β) (a : α) (as : List α) :
    Array.foldlM f init { data := a :: as } 0 (size { data := a :: as }) = do
      { Array.foldlM f (← f init a) { data := as } 0 (size { data := as }) } := by
  simp only [foldlM_eq_foldlM_data, List.foldlM]

@[simp] theorem Array.foldlM_cons_succ {m : Type v → Type w} [Monad m] (f : β → α → m β)
    (init : β) (a : α) (as : List α) (start stop : Nat) :
    start < stop → stop < size { data := a :: as } →
      Array.foldlM f init { data := a :: as } (start + 1) (stop + 1) =
        Array.foldlM f init { data := as } start stop := by
  sorry
  done

@[simp] theorem Array.foldlM_trivial {m : Type v → Type w} [Monad m] (f : β → α → m β)
    (init : β) (as : Array α) (i : Nat) :
    as.foldlM f init i i = pure init := by
  simp [foldlM, Id.run]
  split <;> rename _ => hi
  · simp [foldlM.loop]
  · rw [foldlM.loop]
    simp at hi
    simp [Nat.not_lt_of_le (Nat.le_of_lt hi)]

@[simp] theorem Array.foldl_trivial (f : β → α → β)
    (init : β) (as : Array α) (i : Nat) :
    as.foldl f init i i = init := by
  simp [foldl, Id.run]

theorem Array.foldlM_gt {m : Type v → Type w} [Monad m] {A : Array α} {i : Nat} :
    i > A.size → ∀ (f : β → α → m β) init, A.foldlM f init i = pure init := by
  intro hi f init
  simp [foldlM, Id.run]
  rw [foldlM.loop]
  simp [Nat.not_lt_of_le (Nat.le_of_lt hi)]

theorem Array.foldl_gt {A : Array α} {i : Nat} :
    i > A.size → ∀ (f : β → α → β) init, A.foldl f init i = init := by
  intro hi f init
  simp [Array.foldl, Id.run]
  exact Array.foldlM_gt (m := Id) hi f init

theorem Array.exists_split {A : Array α} {i : Nat} (hi : i ≤ A.size) :
    ∃ (B C : Array α), A = B ++ C ∧ B.size = i ∧ C.size = A.size - i := by
  have ⟨A⟩ := A
  induction A with
  | nil =>
    simp at hi; subst hi
    simp
    exact ⟨#[], #[], rfl, rfl, rfl⟩
  | cons a as ih =>
    simp at hi
    rcases Nat.eq_or_lt_of_le hi with (rfl | h_lt)
    · refine ⟨{ data := a :: as }, #[], rfl, by simp, by simp⟩
    · simp at ih
      rcases ih (Nat.le_of_lt_succ h_lt) with ⟨B, C, h_eq, hB, hC⟩
      refine ⟨{ data := [a] } ++ B, C, ?_, ?_, ?_⟩
      · simp [Array.append_assoc, ← h_eq]
        have :  a :: as = [a] ++ as := rfl
        rw [this]
        sorry
        done
      · sorry
        done
      · sorry
        done
      done
    done
  done

@[simp] theorem Array.size_set! (A : Array α) (i : Nat) (v : α) : (A.set! i v).size = A.size := by
  rw [set!, Array.size_setD]

/-! List -/

def List.distinct [DecidableEq α] (L : List α) : List α :=
  L.foldl (·.insert ·) []

def List.isDistinct [BEq α] : List α → Bool
| [] => true
| x::xs => !xs.contains x && xs.isDistinct

def List.fins (n : Nat) : List (Fin n) :=
  finsAux n (Nat.le_refl _) []
where
  finsAux : (i : Nat) → i ≤ n → List (Fin n) → List (Fin n)
  | 0, _, acc => acc
  | i+1, h, acc => finsAux i (Nat.le_of_lt h) (⟨i,h⟩ :: acc)

@[simp] theorem List.length_fins (n : Nat) : (List.fins n).length = n := by
  unfold fins
  suffices ∀ i (hi : i ≤ n) acc, length (fins.finsAux n i hi acc) = length acc + i
    by have := this n (Nat.le_refl _) []; simp at this; exact this
  intro i hi acc
  induction i generalizing acc <;>
    (unfold fins.finsAux; simp_all [Nat.succ_add, Nat.add_succ])

@[simp] theorem List.fins_zero : List.fins 0 = [] := rfl

theorem List.fins_succ (n : Nat)
  : List.fins (n.succ) = (List.fins n).map (Fin.castSucc) ++ [Fin.last n] := by
  unfold fins
  conv => lhs; unfold fins.finsAux
  suffices ∀ i (hi : i ≤ n) acc,
      fins.finsAux n.succ i (trans hi (Nat.le_succ _)) (map Fin.castSucc acc ++ [Fin.last n]) =
        map Fin.castSucc (fins.finsAux n i hi acc) ++ [Fin.last n]
    by have := this n (Nat.le_refl _) []; simpa using this
  intro i hi acc
  induction i generalizing acc with
  | zero => unfold fins.finsAux; simp
  | succ i ih =>
    unfold fins.finsAux
    replace ih := ih (Nat.le_of_lt hi) (⟨i,hi⟩ :: acc)
    simpa using ih

@[simp] theorem List.get_fins (n : Nat) (i : Fin (List.fins n).length)
  : (List.fins n).get i = ⟨i, by cases i; simp; simp_all⟩ := by
  rcases i with ⟨j,hj⟩
  revert hj; simp; intro hj
  apply Option.some_inj.mp
  rw [← get?_eq_get]
  induction n
  · contradiction
  next n' ih =>
  conv => lhs; rw [fins_succ]
  by_cases h : j = n'
  · rw [get?_append_right]
    · simp [h, Fin.last]
    · simp [h]
  · have : j < n' := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hj) h
    have := ih this
    rw [get?_append, get?_map, this]
    · simp
    · simp; assumption

@[simp] theorem List.mem_fins (n : Nat) (x : Fin n)
  : x ∈ List.fins n := by
  rw [mem_iff_get]
  refine ⟨⟨x,?_⟩,?_⟩
  · simp
  · simp

/- Better parallelism primitive, that is actually like Scala's Future -/
def TaskIO (α) := IO (Task (Except IO.Error α))

namespace TaskIO

instance : Monad TaskIO where
  pure a := pure (f := IO) <| Task.pure (Except.ok a)
  bind a f := bind (m := IO) a (fun task =>
    IO.bindTask task (fun res => do
      let res ← ofExcept res
      f res))

instance : MonadLift IO TaskIO where
  monadLift io := io.map (fun a => Task.pure (Except.ok a))

def wait (task : TaskIO α) : IO α := do
  let task ← task
  let x ← IO.wait task
  ofExcept x

instance : MonadExceptOf IO.Error TaskIO where
  throw e := show IO _ from throw e
  tryCatch a f := bind (m := IO) a (IO.bindTask · fun
    | .ok a => show TaskIO _ from pure a
    | .error e => f e)

def par [ForIn IO σ α] (xs : σ) (f : α → TaskIO β)
    : TaskIO (List β) := show IO _ from do
  let mut tasks := #[]
  for x in xs do
    tasks := tasks.push (← (f x))
  let task ← IO.mapTasks (fun bs => do
    return ←bs.mapM (fun b => ofExcept b)
  ) tasks.toList
  return task

def parUnit [ForIn IO σ α] (xs : σ) (f : α → TaskIO Unit)
    : TaskIO Unit := do
  let _allUnits ← par xs f
  return ()

def parTasks [ForIn IO σ α] (xs : σ) (f : α → IO β)
    : TaskIO (List β) := do
  par xs (fun a => liftM (n := IO) <| IO.asTask (do f a))

def parTasksUnit [ForIn IO σ α] (xs : σ) (f : α → IO Unit)
    : TaskIO Unit := do
  parUnit xs (fun a => liftM (n := IO) <| IO.asTask (do f a))

end TaskIO

def Option.forIn [Monad m] (o : Option α) (b : β) (f : α → β → m (ForInStep β)) : m β := do
  match o with
  | none => return b
  | some a =>
  match ← f a b with
  | .done b => return b
  | .yield b => return b

instance : ForIn m (Option α) α where
  forIn := Option.forIn

def IO.timeMs (prog : IO α) : IO (Nat × α) := do
  let start ← IO.monoMsNow
  let res ← prog
  let end_ ← IO.monoMsNow

  return (end_ - start, res)

instance : GetElem String Nat Char (fun s i => i < s.length) where
  getElem | xs, i, _ => xs.get (String.Pos.mk i)

def randFin (n) (_h : n > 0) : IO (Fin n) := do
  let i ← IO.rand 0 n.pred
  if h : i < n then
    return ⟨i,h⟩
  else
    panic! s!"failed to get random number {i} < {n}"

/- Generate a random permutation of the list.
Implementation is quadratic in length of L. -/
def IO.randPerm (L : List α) : IO (List α) :=
  randPermTR L [] 0
where randPermTR (L acc n) := do
  match L with
  | [] => return acc
  | x::xs =>
    let idx ← IO.rand 0 n
    let acc' := acc.insertNth idx x
    randPermTR xs acc' (n+1)


@[simp]
theorem List.sizeOf_filter [SizeOf α] (f) (L : List α)
  : sizeOf (List.filter f L) ≤ sizeOf L
  := by
  induction L <;> simp [filter]
  split
  . simp
    apply Nat.add_le_add_left
    assumption
  . apply Nat.le_trans ?_ (Nat.le_add_left _ _)
    assumption

theorem List.sizeOf_filter_lt_of_ne [SizeOf α] (f) (L : List α)
    (h : List.filter f L ≠ L)
  : sizeOf (List.filter f L) < sizeOf L
  := by
  induction L <;> simp [filter] at *
  next hd tl ih =>
  split
  next hHd =>
    simp [hHd] at h
    simp [_sizeOf_1]
    apply Nat.add_lt_add_left
    apply ih
    assumption
  next hHd =>
    clear h hHd
    apply Nat.lt_of_le_of_lt (sizeOf_filter _ _)
    rw [Nat.add_comm, Nat.add_comm 1, Nat.add_one, Nat.add_succ]
    apply Nat.succ_le_succ
    apply Nat.le_add_right

def List.subtypeSize [SizeOf α] : (L : List α) → List {a : α // sizeOf a < sizeOf L}
| [] => []
| x::xs =>
  have : sizeOf x < sizeOf (x::xs) := by
    simp
    calc sizeOf x
      _ < sizeOf x + 1 := Nat.lt_succ_self _
      _ = 1 + sizeOf x := by rw [Nat.add_comm]
      _ ≤ 1 + sizeOf x + sizeOf xs := Nat.le_add_right _ _
  ⟨x, this⟩ :: xs.subtypeSize.map (fun ⟨a,h⟩ =>
    ⟨a, by
      simp
      calc sizeOf a
      _ < sizeOf xs := h
      _ ≤ 1 + sizeOf x + sizeOf xs := Nat.le_add_left _ _⟩)

unsafe def Array.subtypeSizeUnsafe [SizeOf α] (A : Array α) : Array {a : α // sizeOf a < sizeOf A} :=
  unsafeCast A

@[implemented_by subtypeSizeUnsafe]
def Array.subtypeSize [SizeOf α] : (A : Array α) → Array {a : α // sizeOf a < sizeOf A}
| ⟨L⟩ => ⟨L.subtypeSize.map (fun ⟨x,h⟩ => ⟨x, by simp; rw [Nat.add_comm]; apply Nat.lt_add_right; exact h⟩)⟩

@[simp] theorem List.find?_map (p : β → Bool) (f : α → β) (L : List α)
  : List.find? p (List.map f L) = Option.map f (List.find? (p ∘ f) L)
  := by induction L <;> simp [find?]; split <;> simp [*]

/-- Like `forDiagM`, but only runs `f e e'` (not `f e e`). -/
@[simp] def List.forPairsM [Monad m] (f : α → α → m PUnit) : List α → m PUnit
  | [] => pure ⟨⟩
  | x :: xs => do xs.forM (f x); xs.forPairsM f

@[simp]
def Std.AssocList.ofList : List (α × β) → Std.AssocList α β
| [] => .nil
| (a,b)::tail => .cons a b (ofList tail)

@[simp] theorem Std.AssocList.toList_ofList (L : List (α × β))
  : toList (ofList L) = L
  := by induction L <;> simp [*]

@[inline]
def Option.expectSome (err : Unit → ε) : Option α → Except ε α
| none => .error (err ())
| some a => .ok a

structure NonemptyList (α) where
  hd : α
  tl : List α

@[inline]
def List.expectNonempty (err : Unit → ε) : List α → Except ε (NonemptyList α)
| [] => .error (err ())
| hd::tl => .ok ⟨hd,tl⟩


def PrinterM := StateM String
def PrinterM.putStr : String → PrinterM Unit :=
  fun string state => ((), state.append string)
def PrinterM.run : PrinterM Unit → String := (StateT.run · "" |>.2)

instance : Monad PrinterM := show Monad (StateM String) from inferInstance

def IO.FS.withTempFile (f : System.FilePath → IO α) : IO α := do
  let mut file := ".tmp" ++ toString (← IO.rand 0 999999)
  while ← System.FilePath.pathExists file do
    file := file ++ toString (← IO.rand 0 999999)

  IO.FS.writeFile file ""
  let res ←
    try f file
    finally
      if ← System.FilePath.pathExists file then
        IO.FS.removeFile file

  return res

@[simp] theorem Array.ofFn_data (f : Fin n → α)
  : (Array.ofFn f).data = (List.fins n).map f := by
  ext i x
  simp [List.get?_eq_some]
  simp only [← Array.getElem_eq_data_get, Array.getElem_ofFn]
  refine ⟨?mp,?mpr⟩
  case mp =>
    rintro ⟨h,rfl⟩
    refine ⟨_,?_,rfl⟩
    simpa using h
  case mpr =>
    rintro ⟨_,⟨h,rfl⟩,rfl⟩
    simpa using h
