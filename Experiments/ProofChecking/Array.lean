import Std
import Init.Data.Nat.Basic
import LeanSAT.Upstream.ToStd
import Std.Data.List.Lemmas

@[simp] def comm_in_second_arg (f : β → α → β) : Prop :=
  ∀ (b : β) (a₁ a₂ : α), f (f b a₁) a₂ = f (f b a₂) a₁

namespace List

-- Cayden notes: making a List.foldlIdxM is hard, because the Fin type would be fixed on
-- the original input L, but would essentially be 0 at each point.

theorem foldl_of_comm (L : List α) (f : β → α → β) (init : β) :
    comm_in_second_arg f →
    ∀ a ∈ L, ∃ (acc : β), L.foldl f init = f acc a := by
  intro hf
  induction L with
  | nil => simp
  | cons x xs ih =>
    intro a ha
    rcases List.mem_cons.mp ha with (rfl | ha)
    · simp
      sorry
      done
    sorry
    done
  done

end List

namespace Array

open Nat

theorem ne_empty_iff_size_pos {A : Array α} : A ≠ #[] ↔ 0 < A.size := by
  have ⟨A⟩ := A
  have : #[] = ({ data := [] } : Array α) := rfl
  simp [this]
  exact Iff.symm List.length_pos

theorem mem_data_iff_exists_fin {A : Array α} {a : α} :
    a ∈ A.data ↔ ∃ (i : Fin A.size), A[i] = a := by
  constructor
  · exact List.get_of_mem
  · rintro ⟨i, rfl⟩
    exact Array.getElem_mem_data A i.isLt

/-
def head (A : Array α) (hA : A.size > 0) : α := A.get ⟨0, hA⟩
def headD (A : Array α) (default : α) : α := if h : A.size > 0 then A.head h else default

#check List.tail
#check Array.back
/-- The last element in the array. Not to be confused with `List.tail`, which drops the head. -/
def tail (A : Array α) (hA : A.size > 0) : α := A.get ⟨A.size - 1, sub_one_lt_of_le hA le.refl⟩
def tailD (A : Array α) (default : α) : α := if h : A.size > 0 then A.tail h else default

def setTail (A : Array α) (hA : A.size > 0) (a : α) : Array α :=
  A.set ⟨A.size - 1, sub_one_lt_of_le hA le.refl⟩ a

def setTail! (A : Array α) (a : α) : Array α :=
  if h : A.size > 0 then A.set ⟨A.size - 1, sub_one_lt_of_le h le.refl⟩ a else A

@[simp]
theorem size_setTail (A : Array α) (hA : A.size > 0) (a : α) : (A.setTail hA a).size = A.size := by
  simp [setTail]

@[simp]
theorem size_setTail! (A : Array α) (a : α) : (A.setTail! a).size = A.size := by
  simp [setTail!]; split <;> simp

@[simp]
theorem tail_setTail (A : Array α) (hA : A.size > 0) (a : α) : (A.setTail hA a).tail (size_setTail A hA a ▸ hA) = a := by
  simp [tail, setTail]
  done

#exit -/

def setBack (A : Array α) (a : α) : Array α :=
  if h : A.size > 0 then A.set ⟨A.size - 1, sub_one_lt_of_le h le.refl⟩ a else A

@[simp]
theorem size_setBack (A : Array α) (a : α) : (A.setBack a).size = A.size := by
  simp [setBack]; split <;> simp

theorem back_setBack [Inhabited α] (A : Array α) (a : α) : A.size > 0 → (A.setBack a).back = a := by
  intro hA; simp [setBack, hA, Option.getD, Array.back?, Array.get?_set]

-- See `#check Array.extract`

@[simp] theorem extract_nil (start stop : Nat) : ({ data := [] } : Array α).extract start stop = #[] :=
  extract_empty _ _

def extractCore' (A acc : Array α) (start stop : Nat) :=
  A.foldl Array.push acc start stop

def extract' (A : Array α) (start stop : Nat) :=
  extractCore' A #[] start stop

@[simp]
theorem extractCore'_empty (acc : Array α) (start stop : Nat) :
    Array.extractCore' (#[] : Array α) acc start stop = acc := by
  simp [extractCore']

@[simp]
theorem extractCore'_nil (acc : Array α) (start stop : Nat) :
    Array.extractCore' ({ data := [] } : Array α) acc start stop = acc := by
  simp [extractCore']

@[simp]
theorem extractCore'_eq (A acc : Array α) (s : Nat) :
    A.extractCore' acc s s = acc := by
  simp [extractCore']

theorem extractCore'_gt (A acc : Array α) (start stop : Nat) :
    start > stop → Array.extractCore' A acc start stop = acc := by
  intro h
  simp [extractCore']
  sorry
  done

/-
@[simp]
theorem extractCore'_cons (a : α) (as : List α) (acc : Array α) (start stop : Nat) :
    Array.extractCore' { data := a :: as } acc start stop = do
      { let acc' := if start = 0 then acc.push a else acc
        Array.extractCore' { data := as } acc' (start - 1) (stop - 1) } := by
  simp [extractCore']
  sorry -/

--#check extract_loop_zero

@[simp]
theorem extract'_lt (A : Array α) {start stop : Nat} :
    start < stop → stop < A.size → A.extract' start stop = A.extract' s s := by sorry
  --induction A with
  --| mk as => simp [extract', Array.extract, Array.foldl, Array.push]

/-
-- TODO: A better implementation exists, probably by writing a custom looper/recursive function
def foldlIdxM {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m]
    (as : Array α) (f : β → Fin as.size → α → m β) (init : β) (start := 0) (stop := as.size) : m β :=
  return Prod.fst <| ← as.foldlM (fun (acc, idx) a =>
    -- Cayden TODO: Should this be stop instead of as.size?
    if hidx : idx < as.size then
      return (← f acc ⟨idx, hidx⟩ a, idx + 1)
    else
      return (acc, 0)) (⟨init, start⟩ : β × Nat) start stop

@[inline]
def foldlIdx {α : Type u} {β : Type v} (as : Array α) (f : β → Fin as.size → α → β)
    (init : β) (start := 0) (stop := as.size) : β :=
  Id.run <| as.foldlIdxM f init start stop

def foldrIdxM {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m]
    (as : Array α) (f : Fin as.size → α → β → m β) (init : β) (start := as.size) (stop := 0) : m β :=
  return Prod.fst <| ← (as.foldrM (fun a (acc, idx) =>
    if hidx : idx - 1 < as.size ∧ idx > stop then
      return (← f ⟨idx - 1, hidx.1⟩ a acc, idx - 1)
    else
      return (acc, 0)) (⟨init, start⟩ : β × Nat) start stop)

@[inline]
def foldrIdx {α : Type u} {β : Type v} (as : Array α) (f : Fin as.size → α → β → β)
    (init : β) (start := as.size) (stop := 0) : β :=
  Id.run <| as.foldrIdxM f init start stop

@[simp]
theorem foldlIdxM_empty {m : Type v → Type w} [Monad m] [LawfulMonad m]
    (f : β → Fin 0 → α → m β) (init : β) (start stop : Nat) :
    Array.foldlIdxM #[] f init start stop = pure init := by
  simp [foldlIdxM]
  stop
  done

@[simp]
theorem foldlIdxM_nil {m : Type v → Type w} [Monad m] [LawfulMonad m]
    (f : β → Fin 0 → α → m β) (init : β) (start stop : Nat) :
    Array.foldlIdxM { data := [] } f init start stop = pure init :=
  Array.foldlIdxM_empty f init start stop

/-
@[simp]
theorem foldlIdxM_cons {m : Type v → Type w} [Monad m] [LawfulMonad m]
     (a : α) (as : List α) (f : β → Fin (a :: as).length → α → m β) (init : β) :
    Array.foldlIdxM { data := a :: as } f init 0 (size { data := a :: as }) = do
      { Array.foldlIdxM { data := as } f (← f init 0 a) 0 (size { data := as }) } := by
  simp [foldlIdxM] -/

--theorem Array.foldlIdx_index_eq (as : Array α) (f : β → Fin as.size → α → β) (init : β) :
  --as.foldlIdx = something about Array.enum

theorem foldlIdx_of_comm (A : Array α) (f : β → Fin A.size → α → β) (init : β) :
    -- Commutativity assumption
    (∀ (acc : β) (idx₁ idx₂ : Fin A.size),
      f (f acc idx₁ (A.get idx₁)) idx₂ (A.get idx₂) = f (f acc idx₂ (A.get idx₂)) idx₁ (A.get idx₁)) →

    -- For all indexes, we can move its function application to the end
    ∀ (idx : Fin A.size), ∃ (acc : β), A.foldlIdx f init = f acc idx (A.get idx) := by sorry

-- TODO: Check to see if a similar theorem exists for lists.
theorem foldl_of_comm (A : Array α) {f : β → α → β} (init : β) :
    (∀ (acc : β) (a₁ a₂ : α), f (f acc a₁) a₂ = f (f acc a₂) a₁) →
    ∀ a ∈ A, ∃ (acc : β), A.foldl f init = f acc a := by sorry -/


/-! # setF - a dynamic sizing setting function for arrays -/

/- A new set operation that fills in with a provided default value until hitting the index -/

/-
Custom-written C++ code is yet to be written.
Below is a functional implementation.

One alternate implementation is to use Array.ofFn to copy over the array.
In order to determine if it's better, profile it.

Note: @implemented_by can refer to other Lean implementations!
  That can help profile the different versions at runtime.
-/

def setF (A : Array α) (i : Nat) (v default : α) : Array α :=
  if hi : i < A.size then
    A.set ⟨i, hi⟩ v
  else
    let rec go (j : Nat) (A' : Array α) : Array α :=
      match j with
      | 0 => A'.push v
      | j + 1 => go j (A'.push default)
    go (i - A.size) A

-- Cayden TODO: An alternate setting that transforms the cell rather than overwriting it
-- Possible time savings
def setF' (A : Array α) (i : Nat) (f : Option α → α) (default : α) : Array α :=
  if hi : i < A.size then
    A.set ⟨i, hi⟩ (f (A.get ⟨i, hi⟩))
  else
    let rec go (j : Nat) (A' : Array α) : Array α :=
      match j with
      | 0 => A'.push (f none)
      | j + 1 => go j (A'.push default)
    go (i - A.size) A

theorem setF_eq_setF' {A : Array α} {i : Nat} {f : Option α → α} {v default : α} :
    (∀ (x : Option α), f x = v) → A.setF i v default = A.setF' i f default := by
  intro hf
  simp [setF, setF']
  by_cases hi : i < A.size
  <;> simp [hi, hf]
  · sorry

section setF

theorem setF_eq_set {A : Array α} {i : Nat} (hi : i < A.size) (v default : α) :
    A.setF i v default = A.set ⟨i, hi⟩ v := by
  simp [setF, hi]

theorem setF_eq_set' {A : Array α} (i : Fin A.size) :
    ∀ (v default), A.setF i v default = A.set i v :=
  Array.setF_eq_set i.isLt

theorem setF_eq_push {A : Array α} (v default : α) :
    A.setF A.size v default = A.push v := by
  simp [setF, setF.go]

-- CC TODO: Private lemmas for the next two, since they refer to setF.go?
theorem setF_go_eq (A : Array α) (i : Nat) (v default : α) :
    setF.go v default i A = (A ++ mkArray i default).push v := by
  induction i generalizing A with
  | zero => rfl
  | succ i ih =>
    rw [setF.go, ih (push A default)]
    apply congrArg₂
    · rw [mkArray_succ, Array.push_eq_append_singleton, Array.append_assoc]
    · rfl

theorem size_setF_go (A : Array α) (i : Nat) (v default : α) :
    (Array.setF.go v default i A).size = A.size + i + 1 := by
  rw [Array.setF_go_eq, Array.size_push, Array.size_append, Array.size_mkArray]

@[simp] theorem size_setF (A : Array α) (i : Nat) (v default : α) :
    (A.setF i v default).size = max A.size (i + 1) := by
  rcases Nat.lt_trichotomy i A.size with (hi | rfl | hi)
  · rw [setF_eq_set hi, size_set]
    exact (Nat.max_eq_left hi).symm
  · rw [setF_eq_push, size_push, Nat.max_eq_right (le_succ A.size)]
  · simp [setF, Nat.lt_asymm hi, setF_go_eq, size_append]
    have h_le : A.size ≤ i + 1 := by
      exact Nat.le_trans (Nat.le_of_lt hi) (Nat.le_succ _)
    rw [Nat.max_eq_right h_le, ← Nat.add_sub_assoc (Nat.le_of_lt hi),
      Nat.add_comm A.size i, Nat.add_sub_cancel]

theorem size_le_setF_size (A : Array α) (i : Nat) (v default : α) :
    A.size ≤ (A.setF i v default).size := by
  rw [Array.size_setF]
  exact Nat.le_max_left (size A) (i + 1)

theorem lt_size_setF (A : Array α) (i : Nat) (v default : α) :
    i < size (A.setF i v default) := by
  rw [Array.size_setF]
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right _ _)

theorem setF_eq_of_gt (A : Array α) {i : Nat} (hi : i > A.size) (v default : α) :
    A.setF i v default = A ++ mkArray (i - A.size) default ++ #[v] := by
  simp [setF, Nat.lt_asymm hi, Array.setF_go_eq]; rfl

theorem setF_eq_of_ge (A : Array α) {i : Nat} (hi : i ≥ A.size) (v default : α) :
    A.setF i v default = (A ++ mkArray (i - A.size) default).push v := by
  simp [setF, Nat.not_lt.mpr hi, Array.setF_go_eq]

theorem setF_setF (A : Array α) (i : Nat) (v v' default : α) :
    (A.setF i v default).setF i v' default = A.setF i v' default := by
  by_cases hi : i < A.size
  · rw [Array.setF_eq_set hi, Array.setF_eq_set hi]
    rw [← Array.size_set A ⟨i, hi⟩ v] at hi
    rw [Array.setF_eq_set hi]
    apply Array.set_set
  · have : i < size (A.setF i v default) := by
      rw [Array.size_setF]
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right _ _)
    simp [Array.setF, hi, this]
    have : i < size (setF.go v default (i - size A) A) := by
      rw [Array.size_setF_go A (i - A.size) v default, ← Nat.add_sub_assoc (Nat.not_lt.mp hi),
        Nat.add_comm A.size i, Nat.add_sub_cancel]
      exact Nat.lt_succ_self _
    simp [this]
    sorry
    done
  done

theorem mem_setF (A : Array α) (i : Nat) (v default : α) :
    ∀ a ∈ (A.setF i v default).data, a ∈ A.data ∨ a = default ∨ a = v := by
  intro a ha
  by_cases h : i < A.size
  . simp [Array.setF_eq_set h] at ha
    rcases List.mem_set ha with (ha | rfl)
    · exact Or.inl ha
    · right; right; rfl
  . rw [Nat.not_lt] at h
    simp only [A.setF_eq_of_ge h,  push_data, append_data, mkArray_data,
      List.append_assoc, List.mem_append, List.mem_singleton] at ha
    rcases ha with (ha | ha | rfl)
    · exact Or.inl ha
    · right; left; exact List.eq_of_mem_replicate ha
    · right; right; rfl

/-
#check Array.get_set
∀ {α : Type u_1} (a : Array α) (i : Fin (Array.size a)) (j : ℕ) (hj : j < Array.size a) (v : α),
  (Array.set a i v)[j] = if ↑i = j then v else a[j]
-/

-- TODO: Expand this into the upper definition later
theorem get_setF (A : Array α) (i : Nat) (v default : α) :
    (A.setF i v default).get ⟨i, lt_size_setF A i v default⟩ = v := by sorry

theorem get_setF' (A : Array α) (i : Nat) (v default : α) :
  ∀ {j : Fin A.size}, j.val ≠ i →
    (A.setF i v default).get ⟨j.val, Nat.lt_of_lt_of_le j.isLt (size_le_setF_size _ _ _ _)⟩ = A.get j := by
  sorry
  done

@[simp] theorem getElem_setF (A : Array α) (i : Nat) (v default : α) :
    (A.setF i v default)[i]'(lt_size_setF A i v default) = v := by
  sorry
  done
  /-
  by_cases hi : i < A.size
  · have := Array.setF_eq_set hi v default
    have h := Array.get_set A ⟨i, hi⟩ i hi v
    simp at h
    sorry
    --rw [← Array.get_eq_getElem] at h
    --have : (set A ⟨i, hi⟩ v)[i] = (setF A i v default)[i] := by
    --  sorry
    --  done
    --rw [← Array.get_eq_getElem] at this
    done
  sorry
  done -/

-- TODO: Match form of Array.get?_set
@[simp] theorem getElem?_setF (A : Array α) (i : Nat) (v default : α) :
    (A.setF i v default)[i]? = some v := by
  sorry

theorem getElem?_setF' {i j : Nat} :
    i ≠ j → ∀ (A : Array α) (v default), (A.setF i v default)[j]? = A[j]? := by
  sorry
  done

end setF /- section -/

end Array

#exit

-- CC: Finally biting the bullet and proving things about Subarrays.
-- CC: Have fun moving this into LeanColls, James!
namespace Subarray

theorem size_toArray_eq_size (A : Subarray α) :
    A.toArray.size = A.stop - A.start := by
  simp [toArray, Array.ofSubarray]
  done

theorem size_eq (A : Array α) (s e : Nat) :

(Array.size (Subarray.toArray (Array.toSubarray C s e)))

/-
structure Subarray (α : Type u)  where
  as : Array α
  start : Nat
  stop : Nat
  h₁ : start ≤ stop
  h₂ : stop ≤ as.size

Array.foldl : {α : Type u} → {β : Type v} →
  (β → α → β) → β → (as : Array α) → optParam Nat 0 → optParam Nat (Array.size as) → β
-/

/-
#check Subarray.foldl

theorem foldl_eq_array_foldl (f : β → α → β) (init : β) (A : Subarray α)
(A : Array α) {s e : Nat} (h₁ : s ≤ e) (h₂ : e ≤ A.size) (s : Subarray A) (f : β → α → β) (init : β) :
    s.foldl f init = (s.toSlice.foldl f init) := by
  simp [Subarray.foldl, Subarray.toSlice, Array.foldl_eq_foldl] -/

end Subarray
