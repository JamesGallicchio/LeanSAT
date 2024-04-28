/- Clearable arrays.

CArrays (clearable arrays) carry around an additional data field called size.
Size is like an Array.size, except it stores the number of "active" elements
in the array. To them make the array act like a normal Array, setting the
CArray.lsize := 0 "clears" the data without having to set each index to a zero value.

Author: Cayden Codel
Carnegie Mellon University

-/

import LeanSAT.Upstream.ToStd
import Experiments.ProofChecking.Array

import Mathlib.Data.Array.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Order.MinMax

structure CArray (α : Type _) where
  data : Array α
  lsize : Fin (data.size + 1) -- Logical size

namespace CArray

open Nat Array

variable {α : Type u} (A : CArray α) (v : α)

def mkCArray (n : Nat) (v : α) : CArray α := {
  data := Array.mkArray n v
  lsize := ⟨n, by rw [Array.size_mkArray n v]; exact lt.base n⟩
}

def empty : CArray α := {
  data := .empty
  lsize := ⟨0, succ_pos _⟩
}

def singleton (v : α) : CArray α := {
  data := Array.singleton v
  lsize := ⟨1, by simp⟩
}

/-- The size of a CArray is its logical size. -/
def size : Nat := A.lsize.val

def clear : CArray α := { A with
  lsize := ⟨0, succ_pos _⟩
}

def clearAfter (i : Nat) : CArray α := { A with
  lsize := ⟨min A.size i, min_lt_of_left_lt A.lsize.isLt⟩
}

-- Cayden TODO: there's probably some conversion here, such as an ext theorem
--    in terms of A.data.take A.lsize = A, but with '=' as behavior and not the underlying data
/- theorem ext (a b : Array α)
    (h₁ : a.size = b.size)
    (h₂ : (i : Nat) → (hi₁ : i < a.size) → (hi₂ : i < b.size) → a[i] = b[i])
    : a = b := -/

/-! # push and set -/

def push : CArray α :=
  if hs : A.size < A.data.size then
    { A with
      data := A.data.set ⟨A.size, hs⟩ v
      lsize := ⟨A.size + 1, by rw [size_set]; exact Nat.succ_lt_succ hs⟩ }
  else
    { A with
      data := A.data.push v
      lsize := ⟨A.size + 1, by rw [size_push]; exact Nat.succ_le_succ A.lsize.isLt⟩ }

def set (i : Fin A.size) (v : α) : CArray α :=
  { A with
    data := A.data.set ⟨i.val, lt_of_lt_of_le i.isLt (le_of_lt_succ A.lsize.isLt)⟩ v
    lsize := by rw [size_set]; exact A.lsize }

def set! (i : Nat) (v : α) : CArray α :=
  { A with
    data := A.data.set! i v
    lsize := by rw [size_set!]; exact A.lsize }

-- `filler` fills the gaps if `i` is too large
def setF (i : Nat) (v filler : α) : CArray α :=
  -- TODO: Do a match on the comparison?
  if hi : i < A.data.size then
    { A with
      data := A.data.set ⟨i, hi⟩ v
      lsize := by rw [size_set]; exact A.lsize }
  else if i = A.data.size then
    push A v
  else
    { A with
      data := (A.data ++ (Array.mkArray (i - A.data.size) filler)).push v,
      lsize := ⟨i, by
        rw [not_lt] at hi
        rw [size_push, size_append, size_mkArray,
          ← Nat.add_sub_assoc hi, add_comm _ i, Nat.add_sub_cancel]
        exact Nat.le_succ _ ⟩ }

@[simp] theorem size_empty : (empty : CArray α).size = 0 := rfl
@[simp] theorem size_mkCArray (n : Nat) (v : α) : (mkCArray n v).size = n := by sorry
@[simp] theorem size_singleton (v : α) : (singleton v).size = 1 := by sorry
@[simp] theorem size_clear : A.clear.size = 0 := rfl
@[simp] theorem size_set (i : Fin A.size) (v : α) : (set A i v).size = A.size := by sorry
@[simp] theorem size_set! (i : Nat) (v : α) : (set! A i v).size = A.size := by sorry
@[simp] theorem size_push (v : α) : (push A v).size = A.size + 1 := sorry
@[simp] theorem size_setF (i : Nat) (v default : α) :
    (A.setF i v default).size = max A.size (i + 1) := by sorry

/-! # get -/

def get  (i : Fin A.size) : α := A.data.get ⟨i.val, lt_of_lt_of_le i.isLt (le_of_lt_succ A.lsize.isLt)⟩
def get? (i : Nat) : Option α := A.data.get? i
def get! [Inhabited α] (A : CArray α) (i : Nat) : α := A.data.get! i

@[simp] theorem get_set_eq (i : Fin A.size) (v : α) :
    (A.set i v).get ⟨i.val, by rw [size_set]; exact i.isLt⟩ = v := by
  --simp only [get, set, eq_mpr_eq_cast, get_eq_getElem, get_set_eq]
  simp [get, set]

@[simp] theorem get_set_ne (i j : Fin A.size) (v : α) :
    i ≠ j → (A.set i v).get ⟨j.val, by rw [size_set]; exact j.isLt⟩ = A.get j := by sorry

/-
theorem get_push_lt (a : Array α) (x : α) (i : Nat) (h : i < a.size) :
    haveI : i < (a.push x).size := by simp [*, Nat.lt_succ_of_le, Nat.le_of_lt]
    (a.push x)[i] = a[i] := by
  simp only [push, getElem_eq_data_get, List.concat_eq_append, List.get_append_left, h]

@[simp] theorem get_push_eq (a : Array α) (x : α) : (a.push x)[a.size] = x := by
  simp only [push, getElem_eq_data_get, List.concat_eq_append]
  rw [List.get_append_right] <;> simp [getElem_eq_data_get, Nat.zero_lt_one]

theorem get_push (a : Array α) (x : α) (i : Nat) (h : i < (a.push x).size) :
    (a.push x)[i] = if h : i < a.size then a[i] else x := by
-/

theorem get_push_lt (v : α) (i : Fin A.size) :
  (A.push v).get ⟨i, by rw [size_push]; sorry⟩ = A.get i := by sorry

@[simp] theorem get_push_eq (v : α) : (A.push v).get ⟨A.size, by sorry⟩ = v := by sorry

theorem get_push (v : α) (i : Fin (A.push v).size) :
    (A.push v).get i = if h : i < A.size then A.get ⟨i, h⟩ else v := by
  by_cases h' : i < A.size
  · simp [h']
    rw [get_push_lt A v ⟨i.val, h'⟩]
  · have ⟨i, hi⟩ := i
    simp only [size_push] at hi
    simp [h', Nat.le_antisymm (Nat.le_of_lt_succ hi) (Nat.ge_of_not_lt h')]

/-
@[simp] theorem get_set_eq (a : Array α) (i : Fin a.size) (v : α) :
    (a.set i v)[i.1]'(by simp [i.2]) = v := by
  simp only [set, getElem_eq_data_get, List.get_set_eq]

@[simp] theorem get_set_ne (a : Array α) (i : Fin a.size) {j : Nat} (v : α) (hj : j < a.size)
    (h : i.1 ≠ j) : (a.set i v)[j]'(by simp [*]) = a[j] := by
  simp only [set, getElem_eq_data_get, List.get_set_ne h]

@[simp] theorem get?_set_eq (a : Array α) (i : Fin a.size) (v : α) :
    (a.set i v)[i.1]? = v := by simp [getElem?_pos, i.2]

@[simp] theorem get?_set_ne (a : Array α) (i : Fin a.size) {j : Nat} (v : α)
    (h : i.1 ≠ j) : (a.set i v)[j]? = a[j]? := by
  by_cases j < a.size <;> simp [getElem?_pos, getElem?_neg, *]

theorem get?_set (a : Array α) (i : Fin a.size) (j : Nat) (v : α) :
    (a.set i v)[j]? = if i.1 = j then some v else a[j]? := by
  if h : i.1 = j then subst j; simp [*] else simp [*]

theorem get_set (a : Array α) (i : Fin a.size) (j : Nat) (hj : j < a.size) (v : α) :
    (a.set i v)[j]'(by simp [*]) = if i = j then v else a[j] := by
  if h : i.1 = j then subst j; simp [*] else simp [*]

theorem set_set (a : Array α) (i : Fin a.size) (v v' : α) :
    (a.set i v).set ⟨i, by simp [i.2]⟩ v' = a.set i v' := by simp [set, List.set_set]
-/

/-! # Misc -/

-- CC TODO: Make these be `abbrev` instead of `def`?
def back [Inhabited α] : α := A.data.back
def setBack := { A with
  data := A.data.setBack v
  lsize := ⟨A.lsize.val, by simp⟩
}

@[simp]
theorem size_setBack : (A.setBack v).size = A.size := by
  simp [size, setBack]

def append (A B : CArray α) : CArray α := {
  data := A.data ++ B.data
  lsize := ⟨A.lsize.val + B.lsize.val, by
    rw [size_append]
    exact lt_succ_of_le <| Nat.add_le_add (le_of_lt_succ A.lsize.isLt) (le_of_lt_succ B.lsize.isLt)⟩ }

@[inline, specialize]
def map {α : Type u} {β : Type v} (f : α → β) (A : CArray α) : CArray β := { A with
  data := A.data.map f
  lsize := ⟨A.lsize.val, by rw [size_map]; exact A.lsize.isLt⟩
}

@[inline, specialize]
def foldlM {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m]
    (f : β → α → m β) (init : β) (A : CArray α) (start := 0) (stop := A.size) : m β :=
  A.data.foldlM f init start stop

@[inline, specialize]
def foldrM {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m]
    (f :  α → β → m β) (init : β) (A : CArray α) (start := 0) (stop := A.size) : m β :=
  A.data.foldrM f init start stop

@[inline]
def foldl {α : Type u} {β : Type v} (f : β → α → β) (init : β)
    (A : CArray α) (start := 0) (stop := A.size) : β :=
  A.data.foldl f init start stop

@[inline]
def foldr {α : Type u} {β : Type v} (f : α → β → β) (init : β)
    (A : CArray α) (start := A.size) (stop := 0) : β :=
  A.data.foldr f init start stop

/-! # lemmas and theorems -/

@[simp] theorem size_map {α : Type u} {β : Type v} (f : α → β) (A : CArray α) :
  (A.map f).size = A.size := by sorry

/-
theorem foldl_eq_foldl_data (f : β → α → β) (init : β) (arr : Array α) :
    arr.foldl f init = arr.data.foldl f init :=
  List.foldl_eq_foldlM .. ▸ foldlM_eq_foldlM_data ..
-/

#check Array.foldl_eq_foldl_data

--theorem foldl_eq_foldl_data (f : β → α → β) (init : β) (arr : CArray α) :
--  arr.foldl f init = (arr.array.data.take (arr.size)).foldl f init := by sorry

instance [ToString α] : ToString (CArray α) where
  toString a := s!"({a.data}, {a.size})"

end CArray
