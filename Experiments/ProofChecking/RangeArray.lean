/-

Arrays that implicitly partition a pool of data into contiguous ranges.
Handles deletions.

Authors: Cayden Codel, James Gallicchio
Carnegie Mellon University

-/

import Experiments.ProofChecking.Array
import Experiments.ProofChecking.ToLeanColls

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Array.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic

import LeanSAT.Upstream.ToStd
import LeanSAT.Upstream.ToMathlib

import LeanSAT.Data.Cnf
import LeanSAT.Data.ICnf
import LeanSAT.Model.PropFun

import LeanColls
open LeanColls

open Array Nat Fin

theorem Int.neg_cast_le (n : Nat) : -(n : Int) ≤ 0 := by simp
theorem Int.exists_nat_of_ge_zero {i : Int} : 0 ≤ i → ∃ (n : Nat), (n : Int) = i := by
  intro h
  exact CanLift.prf i h

universe u v w

namespace RangeArray

-- CC: TODO better names
@[inline, always_inline]
private def markIndexAsDeleted (i : Int) : Int :=
  if i ≥ 0 then -i - 1 else i

@[inline, always_inline]
private def getIndexFromMarkedIndex (i : Int) : Nat :=
  if i ≥ 0 then i.natAbs else i.natAbs - 1

@[simp]
theorem getIndex_markIndex (i : Int) :
    getIndexFromMarkedIndex (markIndexAsDeleted i) = getIndexFromMarkedIndex i := by
  simp [markIndexAsDeleted, getIndexFromMarkedIndex]
  by_cases hi : 0 ≤ i
  · rcases Int.exists_nat_of_ge_zero hi with ⟨n, rfl⟩
    simp [hi]
    split
    · linarith
    · rw [← neg_add', Int.natAbs_neg, ← Nat.cast_one, ← Nat.cast_add,
        Int.natAbs_cast, Nat.add_sub_cancel]
  · simp [hi]

theorem markIndexAsDeleted_coe (n : Nat) : markIndexAsDeleted n = -n - 1 := by
  simp [markIndexAsDeleted]

@[simp]
theorem getIndexFromMarkedIndex_coe (n : Nat) : getIndexFromMarkedIndex n = n := by
  simp [getIndexFromMarkedIndex]

@[simp]
theorem markIndex_getIndex_coe (n : Nat) : getIndexFromMarkedIndex (markIndexAsDeleted n) = n := by
  simp [markIndexAsDeleted, getIndexFromMarkedIndex]
  split
  · rename _ => h
    -- CC: Potentially make this a lemma?
    exact absurd h (Int.not_lt.mpr (Int.neg_cast_le n))
  · rw [← neg_add', Int.natAbs_neg, ← Nat.cast_one, ← Nat.cast_add, Int.natAbs_cast]
    exact add_tsub_cancel_right _ _

theorem markIndex_getIndex_of_ge_zero {i : Int} :
    0 ≤ i → getIndexFromMarkedIndex (markIndexAsDeleted i) = i := by
  intro hi
  rcases Int.exists_nat_of_ge_zero hi with ⟨n, rfl⟩
  rw [markIndex_getIndex_coe]

end RangeArray

/-
  A structure with a single pool of data in an array, and a system for marking
  contiguous regions of that pool into (adjacent, non-overlapping) pieces.
  Also handles deletions.

  To be implemented: garbage collection that compresses the data array once
  enough regions have been deleted.
-/
structure RangeArray (α : Type u) where
  /-- The pool of data. Data is added in groups, or sub-arrays, at a time.
      These sub-arrays, called "containers", are demarcated by `indexes`
      as 0-indexed Nat pointers into `data`. -/
  data : Array α

  /-- We take the convention that `indexes.size` is the number of "committed"
      elements in the data array. The sign of the Int indicates whether the
      container under that index in `data` has been deleted.

      The size of a container is the difference between the absolute values of
      the index and its next highest neighbor (or `dataSize` if at the end).
      Indexes are (not necessarily strictly) monotonically increasing.

      Deleting a container does not delete the underlying region in `data`.
      Instead, we leave that for garbage collection.

      Rather, a deleted region has its index mapped via v ↦ (-v - 1), so
      that the sizes of adjacent containers can still be computed.
      Of course, a simple negation and absolute value mapping is most desirable,
      but Lean sets -0 = 0, and so we cannot differentiate between a deleted
      0-sized starting container and a non-deleted one.  -/
  indexes : Array Int

  /-- The (logical) size of the `data` array. Uncommitted elements will increase
        `data.size`, but will leave `dataSize` unchanged. -/
  dataSize : Nat

  -- CC: An alternate formulation of `indexes`, using LeanColls
  -- size : Nat
  --indexes : ArrayN Int size     -- Using LeanColls `ArrayN`

  /-- Counts the total size of the containers that have been deleted. -/
  deletedSize : Nat

  /-- Invariants -/

  h_size : dataSize ≤ Size.size data
  h_dataSize_empty : Size.size indexes = 0 → dataSize = 0

  -- No index exceeds `dataSize`
  h_indexes : ∀ {i : Nat} (hi : i < Size.size indexes),
    RangeArray.getIndexFromMarkedIndex (Seq.get indexes ⟨i, hi⟩) ≤ dataSize

  -- The indexes are monotonically increasing in (unmarked) value
  h_indexes_inc : ∀ {i j : Nat} (hij : i ≤ j) (hj : j < Size.size indexes),
    RangeArray.getIndexFromMarkedIndex (Seq.get indexes ⟨i, lt_of_le_of_lt hij hj⟩) ≤
    RangeArray.getIndexFromMarkedIndex (Seq.get indexes ⟨j, hj⟩)

/-
CNF: <20 clauses>
LRAT:

21 1 4 -2 0 ...
25 2 -10 0 ...

data = [1, 5, 6, -2 | ]
indexes = [0, -4, -4, -4, -4, ]
indexes = [0, ]

fold at an index (run a function across a single specified clause)
folding across all indexes (hack this with Fin.foldRange [above])
add a sub-array (adding a clause)
delete (has something been deleted?)
(Garbage collect)

spec fns:
- array α @ i (where i is not deleted)
- array (array α) [all deleted clauses filtered out]

proofs:
- fold(M) at index i = fold(M) over (array @ i) or whatever
- fold(M) = fold(M) over array
- toArrays (delete RA) = RA' ↔ ∃ L M R, RA.toArrays = L ++ [M] ++ R ∧ RA'.toArrays = L ++ R
- garbageCollect RA = RA' → RA.toArrays = RA'.toArrays

-/

namespace RangeArray

variable {α : Type u} (A : RangeArray α) (v : α)

/-- The number of indexes, or containers, in the `data` array. -/
abbrev size : Nat := Size.size A.indexes

/-- The total size of the committed containers in the `data` array. -/
abbrev dsize : Nat := A.dataSize

/-- The number of elements added via `push` but not yet committed. -/
abbrev usize : Nat := (Size.size A.data) - A.dsize

-- Initialize a RangeArray with some data.
-- We don't use this operation for proof checking, so no theorems are proved about it.
/- def mkRangeArray (n : Nat) (v : α) : RangeArray α := {
  data := Array.mkArray n v
  indexes := Insert.empty
  dataSize := n
  deletedSize := 0
  h_size := by simp [Size.size]
  h_dataSize_empty := by simp [Size.size]
  h_indexes := by intro i hi; contradiction
  h_indexes_inc := by intro i j hi hj; contradiction
} -/

def empty (size : Nat := 100) : RangeArray α := {
  data := Array.mkEmpty size
  indexes := Array.mkEmpty size
  dataSize := 0
  deletedSize := 0
  h_size := by simp
  h_dataSize_empty := by simp
  h_indexes := by simp [LeanColls.size]
  h_indexes_inc := by simp [LeanColls.size]
}

/-- Adds a single element to the underlying data array, without adding a new index. -/
--@[inline, always_inline, specialize]
def push : RangeArray α := { A with
  data := Seq.snoc A.data v
  h_size := by simp [Seq.size_snoc]; exact le_succ_of_le A.h_size
}

/-- Clears the elements added via `push`, but maintains the rest of the containers.
    Should never actually be called, but is used for correctness. -/
def clear : RangeArray α :=
  if A.usize = 0 then A
  else { A with
    data := { data := A.data.data.take A.dsize }
    h_size := by simp [LeanColls.size]; exact A.h_size
  }

/-- Creates a new container that contains any elements added via `push`. -/
def commit : RangeArray α := { A with
  indexes := Seq.snoc A.indexes (A.dsize : Int)
  dataSize := Size.size A.data
  h_size := le.refl
  h_dataSize_empty := by simp
  h_indexes := by
    simp
    intro i hi
    rcases eq_or_lt_of_le (le_of_lt_succ hi) with (rfl | hi)
    · simp [le_add_right A.h_size]
      exact A.h_size
    · simp [Seq.get_snoc, hi]
      exact le_trans (A.h_indexes hi) A.h_size
  h_indexes_inc := by
    simp [Seq.size_snoc, Seq.get_snoc]
    intro i j hij hj
    rcases eq_or_lt_of_le (succ_le_of_lt hj) with (hj | hj)
    · simp at hj
      simp [hj]
      split <;> simp [A.h_indexes]
    · replace hj := succ_lt_succ_iff.mp hj
      simp [hj, lt_of_le_of_lt hij hj]
      exact A.h_indexes_inc hij _
}

/-- Gets the index of the ith container. -/
@[inline, always_inline]
def indexFin (i : Fin A.size) : Nat :=
  getIndexFromMarkedIndex (Seq.get A.indexes i)

/- Indexes outside `A.size` are 0. -/
@[inline, always_inline]
def index (i : Nat) : Nat :=
  if hi : i < A.size then
    indexFin A ⟨i, hi⟩
  else 0

theorem indexFin_eq_index {A : RangeArray α} {i : Nat} (hi : i < A.size) : A.indexFin ⟨i, hi⟩ = A.index i := by
  simp [index, hi]

theorem indexFin_eq_index?' {A : RangeArray α} (i : Fin A.size) : A.indexFin i = A.index i.val := by
  simp [index]

theorem index_le_dataSize (i : Nat) : A.index i ≤ A.dsize := by
  by_cases hi : i < A.size
  <;> simp [index, hi]
  exact A.h_indexes hi

theorem index_le_index_of_le {i j : Nat} (hij : i ≤ j) (hj : j < A.size) :
    A.index i ≤ A.index j := by
  simp [index, hj, lt_of_le_of_lt hij hj]
  exact A.h_indexes_inc hij hj

/-- Checks whether the ith container is deleted. -/
@[inline, always_inline]
def isDeletedFin (i : Fin A.size) : Bool :=
  (Seq.get A.indexes i) < 0

/- Checks whether the ith container is deleted.
    Containers outside of `A.size` are considered deleted. -/
def isDeleted (i : Nat) : Bool :=
  if hi : i < A.size then isDeletedFin A ⟨i, hi⟩
  else true

theorem isDeletedFin_eq_isDeleted {A : RangeArray α} {i : Nat} (hi : i < A.size) :
    A.isDeletedFin ⟨i, hi⟩ = A.isDeleted i := by
  simp [isDeleted, hi]

theorem isDeletedFin_eq_isDeleted' {A : RangeArray α} (i : Fin A.size) : A.isDeletedFin i = A.isDeleted i.val := by
  simp [isDeleted]

/-- Gets the size of the container under the provided index.
    The size of the most-recently-added container is the old `A.usize`.

    Note that the `rsize` of a deleted container can be computed, but is
    undefined, since garbage collection might discard deleted containers.

    CC: Should we say that `rsize` of a deleted container is 0? -/
@[inline, always_inline]
def rsizeFin (i : Fin A.size) : Nat :=
  if hi : i.val + 1 < A.size then
    A.indexFin ⟨i.val + 1, hi⟩ - A.indexFin i
  else --if i + 1 = A.size then
    A.dsize - A.indexFin i

def rsize (i : Nat) : Nat :=
  if hi : i < A.size then A.rsizeFin ⟨i, hi⟩
  else 0

theorem rsizeFin_eq_rsize {A : RangeArray α} {i : Nat} (hi : i < A.size) : A.rsizeFin ⟨i, hi⟩ = A.rsize i := by
  simp [rsize, hi]

theorem rsizeFin_eq_rsize' {A : RangeArray α} (i : Fin A.size) : A.rsizeFin i = A.rsize i.val := by
  simp [rsize]

def deleteFin (i : Fin A.size) : RangeArray α := { A with
  indexes := Seq.set A.indexes i (markIndexAsDeleted (Seq.get A.indexes i))
  deletedSize := A.deletedSize + A.rsize i
  h_dataSize_empty := by simp; exact A.h_dataSize_empty
  h_indexes := by
    simp [Seq.get_set]
    rcases i with ⟨i, hi⟩
    intro j hj
    by_cases hij : i = j
    <;> simp [hij, A.h_indexes]
  h_indexes_inc := by
    simp [Seq.get_set]
    rcases i with ⟨i, hi⟩
    intro j k hjk hk
    by_cases hjk_eq : j = k
    <;> simp [hjk_eq]
    by_cases hij : i = j
    · simp [hij, hjk_eq, A.h_indexes_inc hjk]
    · simp [hij]
      by_cases hik : i = k
      <;> simp [hik, A.h_indexes_inc hjk]
}

def delete (i : Nat) : RangeArray α :=
  if hi : i < A.size then A.deleteFin ⟨i, hi⟩ else A

theorem deleteFin_eq_delete {i : Nat} (hi : i < A.size) : A.deleteFin ⟨i, hi⟩ = A.delete i := by
  simp [delete, hi]

theorem deleteFin_eq_delete' (i : Fin A.size) : A.deleteFin i = A.delete i.val := by
  simp [delete]

-- CC: Can be implemented as `commit`, then `delete`.
/-- Creates a new container that contains any elements added via `addElement`,
    but that container is marked as deleted. -/
def commitDeleted : RangeArray α := { A with
  indexes := Seq.snoc A.indexes (markIndexAsDeleted A.dsize)
  dataSize := A.data.size
  h_size := le.refl
  h_dataSize_empty := by simp
  h_indexes := by
    simp
    intro i hi
    rcases eq_or_lt_of_le (le_of_lt_succ hi) with (rfl | hi)
    · simp; exact A.h_size
    · simp [Seq.get_snoc, hi]
      exact le_trans (A.h_indexes hi) A.h_size
  h_indexes_inc := by
    simp [Seq.size_snoc, Seq.get_snoc]
    intro i j hij hj
    rcases eq_or_lt_of_le (succ_le_of_lt hj) with (hj | hj)
    · simp at hj
      simp [hj]
      split <;> simp [A.h_indexes]
    · replace hj := succ_lt_succ_iff.mp hj
      simp [hj, lt_of_le_of_lt hij hj]
      exact A.h_indexes_inc hij _
}

/-- Commits deleted containers until the desired size. -/
def commitUntil (desiredSize : Nat) : RangeArray α :=
  let rec loop (n : Nat) (A' : RangeArray α) : RangeArray α :=
    match n with
    | 0 => A'
    | n + 1 => loop n A'.commitDeleted
  loop (desiredSize - A.size) A

/-- Adds a container. Any uncommitted elements are also part of the container. -/
@[inline, always_inline]
def append (arr : Array α) :=
  (arr.foldl (init := A.clear) (fun A' v => A'.push v)) |>.commit

-- An alternate version that directly implements it.
-- CC: Actually slightly different, since this will include any uncomitted elements, while the above does not.
def append' (arr : Array α) := { A with
  data := A.data ++ arr
  indexes := Seq.snoc A.indexes (A.dsize : Int)
  dataSize := (Size.size A.data) + (Size.size arr)
  h_size := by simp [size_append, A.h_size]
  h_dataSize_empty := by simp [size_append, A.h_dataSize_empty]
  h_indexes := by
    simp
    intro i hi
    rcases eq_or_lt_of_le (le_of_lt_succ hi) with (rfl | hi)
    · simp
      exact le_add_right A.h_size
    · simp [Seq.get_snoc, hi]
      exact le_trans (A.h_indexes hi) (le_add_right A.h_size)
  h_indexes_inc := by
    intro i j hij hj
    simp at hj
    simp [Seq.get_snoc, hj]
    rcases eq_or_lt_of_le (succ_le_of_lt hj) with (hj | hj)
    · simp at hj
      simp [hj]
      split <;> simp [A.h_indexes]
    · replace hj := succ_lt_succ_iff.mp hj
      simp [hj, lt_of_le_of_lt hij hj]
      exact A.h_indexes_inc hij _
}

section lemmas

variable (A : RangeArray α) (v : α) (i : Nat)

/-! # empty -/

@[simp]
theorem size_empty (n : Nat) : (empty n : RangeArray α).size = 0 := by
  simp [size, empty, LeanColls.size]

@[simp]
theorem dsize_empty (n : Nat) : (empty n : RangeArray α).dsize = 0 := by
  simp [empty, dsize]

@[simp]
theorem usize_empty (n : Nat) : (empty n : RangeArray α).usize = 0 := by
  simp [empty, LeanColls.size, usize]

/-! # push -/

@[simp]
theorem size_push : (A.push v).size = A.size := by simp [push, size]

@[simp]
theorem dsize_push : (A.push v).dsize = A.dsize := by simp [push, dsize]

@[simp]
theorem usize_push : (A.push v).usize = A.usize + 1 := by
  simp [push, usize, dsize, Nat.sub_add_comm A.h_size]

@[simp]
theorem index_push : (A.push v).index i = A.index i := by
  simp [push, index, indexFin]

@[simp]
theorem rsizeFin_push {A : RangeArray α} {i : Nat} (hi : i < A.size) (v : α) :
    (A.push v).rsizeFin ⟨i, hi⟩ = A.rsizeFin ⟨i, hi⟩ := by
  simp [rsizeFin]; rfl

@[simp]
theorem rsize_push : (A.push v).rsize i = A.rsize i := by
  simp [rsize]

@[simp]
theorem isDeleted_push : (A.push v).isDeleted i = A.isDeleted i := by
  simp [push, isDeleted, isDeletedFin, size]

theorem delete_push_comm : (A.push v).delete i = (A.delete i).push v := by
  simp [delete, deleteFin]
  split
  · congr 2
  · rfl

theorem clear_of_usize_zero : A.usize = 0 → A.clear = A := by
  intro hu
  simp [clear, hu]

@[simp]
theorem clear_push : (A.push v).clear = A.clear := by
  simp [clear, push, Seq.snoc, Array.push, usize, dsize, LeanColls.size, Array.size_append]
  have h_le := A.h_size
  simp [dataSize, dsize, LeanColls.size] at h_le
  unfold Array.size at h_le ⊢
  split
  · rename _ => h_eq
    have : A.dataSize ≥ List.length A.data.data + 1 := Nat.le_of_sub_eq_zero h_eq
    have := lt_of_succ_le this
    exact absurd h_le (not_le.mpr this)
  · rename _ => h_ne; clear h_ne
    split
    · rename _ => h_eq
      congr
      rw [← le_antisymm (Nat.le_of_sub_eq_zero h_eq) A.h_size]
      conv => lhs; rw [← Nat.add_zero (List.length A.data.data)]
      simp [List.take_append]
    · have : List.take A.dataSize (A.data.data ++ [v]) = List.take A.dataSize A.data.data := by
        rw [List.take_append_of_le_length h_le]
      congr

/-! # clear -/

@[simp]
theorem size_clear : A.clear.size = A.size := by
  simp [clear, size]; split <;> rfl

@[simp]
theorem dsize_clear : A.clear.dsize = A.dsize := by
  simp [clear, dsize]; split <;> rfl

@[simp]
theorem data_size_clear : Size.size (A.clear).data = A.dsize := by
  simp [clear, dsize]
  split <;> rename _ => h
  · simp [usize, dsize] at h
    exact le_antisymm (Nat.le_of_sub_eq_zero h) A.h_size
  · simp [LeanColls.size]
    exact A.h_size

@[simp]
theorem indexes_clear : A.clear.indexes = A.indexes := by
  simp [clear, indexes]
  split <;> rename _ => h
  · rfl
  · simp [LeanColls.size]

@[simp]
theorem usize_clear : A.clear.usize = 0 := by
  simp [clear, usize]
  split
  · assumption
  · simp [LeanColls.size]

@[simp]
theorem rsize_clear : A.clear.rsize i = A.rsize i := by
  simp [clear, rsize]
  split <;> rename _ => h
  · split <;> rename _ => hi
    · congr 2
      simp [h]
      exact size_clear A
      aesop -- CC: ???
    · rfl
  · split <;> rename _ => hi
    · -- Annoyingly, we must unpack rsizeFin to get rid of the `if`
      -- We then put it back into rsizeFin for the data comparison
      simp [rsizeFin_eq_rsize, h]
      simp [rsize, hi, rsizeFin, size]
      congr
    · rfl

@[simp]
theorem clear_clear : A.clear.clear = A.clear := by
  simp [clear, size, dsize, usize, LeanColls.size]
  split <;> rename _ => h_usize
  <;> simp [h_usize]


/-! # delete -/

@[simp]
theorem size_delete : (A.delete i).size = A.size := by
  rw [delete]; split <;> rename _ => hi <;> try rfl
  simp [deleteFin, hi, size]

@[simp]
theorem size_deleteFin {A : RangeArray α} {i : Nat} (hi : i < A.size) :
    (A.deleteFin ⟨i, hi⟩).size = A.size := by
  simp [deleteFin, size]

@[simp]
theorem dsize_delete : (A.delete i).dsize = A.dsize := by
  rw [delete]; split <;> rfl

@[simp]
theorem dsize_deleteFin {A : RangeArray α} {i : Nat} (hi : i < A.size) :
    (A.deleteFin ⟨i, hi⟩).dsize = A.dsize := by
  simp [deleteFin, dsize]

@[simp]
theorem usize_delete : (A.delete i).usize = A.usize := by
  rw [delete]; split <;> rfl

@[simp]
theorem usize_deleteFin {A : RangeArray α} {i : Nat} (hi : i < A.size) :
    (A.deleteFin ⟨i, hi⟩).usize = A.usize := by
  simp [deleteFin, usize]

-- We cannot prove this theorem, because garbage collection will throw this off
--theorem index_delete_ne (A : RangeArray α) {i j : Nat} (hij : i ≠ j) :
--    (A.delete i).index j = A.index j := by

-- This theorem will hold, regardless of garbage collection
theorem rsize_delete_ne {A : RangeArray α} {i j : Nat} (hij : i ≠ j) :
    (A.delete i).rsize j = A.rsize j := by
  simp [delete]
  split <;> rename _ => hi <;> try rfl
  simp [deleteFin, rsize, size]
  split <;> rename _ => hj <;> try rfl
  simp [rsizeFin, hi, hj, size, indexFin, Seq.get_set, hij]
  split <;> rename _ => hj₂ <;> try rfl
  split <;> rename _ => hi₂ <;> try rfl
  simp [hi₂]

@[simp]
theorem isDeleted_delete_eq : (A.delete i).isDeleted i = true := by
  by_cases hi : i < Size.size A.indexes
  · simp [isDeleted, isDeletedFin, delete, deleteFin, hi,
      Seq.get, Seq.set, RangeArray.markIndexAsDeleted]
    split <;> omega
  · simp [isDeleted, hi]

theorem isDeleted_delete_ne (A : RangeArray α) {i j : Nat} (hij : i ≠ j) :
    (A.delete i).isDeleted j = A.isDeleted j := by
  simp [delete]
  split <;> rename _ => hi <;> try rfl
  simp [isDeleted]
  split <;> rename _ => hj <;> try rfl
  simp [isDeletedFin, deleteFin, hi, hj, size, indexFin, hij]

theorem isDeleted_delete (i j : Nat) : (A.delete i).isDeleted j =
    if i = j then true else A.isDeleted j := by
  split <;> rename _ => hij
  · subst hij; exact isDeleted_delete_eq A i
  · exact isDeleted_delete_ne A hij

theorem isDeleted_true_of_ge {A : RangeArray α} {i : Nat} (hi : i ≥ A.size) : A.isDeleted i = true := by
  simp [isDeleted, hi]

theorem lt_of_isDeleted_false {A : RangeArray α} {i : Nat} (hi : A.isDeleted i = false) : i < A.size := by
  simp [isDeleted] at hi
  split at hi
  · assumption
  · contradiction

/-! # commit -/

@[simp]
theorem size_commit : A.commit.size = A.size + 1 := by
  simp [commit, size]

@[simp]
theorem dsize_commit : A.commit.dsize = Size.size A.data := by
  simp [commit, dsize]

@[simp]
theorem usize_commit : A.commit.usize = 0 := by
  simp [usize, commit, dsize]

theorem index_commit_lt {A : RangeArray α} {i : Nat} (hi : i < A.size) :
    (A.commit).index i = A.index i := by
  rw [size] at hi
  simp [commit, size, hi, lt_succ_of_lt hi, index, indexFin, Seq.get_snoc]

@[simp]
theorem index_commit_eq : (A.commit).index A.size = A.dsize := by
  simp [commit, index, indexFin, Seq.get_snoc, size]

theorem index_commit_gt {A : RangeArray α} {i : Nat} (hi : i > A.size) :
    (A.commit).index i = 0 := by
  rw [size] at hi
  simp [commit, index, indexFin, size, hi]
  intro h
  exact absurd hi (not_lt_of_ge (le_of_lt_succ h))

@[simp]
theorem rsize_commit_lt {A : RangeArray α} {i : Nat} (hi : i < A.size) :
    (A.commit).rsize i = A.rsize i := by
  rw [size] at hi
  simp [commit, rsize, size, hi, lt_succ_of_lt hi, rsizeFin]
  split <;> rename _ => hi'
  · simp [indexFin, size, Seq.get_snoc, hi', lt_of_succ_lt hi']
  · have := le_antisymm (Nat.succ_le_of_lt hi) (not_lt.mp hi')
    rw [succ_eq_add_one] at this
    simp [indexFin, size, this, Seq.get_snoc, getIndexFromMarkedIndex_coe, hi]

@[simp]
theorem rsizeFin_commit {A : RangeArray α} {i : Nat} (hi : i < A.size) :
    (A.commit).rsizeFin ⟨i, by rw [size_commit]; exact Nat.lt_succ_of_lt hi⟩ = A.rsizeFin ⟨i, hi⟩ := by
  simp [rsizeFin_eq_rsize]; exact rsize_commit_lt hi

@[simp]
theorem rsize_commit_eq : (A.commit).rsize A.size = A.usize := by
  simp [commit, rsize, rsizeFin, dsize, size, index, indexFin, Seq.get_snoc]

@[simp]
theorem rsizeFin_commit_eq : (A.commit).rsizeFin ⟨A.size, by simp⟩ = A.usize := by
  simp [rsizeFin_eq_rsize]

@[simp]
theorem rsize_commit_gt {A : RangeArray α} {i : Nat} (hi : i > A.size) :
    (A.commit).rsize i = 0 := by
  rw [size] at hi
  simp [commit, rsize, rsizeFin, size, hi]
  intro h
  exact absurd hi (not_lt_of_ge (le_of_lt_succ h))

@[simp]
theorem clear_commit (A : RangeArray α) : A.commit.clear = A.commit := by
  simp [commit, clear]

theorem isDeleted_commit_lt {A : RangeArray α} {i : Nat} (hi : i < A.size) :
    (A.commit).isDeleted i = A.isDeleted i := by
  rw [size] at hi
  simp [commit, isDeleted, isDeletedFin, size, hi, lt_succ_of_lt hi, Seq.get_snoc]

@[simp]
theorem isDeleted_commit_eq : (A.commit).isDeleted A.size = false := by
  simp [commit, isDeleted, isDeletedFin, size, Seq.get_snoc]

/-! # append -/

@[simp]
theorem append_empty (A : RangeArray α) : A.append Array.empty = A.clear.commit := by
  simp [append, Array.empty, commit]

@[simp]
theorem append_empty' (A : RangeArray α) : A.append #[] = A.clear.commit := by
  simp [append, Array.empty, commit]

@[simp]
theorem append_nil (A : RangeArray α) : A.append { data := [] } = A.clear.commit :=
  append_empty A

variable (arr : Array α)

theorem append_eq_append'_aux :
  ((arr.foldl (init := A) (fun A' v => A'.push v)) |>.commit) = A.append' arr := by
  have ⟨L⟩ := arr
  rw [append']
  induction' L with x xs ih generalizing A
  · simp [commit, LeanColls.size]
  · rw [foldl_cons]
    rw [ih (push A x)]
    simp [push, Seq.snoc]
    constructor
    · have : A.data.push x = A.data ++ #[x] := rfl
      rw [this]
      rw [Array.append_assoc, Array.singleton_append_data_eq_cons]
    · simp [LeanColls.size, succ_eq_add_one]
      rw [add_assoc, add_comm 1 (List.length xs)]

theorem append_eq_append' : A.append arr = (A.clear).append' arr := by
  rw [append, append_eq_append'_aux A.clear arr]

@[simp]
theorem append_indexes : (A.append arr).indexes = Seq.snoc A.indexes (A.dsize : Int) := by
  rw [append_eq_append']
  simp [append']

@[simp]
theorem size_append : (A.append arr).size = A.size + 1 := by
  have ⟨L⟩ := arr
  cases L
  · simp
  · rw [append_eq_append']
    simp [append', size]

@[simp]
theorem dsize_append : (A.append arr).dsize = A.dsize + Size.size arr := by
  have ⟨L⟩ := arr
  cases L
  · simp [append, usize, dsize]; rfl
  · simp [append_eq_append', append', dsize]

theorem lt_size_append_of_lt_size {A : RangeArray α} {i : Nat} (hi : i < A.size)
    (arr : Array α) : i < (A.append arr).size := by
  simp; exact lt_succ_of_lt hi

theorem index_append_lt {A : RangeArray α} {i : Nat} (hi : i < A.size) (arr : Array α) :
    (A.append arr).index i = A.index i := by
  rw [append_eq_append']
  rw [size] at hi
  simp [append', hi, lt_succ_of_lt hi, size]
  simp [index, indexFin, size, hi, lt_succ_of_lt hi, Seq.get_snoc]

@[simp]
theorem index_append_eq : (A.append arr).index A.size = A.dsize := by
  rw [append_eq_append', append']
  simp [index, indexFin, size, Seq.get_snoc]

theorem rsize_append_lt {A : RangeArray α} {i : Nat} (hi : i < A.size) (arr : Array α) :
    (A.append arr).rsize i = A.rsize i := by
  rw [append_eq_append']
  rw [size] at hi
  simp [append', hi, lt_succ_of_lt hi, size]
  simp [rsize, rsizeFin, index, indexFin, size, hi, lt_succ_of_lt hi, Seq.get_snoc]
  split <;> rename _ => hi'
  · rfl
  · have := le_antisymm (Nat.succ_le_of_lt hi) (not_lt.mp hi')
    rw [succ_eq_add_one] at this
    simp [this]

@[simp]
theorem rsize_append_eq : (A.append arr).rsize A.size = Size.size arr := by
  rw [append_eq_append']
  simp [rsize, size, append', rsizeFin, dsize]
  rw [indexFin_eq_index]
  simp
  conv => lhs; lhs; rw [Nat.add_comm]
  simp [index, indexFin, size]

@[simp]
theorem usize_append (arr : Array α) : (A.append arr).usize = 0 := by
  simp [append_eq_append', append']

theorem isDeleted_append_lt {A : RangeArray α} {i : Nat} (hi : i < A.size) (arr : Array α) :
    (A.append arr).isDeleted i = A.isDeleted i := by
  rw [append_eq_append']
  rw [size] at hi
  simp [append', hi, lt_succ_of_lt hi, size]
  simp [isDeleted, isDeletedFin, hi, lt_succ_of_lt hi, Seq.get_snoc, size]

@[simp]
theorem isDeleted_append_eq : (A.append arr).isDeleted A.size = false := by
  rw [append_eq_append']
  simp [append', isDeleted, isDeletedFin, size, Seq.get_snoc]

end lemmas

/-! # get -/

@[inline, always_inline]
def getFin (i : Fin (Size.size A.data)) : α :=
  Seq.get A.data i

@[inline, always_inline]
def get [Inhabited α] (i : Nat) : α :=
  if hi : i < Size.size A.data then
    A.getFin ⟨i, hi⟩
  else default

variable [Inhabited α]

theorem getFin_eq_get {i : Nat} (hi : i < Size.size A.data) : A.getFin ⟨i, hi⟩ = A.get i := by
  simp [get, hi]

theorem getFin_eq_get' (i : Fin (Size.size A.data)) : A.getFin i = A.get i.val := by
  simp [get]

theorem get_push_lt {A : RangeArray α} {i : Nat} (hi : i < Size.size A.data) (v : α) :
    (A.push v).get i = A.get i := by
  simp [get, getFin, push, hi, Seq.get_snoc, lt_succ_of_lt hi]

@[simp]
theorem get_push_eq : (A.push v).get (Size.size A.data) = v := by
  simp [get, getFin, push, Seq.get_snoc]

theorem get_push_gt {A : RangeArray α} {i : Nat} (hi : i > Size.size A.data) (v : α) :
    (A.push v).get i = default := by
  replace hi := succ_le_of_lt hi
  rw [succ_eq_add_one] at hi
  have := (not_lt.mpr hi)
  simp [get, push, Seq.size_snoc, this]

theorem get_clear_lt {A : RangeArray α} {i : Nat} (hi : i < A.dsize) :
    (A.clear).get i = A.get i := by
  simp [clear, get, hi, usize]
  split <;> rename _ => h_usize
  · simp [getFin_eq_get, h_usize]
  · have h_dsize : dsize A < LeanColls.size A.data := by omega
    split <;> rename _ => hi'
    · simp [LeanColls.size] at hi'
      simp [getFin_eq_get, h_usize]
      simp [get, hi, LeanColls.size, hi', getFin]
      have := List.get_take A.data.data (lt_trans hi h_dsize) hi'.1
      simp [Seq.get, getElem_eq_data_get, this]
    · simp [LeanColls.size, hi] at hi'
      have := lt_trans hi h_dsize
      exact absurd this (not_lt_of_ge hi')

theorem get_clear_ge {A : RangeArray α} {i : Nat} (hi : i ≥ A.dsize) :
    (A.clear).get i = default := by
  simp [clear, get, hi, usize]
  split <;> rename _ => h_usize
  · simp [getFin_eq_get, h_usize]
    have : A.dsize ≥ LeanColls.size A.data := by omega
    intro h_con
    exact absurd (lt_of_lt_of_le h_con this) (not_lt_of_ge hi)
  · simp [LeanColls.size, hi]

theorem get_commit_lt {A : RangeArray α} {i : Nat} (hi : i < Size.size A.data) :
    (A.commit).get i = A.get i := by
  simp [get, getFin, commit, hi, usize]

theorem get_commit_lt_usize {A : RangeArray α} {i : Nat} (hi : i < A.usize) :
    (A.commit).get (A.dsize + i) = A.get (A.dsize + i) := by
  simp [get, getFin, commit, hi, usize]

/- theorem get_append_lt {A : RangeArray α} {i : Nat} (hi : i < A.dsize) (arr : Array α) :
    (A.append arr).get i = A.get i := by -/

/-
theorem get_append_ge {A : RangeArray α} {i : Nat} (hi : i ≥ A.dsize) (arr : Array α) :
    (A.append arr).get i = arr.get (i - A.dsize) := by -/

theorem indexFin_add_rsizeFin_le_size {A : RangeArray α}
      (i : Fin A.size) :
    A.indexFin i + A.rsizeFin i ≤ Size.size A.data := by
  rcases i with ⟨i, hi⟩
  simp [indexFin, rsizeFin]
  split <;> rename _ => hi'
  · rw [← Nat.add_sub_assoc, Nat.add_comm, Nat.add_sub_cancel]
    exact le_trans (A.h_indexes hi') A.h_size
    apply A.h_indexes_inc (by simp)
  · rw [← Nat.add_sub_assoc, Nat.add_comm, Nat.add_sub_cancel]
    exact A.h_size
    exact A.h_indexes hi

theorem indexFin_add_offset_lt_size {A : RangeArray α}
      (i : Fin A.size) (offset : Fin (A.rsizeFin i)) :
    A.indexFin i + offset.val < Size.size A.data := by
  have := indexFin_add_rsizeFin_le_size i
  apply lt_of_lt_of_le (by omega) this

theorem index_add_offset_lt_size {A : RangeArray α} {i offset : Nat}
      (hi : i < A.size) (ho : offset < A.rsize i) :
    A.index i + offset < Size.size A.data := by
  have := indexFin_add_offset_lt_size ⟨i, hi⟩ ⟨offset, by rw [rsizeFin_eq_rsize]; exact ho⟩
  rw [indexFin_eq_index] at this
  exact this

/-! # oget and uget -/

@[inline, always_inline]
def ogetFin {A : RangeArray α} (i : Fin A.size) (offset : Fin (A.rsizeFin i)) : α :=
  A.getFin ⟨A.indexFin i + offset.val,
      indexFin_add_offset_lt_size i offset⟩

@[inline, always_inline]
def oget (i offset : Nat) : α :=
  if hi : i < A.size then
    if ho : offset < A.rsizeFin ⟨i, hi⟩ then
      A.ogetFin ⟨i, hi⟩ ⟨offset, ho⟩
    else default
  else default

theorem ogetFin_eq_oget {i offset : Nat} (hi : i < A.size) (ho : offset < A.rsizeFin ⟨i, hi⟩) :
    A.ogetFin ⟨i, hi⟩ ⟨offset, ho⟩ = A.oget i offset := by
  simp [oget, hi, ho]

theorem ogetFin_eq_oget' (i : Fin A.size) (offset : Fin (A.rsizeFin i)) :
    A.ogetFin i offset = A.oget i.val offset.val := by
  simp [oget]

theorem ogetFin_eq_getFin {i offset : Nat} (hi : i < A.size) (ho : offset < A.rsizeFin ⟨i, hi⟩) :
    A.ogetFin ⟨i, hi⟩ ⟨offset, ho⟩ =
      A.getFin ⟨A.indexFin ⟨i, hi⟩ + offset, indexFin_add_offset_lt_size ⟨_, hi⟩ ⟨_, ho⟩⟩ := by
  simp [ogetFin]

@[inline, always_inline]
def ugetFin {A : RangeArray α} (i : Fin A.usize) : α :=
  A.getFin ⟨A.dsize + i.val, Nat.add_lt_of_lt_sub' i.isLt⟩

@[inline, always_inline]
def uget (i : Nat) : α :=
  if hi : i < A.usize then
    A.ugetFin ⟨i, hi⟩
  else default

theorem ugetFin_eq_uget {i : Nat} (hi : i < A.usize) : A.ugetFin ⟨i, hi⟩ = A.uget i := by
  simp [uget, hi]

theorem ugetFin_eq_uget' (i : Fin A.usize) : A.ugetFin i = A.uget i.val := by
  simp [uget]

@[simp]
theorem oget_push (A : RangeArray α) (i offset : Nat) (v : α) :
    (A.push v).oget i offset = A.oget i offset := by
  simp [oget, ogetFin]
  split <;> try rfl
  rename _ => hi
  split <;> try rfl
  rename _ => ho
  rw [rsizeFin_eq_rsize] at ho
  have h_add := indexFin_add_rsizeFin_le_size ⟨i, hi⟩
  simp_rw [getFin_eq_get, indexFin_eq_index, rsizeFin_eq_rsize] at h_add ⊢
  have : index A i + offset < index A i + rsize A i := by omega
  have := lt_of_lt_of_le this h_add
  simp [get_push_lt this v]

theorem oget_commit_lt {A : RangeArray α} {i offset : Nat} (hi : i < A.size) (ho : offset < A.rsize i) :
    (A.commit).oget i offset = A.oget i offset := by
  simp [oget, ogetFin, hi, lt_succ_of_lt hi]
  simp_rw [rsizeFin_eq_rsize, getFin_eq_get, indexFin_eq_index]
  simp [ho, index_commit_lt hi]
  apply get_commit_lt
  exact index_add_offset_lt_size hi ho

theorem oget_commit_eq {A : RangeArray α} {offset : Nat} (ho : offset < A.usize) :
    (A.commit).oget A.size offset = A.uget offset := by
  simp [oget, ogetFin, uget, ugetFin, ho]
  simp_rw [indexFin_eq_index, getFin_eq_get]
  simp
  apply get_commit_lt
  simp [usize] at ho
  omega

theorem oget_delete_ne (A : RangeArray α) {i j offset : Nat} (hij : i ≠ j) :
    (A.delete i).oget j offset = A.oget j offset := by
  simp [delete]
  split <;> rename _ => hi <;> try rfl
  simp [oget, ogetFin]
  split <;> rename _ => hj <;> try rfl
  simp_rw [rsizeFin_eq_rsize, deleteFin_eq_delete]
  simp [rsize_delete_ne hij]
  split <;> rename _ => ho <;> try rfl
  simp [getFin, deleteFin, indexFin, Seq.get_set, hij]

theorem uget_push_lt {A : RangeArray α} {i : Nat} (hi : i < A.usize) (v : α) :
    (A.push v).uget i = A.uget i := by
  simp [uget, ugetFin, hi, lt_succ_of_lt hi]
  simp_rw [getFin_eq_get]
  apply get_push_lt
  simp [usize] at hi
  omega

@[simp]
theorem uget_push_eq : (A.push v).uget A.usize = v := by
  simp [uget, ugetFin]
  rw [getFin_eq_get]
  simp [usize]
  rw [← Nat.add_sub_assoc A.h_size, Nat.add_comm, Nat.add_sub_cancel]
  exact get_push_eq _ _

@[simp]
theorem uget_delete (A : RangeArray α) (i j : Nat) :
    (A.delete j).uget i = A.uget i := by
  simp [delete]
  split <;> rfl

/-! # models -/

structure models (R : RangeArray α) (Ls : List (Option (List α))) (L : List α) : Prop where
  (h_size₁ : R.size = Size.size Ls)
  (h_size₂ : R.usize = Size.size L)
  (h_some : ∀ {i : Nat} (hi : i < Size.size Ls),
    (R.isDeleted i = false) ↔ (∃ (C : List α), Seq.get Ls ⟨i, hi⟩ = some C))
  (h_sizes : ∀ {i : Nat} (hi : i < Size.size Ls) {sL : List α},
    Seq.get Ls ⟨i, hi⟩ = some sL → R.rsize i = Size.size sL)
  (h_agree : ∀ {i : Nat} (hi : i < Size.size Ls) {sL : List α},
      Seq.get Ls ⟨i, hi⟩ = some sL →
        (∀ {j : Nat} (hj : j < (Size.size sL)),
          R.oget i j = Seq.get sL ⟨j, hj⟩))
  (h_uncommitted : ∀ {i : Nat} (hi : i < Size.size L),
      R.uget i = Seq.get L ⟨i, hi⟩)

variable {R : RangeArray α} {Ls : List (Option (List α))} {L : List α} (h_models : models R Ls L)

theorem get_eq_some_of_models_of_not_deleted {i : Nat} :
    R.isDeleted i = false → (hi : i < Size.size Ls) ×' ∃ sL, Seq.get Ls ⟨i, hi⟩ = some sL := by
  intro h_del
  by_cases hi : i < Size.size Ls
  · have := h_models.h_some hi
    simp [h_del] at this
    use hi
  · rw [← h_models.h_size₁] at hi
    rw [isDeleted_true_of_ge (not_lt.mp hi)] at h_del
    contradiction

@[simp]
theorem models_empty (size : Nat) : models (empty size) ([] : List (Option (List α))) [] := by
  constructor <;> simp

theorem models_push : ∀ (v : α), models (R.push v) Ls (Seq.snoc L v) := by
  intro v
  constructor
  · simp [h_models.h_size₁]
  · simp [h_models.h_size₂]
  · refine h_models.h_some
  · refine h_models.h_sizes
  · intro i hi sL hsL j hj
    simp [h_models.h_agree hi hsL hj]
  · intro i hi
    have hi₁ := hi
    rw [Seq.size_snoc, ← h_models.h_size₂] at hi₁
    rcases eq_or_lt_of_le (le_of_lt_succ hi₁) with (hi' | hi')
    · conv => lhs; simp [hi']
      rw [h_models.h_size₂] at hi'
      simp [Seq.get_snoc, hi']
    · conv => lhs; simp [uget_push_lt hi']
      rw [Seq.get_snoc]
      rw [h_models.h_size₂] at hi'
      split <;> rename _ => hi₂
      · exact h_models.h_uncommitted hi'
      · simp at hi₂ hi
        have := le_antisymm hi₂ (le_of_lt_succ hi)
        rw [this] at hi'
        exact absurd hi' (not_lt.mpr (le_refl _))

theorem models_commit : models (R.commit) (Seq.snoc Ls (some L)) [] := by
  constructor
  · simp [h_models.h_size₁]
  · simp [h_models.h_size₂]
  · intro i hi
    have hi₁ := hi
    simp at hi₁
    simp [Seq.get_snoc, -eq_iff_iff]
    split <;> rename _ => hi₂
    · rw [← h_models.h_size₁] at hi₂
      conv => lhs; simp [isDeleted_commit_lt hi₂]
      rw [h_models.h_size₁] at hi₂
      exact h_models.h_some hi₂
    · simp only [not_lt] at hi₂
      have := le_antisymm (le_of_lt_succ hi₁) hi₂
      rw [← h_models.h_size₁] at this
      simp [this]
  · intro i hi sL hsL
    simp at hi
    rcases eq_or_lt_of_le (le_of_lt_succ hi) with (rfl | hi₂)
    · conv => lhs; rw [← h_models.h_size₁]
      simp [h_models.h_size₂]
      simp [Seq.get_snoc] at hsL
      subst hsL
      rfl
    · rw [← h_models.h_size₁] at hi₂
      rw [rsize_commit_lt hi₂]
      rw [h_models.h_size₁] at hi₂
      simp [Seq.get_snoc, hi₂] at hsL
      exact h_models.h_sizes hi₂ hsL
  · intro i hi sL hsL j hj
    have hi₁ := hi
    simp at hi₁
    rcases eq_or_lt_of_le (le_of_lt_succ hi₁) with (hi₂ | hi₂)
    · simp [hi₂] at hsL
      subst hsL
      rw [← h_models.h_size₁] at hi₂
      rw [hi₂, oget_commit_eq ((h_models.h_size₂).symm ▸ hj)]
      exact h_models.h_uncommitted hj
    · simp [Seq.get_snoc, hi₂] at hsL
      rw [← h_models.h_sizes hi₂ hsL] at hj
      rw [← h_models.h_size₁] at hi₂
      rw [oget_commit_lt hi₂ hj]
      rw [h_models.h_size₁] at hi₂
      rw [h_models.h_sizes hi₂ hsL] at hj
      exact h_models.h_agree hi₂ hsL hj
  · simp

theorem models_delete : ∀ {i : Nat} (hi : i < Size.size Ls),
    models (R.delete i) (Seq.set Ls ⟨i, hi⟩ none) L := by
  intro i hi
  constructor
  · simp [h_models.h_size₁]
  · simp [h_models.h_size₂]
  · intro j hj
    by_cases hij : i = j
    · simp [hij]
    · rw [isDeleted_delete_ne R hij]
      simp [Seq.get_set, hij, -eq_iff_iff]
      simp at hj
      exact h_models.h_some hj
  · intro j hj sL hsL
    by_cases hij : i = j
    · simp [Seq.get_set, hij] at hsL
    · simp [Seq.get_set, hij] at hsL
      simp at hj
      rw [rsize_delete_ne hij]
      exact h_models.h_sizes hj hsL
  · intro j hj sL hsL k hk
    by_cases hij : i = j
    <;> simp [Seq.get_set, hij] at hsL
    simp at hj
    have := h_models.h_some hj
    simp [hsL] at this
    rw [oget_delete_ne R hij]
    exact h_models.h_agree hj hsL hk
  · intro j hj
    simp [uget_delete]
    exact h_models.h_uncommitted hj

/-! # drop and take -/

/-def drop (A : RangeArray α) : RangeArray α :=

theorem models_cons {R : RangeArray α} {x : α} {xs : List α} {Ls : Option (List α)} {L : List α}
  (h_models : R)

#exit -/

-- CC: Which direction does this theorem need to be in?
/- theorem exists_model (A : RangeArray α) :
    ∃ (Ls : List (Option (List α))) (L : List α), models A Ls L := by -/

/- theorem exists_model' (Ls : List (Option (List α))) (L : List α) :
    ∃ (A : RangeArray α), models A Ls L := by -/

/-! # fold -/

@[inline, always_inline, specialize]
def foldlM_index {β : Type v} {m : Type v → Type w} [Monad m] (f : β → α → m β)
    (init : β) (A : RangeArray α) (i : Nat) : m β :=
  if isDeleted A i = false then
    A.data.foldlM f init (A.index i) (A.index i + A.rsize i)
  else return init

@[inline, always_inline, specialize]
def foldl_index {β : Type v} (f : β → α → β)
    (init : β) (A : RangeArray α) (i : Nat) : β :=
  if isDeleted A i = false then
    A.data.foldl f init (A.index i) (A.index i + A.rsize i)
  else init

@[inline, always_inline, specialize]
def foldlM_indexHyps {β : Type v} {m : Type v → Type w} [Monad m] (f : β → α → m β)
    (init : β) (A : RangeArray α) (i : Fin A.size) : m β :=
  if isDeleted A i = false then
    A.data.foldlM f init (A.indexFin i) (A.indexFin i + A.rsizeFin i)
  else return init

@[inline, always_inline, specialize]
def foldl_indexHyps {β : Type v} (f : β → α → β)
    (init : β) (A : RangeArray α) (i : Fin A.size) : β :=
  if isDeleted A i = false then
    A.data.foldl f init (A.indexFin i) (A.indexFin i + A.rsizeFin i)
  else init

@[inline, always_inline, specialize]
def ufoldlM {β : Type v} {m : Type v → Type w} [Monad m] (f : β → α → m β)
    (init : β) (A : RangeArray α) : m β :=
  A.data.foldlM f init A.dsize (A.dsize + A.usize)

@[inline, always_inline, specialize]
def ufoldl {β : Type v} (f : β → α → β)
    (init : β) (A : RangeArray α) : β :=
  A.data.foldl f init A.dsize (A.dsize + A.usize)

def foldlM_index_looped {β : Type v} {m : Type v → Type w} [Monad m] (f : β → α → m β)
    (init : β) (A : RangeArray α) (i : Nat) : m β :=
  if isDeleted A i = false then
    let rec loop (j : Nat) (b : β) : m β := do
      if j < A.rsize i then
        loop (j + 1) (← f b (A.oget i j))
      else return b
    termination_by A.rsize i - j
    loop 0 init
  else return init

/-
theorem unitProp.go.cons_aux (τ : PPA) (l : ILit) {ls : List ILit} {i j : Nat} :
    j = ls.length - i → unitProp.go τ { data := l :: ls } (i + 1) = unitProp.go τ { data := ls } i := by

    /-- Invariants -/

  h_size : dataSize ≤ Size.size data
  h_dataSize_empty : Size.size indexes = 0 → dataSize = 0

  -- No index exceeds `dataSize`
  h_indexes : ∀ {i : Nat} (hi : i < Size.size indexes),
    RangeArray.getIndexFromMarkedIndex (Seq.get indexes ⟨i, hi⟩) ≤ dataSize

  -- The indexes are monotonically increasing in (unmarked) value
  h_indexes_inc : ∀ {i j : Nat} (hij : i ≤ j) (hj : j < Size.size indexes),
-/

--theorem foldlM_index_looped.loop.cons_aux

/-theorem foldlM_index_looped_eq_foldlM_index {β : Type v} {m : Type v → Type w} [Monad m]
    (f : β → α → m β) (init : β) (A : RangeArray α) (i : Nat) :
      A.foldlM_index_looped f init i = A.foldlM_index f init i := by
  have ⟨data, indexes, dataSize, _, h_size, h_dataSize_empty, h_indexes, h_indexes_inc⟩ := A
  have ⟨data⟩ := data
  have ⟨indexes⟩ := indexes
  simp [foldlM_index_looped, foldlM_index]
  induction data with
  | nil =>
    simp [foldlM, foldlM_index]
  | cons x xs ih =>
    simp [foldlM, foldlM_index]
    rw [ih]
    simp [foldlM_index_looped]

#exit -/

/-
theorem unitProp.go.cons_aux (τ : PPA) (l : ILit) {ls : List ILit} {i j : Nat} :
    j = ls.length - i → unitProp.go τ { data := l :: ls } (i + 1) = unitProp.go τ { data := ls } i := by
  intro hj
  ext unit?
  induction j generalizing τ unit? i with
  | zero =>
-/

#check LeanColls.Seq
#check Option.bind
theorem foldlM_index_eq_foldlM {i : Nat} {hi : i < Size.size Ls}
    {sL : List α} (hsL : Seq.get Ls ⟨i, hi⟩ = some sL)
    {β : Type v} {m : Type v → Type w} [Monad m] (f : β → α → m β) (init : β) :
    R.foldlM_index f init i = sL.foldlM f init := by
  have ⟨data, indexes, dataSize, _, h_size, h_dataSize_empty, h_indexes, h_indexes_inc⟩ := A
  have ⟨data⟩ := data
  have ⟨indexes⟩ := indexes
  rw [foldlM_index]
  have := h_models.h_some hi
  simp [hsL] at this
  simp [this]
  sorry
  /-induction sL generalizing Ls with
  | nil =>
    have := h_models.h_sizes hi hsL
    simp at this
    simp [this]
  | cons x xs ih =>
    stop
    done -/
  done

#exit


@[simp]
theorem foldlM_index_empty {β : Type v} {m : Type v → Type w} [Monad m]
    (f : β → α → m β) (init : β) (i : Nat) :
      (empty : RangeArray α).foldlM_index f init i = return init := by
  simp [foldlM_index, empty]

@[simp]
theorem foldl_index_empty {β : Type v} (f : β → α → β) (init : β) (i : Nat) :
      (empty : RangeArray α).foldl_index f init i = init := by
  simp [foldl_index, empty]

@[simp]
theorem foldlM_index_add {β : Type v} {m : Type v → Type w} [Monad m]
    (f : β → α → m β) (init : β) (arr : Array α) (i : Nat) :
      (A.add arr).foldlM_index f init i =
        if i = A.size then arr.foldlM f init
        else A.foldlM_index f init i := by
  simp [foldlM_index, add, foldlM]
  sorry

@[simp]
theorem foldl_index_add {β : Type v} (f : β → α → β) (init : β) (arr : Array α) (i : Nat) :
      (A.add arr).foldl_index f init i =
        if i = A.size then arr.foldl f init
        else A.foldl_index f init i := by
  simp [foldl_index, empty, foldlM_index_empty]
  sorry

theorem foldlM_index_trivial {β : Type v} {m : Type v → Type w} [Monad m]
    {A : RangeArray α} {i : Nat} : (A.rsize i) = 0 →
      ∀ (f : β → α → m β) init, A.foldlM_index f init i = return init := by
  sorry

theorem foldl_index_trivial {β : Type v} {A : RangeArray α} {i : Nat} :
    (A.rsize i) = 0 → ∀ (f : β → α → β) init, A.foldl_index f init i = init := by
  intro hr
  simp [foldl_index, Array.foldl]
  sorry

@[inline]
def foldlM {β : Type v} {m : Type v → Type w} [Monad m]
    (g : β → α → m β) (f : β → β → m β)
    (initg initf : β) (A : RangeArray α)
    (start : Nat := 0) (stop : Nat := A.size) : m β :=
  let minStop := min stop A.size
  let rec loop (i : Nat) (b : β) : m β := do
    if h : i < minStop then
      loop (i + 1) (
        if !A.isDeleted i then
          ← f b (← A.foldlM_index g initg i)
        else b)
    else return b
  termination_by minStop - i
  loop start initf

@[inline]
def foldlM_over_indexes {β : Type v} {m : Type v → Type w} [Monad m]
    (f : β → Nat → m β) (init : β) (A : RangeArray α)
    (start : Nat := 0) (stop : Nat := A.size) : m β :=
  let minStop := min stop A.size
  let rec loop (i : Nat) (b : β) : m β := do
    if h : i < minStop then
      loop (i + 1) (
        if !A.isDeleted i then
          ← f b i
        else b)
    else return b
  termination_by minStop - i
  loop start init

@[inline]
def foldl_over_indexes {β : Type v}
    (f : β → Nat → β) (init : β) (A : RangeArray α)
    (start : Nat := 0) (stop : Nat := A.size) : β :=
  Id.run <| A.foldlM_over_indexes f init start stop

@[inline]
def foldl {β : Type v} (g : β → α → β) (f : β → β → β)
    (initg initf : β) (A : RangeArray α) (start : Nat := 0) (stop : Nat := A.size) :=
  Id.run <| A.foldlM g f initg initf start stop
--Fin.foldRange (fun i b => f_outer b (A.foldl_index f_inner init_inner i)) init_outer start stop

@[simp]
theorem foldlM_empty {β : Type v} {m : Type v → Type w} [Monad m]
    (g : β → α → m β) (f : β → β → m β) (initg initf : β) (start stop : Nat) :
      (empty : RangeArray α).foldlM g f initg initf start stop = return initf := by
  stop
  simp [RangeArray.foldlM]
  simp [foldlM, empty]
  rintro rfl
  exact Array.foldlM_empty _ _ _ _

@[simp]
theorem foldl_empty {β : Type v} (g : β → α → β) (f : β → β → β)
    (initg initf : β) (start stop : Nat) :
      (empty : RangeArray α).foldl g f initg initf start stop = initf := by
  simp [foldl, Id.run]

theorem foldlM_add {β : Type v} {m : Type v → Type w} [Monad m]
    (g : β → α → m β) (f : β → β → m β) (initg initf : β)
    (A : RangeArray α) (arr : Array α) :
      (A.add arr).foldlM g f initg initf = do
        { f (← A.foldlM g f initg initf) (← arr.foldlM g initg) } := by
  stop
  done

theorem foldl_add {β : Type v} (g : β → α → β) (f : β → β → β)
    (initg initf : β) (A : RangeArray α) (arr : Array α) :
      (A.add arr).foldl g f initg initf = f (A.foldl g f initg initf) (arr.foldl g initg) := by
  --simp [foldl, foldlM_add]
  --intro hi f init
  simp [Array.foldl, Id.run]
  --exact foldlM_add (m := Id) g f initg initf _ _
  sorry
  done

end RangeArray
