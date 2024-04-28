/-

Things to put in LeanColls.

-/

import LeanColls

namespace LeanColls.Seq

variable [Seq C τ] [LawfulSeq C τ]

theorem get_snoc_lt (cont : C) {i : Nat} (hi : i < size cont) (x : τ) :
    get (snoc cont x) (⟨i, by rw [size_snoc]; exact Nat.lt_succ_of_lt hi⟩) = get cont ⟨i, hi⟩ := by
  sorry
  done

@[simp]
theorem get_snoc_eq (cont : C) (x : τ) :
    get (snoc cont x) (⟨size cont, by rw [size_snoc]; exact Nat.lt_succ_self _⟩) = x := by
  sorry
  done

theorem get_snoc (cont : C) (x : τ) (i : Fin (size (snoc cont x))) :
    get (snoc cont x) i = if h : i.val < size cont then get cont ⟨i, h⟩ else x := by
  sorry
  done

end LeanColls.Seq
