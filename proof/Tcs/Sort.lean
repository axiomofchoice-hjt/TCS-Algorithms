/-
  The general sorting primitive reused by every range-based algorithm proof.

  The C++ `bubble_sort(range)` is modelled by core's `mergeSort` with the key
  comparison. Both are comparison sorts for the same total order, and everything
  proved below is arrangement-agnostic, so any sorting routine with the same
  contract would do. Keeping `sortRange` here (rather than next to BFPRT, where
  it was first needed) makes it available to the merge and block stages without
  pulling in the selection theory.
-/
import Tcs.Select

namespace Tcs

variable {α : Type u} {β : Type v} [Cmp β]

/-- C++'s `bubble_sort` on a range. Core's `mergeSort` is used as the model: both
are stable comparison sorts for the same total order, so they return the same
list, and everything used below is arrangement-agnostic anyway. -/
def sortRange (proj : α → β) (l : List α) : List α :=
  l.mergeSort (fun a b => Cmp.ble (proj a) (proj b))

theorem sortRange_perm (proj : α → β) (l : List α) : (sortRange proj l).Perm l :=
  List.mergeSort_perm l _

theorem sortRange_sorted (proj : α → β) (l : List α) : Sorted (KeyLe proj) (sortRange proj l) :=
  List.pairwise_mergeSort (le := fun a b => Cmp.ble (proj a) (proj b))
    (fun _ _ _ h₁ h₂ => Cmp.ble_trans h₁ h₂)
    (fun a b => by rcases Cmp.ble_total (proj a) (proj b) with h | h <;> simp [h]) l

end Tcs
