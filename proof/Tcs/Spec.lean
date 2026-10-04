/-
  Specification layer (Lean core + Std only; no Mathlib, fully offline).

  Modelling conventions used by every proof module:
  * algorithms are `Array α → Array α`, mirroring a C++ iterator range
    `[first, last)`; `Array.swap` / `Array.set` model `std::swap` / assignment;
  * "rearranged" is `List.Perm` on `Array.toList`;
  * "sorted" is `Sorted` below; `R` models a C++ `proj` + comparator pair;
  * "stable" labels elements with their original index and orders by key only;
  * "O(1) extra space" is constructive: algorithms only `swap` / `set` in place.
-/

namespace Tcs

/-- Adjacent elements satisfy `R` (core `List.Pairwise`). -/
def Sorted {α : Type u} (R : α → α → Prop) (xs : List α) : Prop :=
  xs.Pairwise R

/-- An array is sorted when its `toList` is. -/
def ArraySorted {α : Type u} (R : α → α → Prop) (a : Array α) : Prop :=
  Sorted R a.toList

/-- The output is a permutation of the input (an in-place rearrangement). -/
def Permutes {α : Type u} (f : Array α → Array α) : Prop :=
  ∀ a, List.Perm (f a).toList a.toList

/-- A sort: output sorted, and a permutation of the input. -/
def IsSort {α : Type u} (R : α → α → Prop) (f : Array α → Array α) : Prop :=
  (∀ a, ArraySorted R (f a)) ∧ Permutes f

theorem arraySorted_iff {α : Type u} (R : α → α → Prop) (a : Array α) :
    ArraySorted R a ↔ Sorted R a.toList :=
  Iff.rfl

theorem sorted_nil {α : Type u} (R : α → α → Prop) : Sorted R [] := by
  simp [Sorted]

theorem sorted_singleton {α : Type u} (R : α → α → Prop) (x : α) : Sorted R [x] := by
  simp [Sorted]

theorem sorted_cons_iff {α : Type u} (R : α → α → Prop) (x : α) (xs : List α) :
    Sorted R (x :: xs) ↔ (∀ y ∈ xs, R x y) ∧ Sorted R xs := by
  simp [Sorted, List.pairwise_cons]

end Tcs
