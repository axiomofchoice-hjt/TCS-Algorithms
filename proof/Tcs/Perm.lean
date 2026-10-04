/-
  Swap → `Perm` bridge for the in-place algorithms.

  They move elements only with `std::swap` (modelled as `Array.swap`). Core has
  `List.Perm.swap'` for two elements at the head, but links nothing to
  `List.set` — and `List.Perm.set` cannot exist, since `set` alone changes the
  multiset. Only the swap form, two `set`s exchanging values, is a permutation.
-/
import Tcs.Spec

namespace Tcs

namespace List

/-- Inductive workhorse: pulling `l[j]` to the front while writing `x` at `j`. -/
theorem perm_getElem_set_cons {α : Type u} (l : List α) (j : Nat) (x : α)
    (hj : j < l.length) : (l[j] :: l.set j x).Perm (x :: l) := by
  induction l generalizing j with
  | nil => simp at hj
  | cons y s ih =>
    cases j with
    | zero =>
      simpa [List.set_cons_zero] using List.Perm.swap' x y (List.Perm.refl s)
    | succ k =>
      have hk : k < s.length := by simpa using hj
      have ih' : (s[k] :: s.set k x).Perm (x :: s) := ih k hk
      simpa using
        (List.Perm.swap' s[k] y (List.Perm.refl (s.set k x))).symm.trans
          ((List.Perm.cons y ih').trans (List.Perm.swap' x y (List.Perm.refl s)))

/-- Swapping positions `i` and `j` of a list is a permutation (`i = j` allowed). -/
theorem perm_set_swap {α : Type u} (l : List α) {i j : Nat} (hi : i < l.length)
    (hj : j < l.length) : ((l.set i (l[j]'hj)).set j (l[i]'hi)).Perm l := by
  induction l generalizing i j with
  | nil => simp at hi
  | cons y s ih =>
    cases i with
    | zero =>
      cases j with
      | zero => simp [List.set_cons_zero]
      | succ k =>
        have hk : k < s.length := by simpa using hj
        simpa [List.set_cons_zero] using perm_getElem_set_cons s k y hk
    | succ i' =>
      cases j with
      | zero =>
        have hi' : i' < s.length := by simpa using hi
        simpa [List.set_cons_zero] using perm_getElem_set_cons s i' y hi'
      | succ j' =>
        have hi' : i' < s.length := by simpa using hi
        have hj' : j' < s.length := by simpa using hj
        simpa using List.Perm.cons y (ih hi' hj')

end List

namespace Array

/-- **The bridge every in-place algorithm needs**: `Array.swap` only permutes
its elements, so a swap-based algorithm is `Permutes`. -/
theorem swap_perm {α : Type u} (xs : Array α) (i j : Nat) (hi : i < xs.size)
    (hj : j < xs.size) : (xs.swap i j hi hj).toList.Perm xs.toList := by
  have hi' : i < xs.toList.length := by simpa using hi
  have hj' : j < xs.toList.length := by simpa using hj
  simpa [Array.toList_swap, Array.getElem_toList] using
    List.perm_set_swap (l := xs.toList) hi' hj'

end Array

/-! Concrete values, so a mis-stated lemma cannot pass as vacuously true. -/

example : (Array.swap #[1, 2, 3, 4] 0 2 (by decide) (by decide)).toList = [3, 2, 1, 4] := rfl

example : (Array.swap #[1, 2, 3, 4] 1 3 (by decide) (by decide)).toList = [1, 4, 3, 2] := rfl

example : (Array.swap #[1, 2, 3] 1 1 (by decide) (by decide)).toList = [1, 2, 3] := rfl

/-- The bridge composes with the core `List.Perm` API. -/
example {α : Type u} (xs : Array α) (i j : Nat) (hi : i < xs.size) (hj : j < xs.size) :
    (xs.swap i j hi hj).toList.Nodup ↔ xs.toList.Nodup :=
  (Array.swap_perm xs i j hi hj).nodup_iff

end Tcs
