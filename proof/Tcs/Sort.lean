/-
  The sorting primitive behind every C++ `bubble_sort` call.

  The model is the C++ loop itself rather than any other sort with the same
  contract: one pass carries the maximum of the range to the right end, and the
  outer loop then runs on the prefix, peeling the maxima off from the right. Keeping
  the model operational is what makes its cost countable (`Tcs.Cost`): a pass over
  `m` elements performs exactly `m - 1` key comparisons.
-/
import Tcs.Select

namespace Tcs

variable {α : Type u} {β : Type v} [Cmp β]

/-! ## One bubble pass -/

/-- `m` is a maximum of `l`: it occurs in `l` and no key of `l` exceeds it. -/
def IsMaxKey (proj : α → β) (l : List α) (m : α) : Prop :=
  m ∈ l ∧ ∀ z ∈ l, KeyLe proj z m

/-- C++'s inner loop body: carry `a` rightwards through `l`, swapping with the next
element whenever that element's key is strictly smaller. The result is the carried
sequence without its maximum together with that maximum, so the caller can peel the
maximum off the right end - which is exactly what the shrinking C++ range does. -/
def bubbleUpR (proj : α → β) : α → List α → List α × α
  | a, [] => ([], a)
  | a, b :: bs =>
      if Cmp.blt (proj b) (proj a) then
        let r := bubbleUpR proj a bs
        (b :: r.1, r.2)
      else
        let r := bubbleUpR proj b bs
        (a :: r.1, r.2)

theorem bubbleUpR_cons (proj : α → β) (a b : α) (bs : List α) :
    bubbleUpR proj a (b :: bs) =
      if Cmp.blt (proj b) (proj a) then
        let r := bubbleUpR proj a bs
        (b :: r.1, r.2)
      else
        let r := bubbleUpR proj b bs
        (a :: r.1, r.2) :=
  rfl

theorem bubbleUpR_cons_of_blt {proj : α → β} {a b : α} {bs : List α}
    (h : Cmp.blt (proj b) (proj a) = true) :
    bubbleUpR proj a (b :: bs) =
      (let r := bubbleUpR proj a bs
       (b :: r.1, r.2)) := by
  rw [bubbleUpR_cons, ite_eq_left h]

theorem bubbleUpR_cons_of_not_blt {proj : α → β} {a b : α} {bs : List α}
    (h : Cmp.blt (proj b) (proj a) = false) :
    bubbleUpR proj a (b :: bs) =
      (let r := bubbleUpR proj b bs
       (a :: r.1, r.2)) := by
  rw [bubbleUpR_cons, ite_eq_right (by simp [h])]

theorem bubbleUpR_length (proj : α → β) (a : α) :
    ∀ l : List α, (bubbleUpR proj a l).1.length = l.length
  | [] => rfl
  | b :: bs => by
      by_cases h : Cmp.blt (proj b) (proj a) = true
      · rw [bubbleUpR_cons_of_blt h]
        dsimp only
        simp only [List.length_cons, bubbleUpR_length proj a bs]
      · rw [bubbleUpR_cons_of_not_blt (by simpa using h)]
        dsimp only
        simp only [List.length_cons, bubbleUpR_length proj b bs]

theorem bubbleUpR_perm (proj : α → β) (a : α) : ∀ l : List α,
    ((bubbleUpR proj a l).1 ++ [(bubbleUpR proj a l).2]).Perm (a :: l)
  | [] => by simp [bubbleUpR]
  | b :: bs => by
      have ih₁ := bubbleUpR_perm proj a bs
      have ih₂ := bubbleUpR_perm proj b bs
      by_cases h : Cmp.blt (proj b) (proj a) = true
      · rw [bubbleUpR_cons_of_blt h]
        dsimp only
        exact (List.Perm.cons b ih₁).trans (List.Perm.swap a b bs)
      · rw [bubbleUpR_cons_of_not_blt (by simpa using h)]
        dsimp only
        exact List.Perm.cons a ih₂

/-- The maximum a pass carries out is a maximum of the whole list, so it may be
appended to the prefix that the remaining passes sort. -/
theorem bubbleUpR_max (proj : α → β) (a : α) :
    ∀ l : List α, IsMaxKey proj (a :: l) (bubbleUpR proj a l).2
  | [] => ⟨by simp [bubbleUpR], by
      intro z hz
      rw [List.mem_singleton] at hz
      rw [hz]
      exact Cmp.ble_refl _⟩
  | b :: bs => by
      have ih₁ := bubbleUpR_max proj a bs
      have ih₂ := bubbleUpR_max proj b bs
      by_cases h : Cmp.blt (proj b) (proj a) = true
      · rw [bubbleUpR_cons_of_blt h]
        dsimp only
        refine ⟨?_, ?_⟩
        · rcases List.mem_cons.mp ih₁.1 with h' | h'
          · rw [h']; exact List.mem_cons_self
          · exact List.mem_cons_of_mem a (List.mem_cons_of_mem b h')
        · intro z hz
          rcases List.mem_cons.mp hz with hza | hz'
          · rw [hza]
            exact ih₁.2 a List.mem_cons_self
          · rcases List.mem_cons.mp hz' with hzb | hzbs
            · rw [hzb]
              exact Cmp.ble_trans (Cmp.ble_of_blt h) (ih₁.2 a List.mem_cons_self)
            · exact ih₁.2 z (List.mem_cons_of_mem a hzbs)
      · rw [bubbleUpR_cons_of_not_blt (by simpa using h)]
        dsimp only
        refine ⟨List.mem_cons_of_mem a ih₂.1, ?_⟩
        intro z hz
        rcases List.mem_cons.mp hz with hza | hz'
        · rw [hza]
          exact Cmp.ble_trans (Cmp.ble_of_not_blt (by simpa using h))
            (ih₂.2 b List.mem_cons_self)
        · exact ih₂.2 z hz'

/-! ## The outer loop -/

/-- C++'s `bubble_sort(first, last)`: `fuel` bounds the length of `l`, which keeps
the recursion structural. One pass leaves the maximum at the right end and the outer
loop then sorts the prefix, so the maxima are re-appended one by one. -/
def bubbleSortAux (proj : α → β) : Nat → List α → List α
  | 0, l => l
  | _ + 1, [] => []
  | n + 1, x :: xs =>
      let r := bubbleUpR proj x xs
      bubbleSortAux proj n r.1 ++ [r.2]

/-- C++'s `bubble_sort` on a range. -/
def bubbleSort (proj : α → β) (l : List α) : List α :=
  bubbleSortAux proj l.length l

theorem bubbleSortAux_succ_cons (proj : α → β) (n : Nat) (x : α) (xs : List α) :
    bubbleSortAux proj (n + 1) (x :: xs) =
      (let r := bubbleUpR proj x xs
       bubbleSortAux proj n r.1 ++ [r.2]) :=
  rfl

theorem bubbleSortAux_perm (proj : α → β) (fuel : Nat) :
    ∀ l : List α, l.length ≤ fuel → (bubbleSortAux proj fuel l).Perm l := by
  induction fuel with
  | zero => intro l _; exact List.Perm.refl l
  | succ n ih =>
      intro l hl
      match l with
      | [] => exact List.Perm.refl []
      | x :: xs =>
        rw [bubbleSortAux_succ_cons]
        dsimp only
        have hlen : (bubbleUpR proj x xs).1.length ≤ n := by
          rw [bubbleUpR_length]
          simp only [List.length_cons] at hl
          omega
        exact (List.Perm.append_right _ (ih _ hlen)).trans (bubbleUpR_perm proj x xs)

theorem bubbleSortAux_sorted (proj : α → β) (fuel : Nat) :
    ∀ l : List α, l.length ≤ fuel → Sorted (KeyLe proj) (bubbleSortAux proj fuel l) := by
  induction fuel with
  | zero =>
      intro l hl
      match l with
      | [] => exact sorted_nil _
      | x :: xs => exact absurd hl (Nat.not_succ_le_zero xs.length)
  | succ n ih =>
      intro l hl
      match l with
      | [] => exact sorted_nil _
      | x :: xs =>
        rw [bubbleSortAux_succ_cons]
        dsimp only
        have hlen : (bubbleUpR proj x xs).1.length ≤ n := by
          rw [bubbleUpR_length]
          simp only [List.length_cons] at hl
          omega
        show List.Pairwise (KeyLe proj) (bubbleSortAux proj n (bubbleUpR proj x xs).1 ++
          [(bubbleUpR proj x xs).2])
        rw [List.pairwise_append]
        refine ⟨ih _ hlen, List.pairwise_singleton _ _, ?_⟩
        intro a ha b hb
        rw [List.mem_singleton] at hb
        subst hb
        have hmem : a ∈ x :: xs :=
          (bubbleUpR_perm proj x xs).mem_iff.mp
            (List.mem_append_left _ ((bubbleSortAux_perm proj n _ hlen).mem_iff.mp ha))
        exact (bubbleUpR_max proj x xs).2 a hmem

theorem bubbleSort_perm (proj : α → β) (l : List α) : (bubbleSort proj l).Perm l :=
  bubbleSortAux_perm proj l.length l (Nat.le_refl _)

theorem bubbleSort_sorted (proj : α → β) (l : List α) :
    Sorted (KeyLe proj) (bubbleSort proj l) :=
  bubbleSortAux_sorted proj l.length l (Nat.le_refl _)

theorem bubbleSort_length (proj : α → β) (l : List α) : (bubbleSort proj l).length = l.length :=
  (bubbleSort_perm proj l).length_eq

end Tcs
