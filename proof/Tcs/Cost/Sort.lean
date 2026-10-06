/-
  Cost of `Tcs.bubbleSort`.

  This is the reference example for the cost modules: a counting copy of the model
  whose shapes are literally parallel, an agreement theorem `(fC x).1 = f x` proved
  by the same induction as the model, and then exact/one-sided cost bounds.

  Counting rules (see `Tcs.Cost`): the inner loop compares two keys once per step and
  swaps (three moves) exactly when the carried key is strictly greater; the outer
  loop then runs over the prefix, so a sort of `n` elements performs exactly
  `tri (n - 1)` comparisons.
-/
import Tcs.Sort
import Tcs.Cost

namespace Tcs

variable {α : Type u} {β : Type v} [Cmp β]

/-! ## The pass -/

/-- `bubbleUpR` carrying its cost: one comparison per step, plus one swap when the
carried element overtakes a smaller one. -/
def bubbleUpRC (proj : α → β) : α → List α → (List α × α) × Cost
  | a, [] => (([], a), 0)
  | a, b :: bs =>
      if Cmp.blt (proj b) (proj a) then
        let r := bubbleUpRC proj a bs
        ((b :: r.1.1, r.1.2), r.2 + (Cost.cmp1 + Cost.swap))
      else
        let r := bubbleUpRC proj b bs
        ((a :: r.1.1, r.1.2), r.2 + Cost.cmp1)

theorem bubbleUpRC_nil (proj : α → β) (a : α) : bubbleUpRC proj a [] = (([], a), 0) :=
  rfl

theorem bubbleUpRC_cons (proj : α → β) (a b : α) (bs : List α) :
    bubbleUpRC proj a (b :: bs) =
      if Cmp.blt (proj b) (proj a) then
        let r := bubbleUpRC proj a bs
        ((b :: r.1.1, r.1.2), r.2 + (Cost.cmp1 + Cost.swap))
      else
        let r := bubbleUpRC proj b bs
        ((a :: r.1.1, r.1.2), r.2 + Cost.cmp1) :=
  rfl

theorem bubbleUpRC_cons_of_blt {proj : α → β} {a b : α} {bs : List α}
    (h : Cmp.blt (proj b) (proj a) = true) :
    bubbleUpRC proj a (b :: bs) =
      (let r := bubbleUpRC proj a bs
       ((b :: r.1.1, r.1.2), r.2 + (Cost.cmp1 + Cost.swap))) := by
  rw [bubbleUpRC_cons, ite_eq_left h]

theorem bubbleUpRC_cons_of_not_blt {proj : α → β} {a b : α} {bs : List α}
    (h : Cmp.blt (proj b) (proj a) = false) :
    bubbleUpRC proj a (b :: bs) =
      (let r := bubbleUpRC proj b bs
       ((a :: r.1.1, r.1.2), r.2 + Cost.cmp1)) := by
  rw [bubbleUpRC_cons, ite_eq_right (by simp [h])]

/-- The counting pass computes the same thing as the model. -/
theorem bubbleUpRC_fst (proj : α → β) (a : α) :
    ∀ l : List α, (bubbleUpRC proj a l).1 = bubbleUpR proj a l
  | [] => by simp [bubbleUpRC_nil, bubbleUpR]
  | b :: bs => by
      have ih₁ := bubbleUpRC_fst proj a bs
      have ih₂ := bubbleUpRC_fst proj b bs
      by_cases h : Cmp.blt (proj b) (proj a) = true
      · rw [bubbleUpRC_cons_of_blt h, bubbleUpR_cons_of_blt h]
        dsimp only
        rw [ih₁]
      · rw [bubbleUpRC_cons_of_not_blt (by simpa using h),
          bubbleUpR_cons_of_not_blt (by simpa using h)]
        dsimp only
        rw [ih₂]

theorem bubbleUpRC_length (proj : α → β) (a : α) :
    ∀ l : List α, (bubbleUpRC proj a l).1.1.length = l.length
  | [] => by simp [bubbleUpRC_nil]
  | b :: bs => by
      by_cases h : Cmp.blt (proj b) (proj a) = true
      · rw [bubbleUpRC_cons_of_blt h]
        dsimp only
        simp only [List.length_cons, bubbleUpRC_length proj a bs]
      · rw [bubbleUpRC_cons_of_not_blt (by simpa using h)]
        dsimp only
        simp only [List.length_cons, bubbleUpRC_length proj b bs]

/-- A pass performs exactly one comparison per element it steps over. -/
theorem bubbleUpRC_cmp (proj : α → β) (a : α) :
    ∀ l : List α, (bubbleUpRC proj a l).2.cmp = l.length
  | [] => by simp [bubbleUpRC_nil]
  | b :: bs => by
      by_cases h : Cmp.blt (proj b) (proj a) = true
      · rw [bubbleUpRC_cons_of_blt h]
        dsimp only
        simp only [Cost.cmp_add, Cost.cmp_cmp1, Cost.cmp_swap,
          bubbleUpRC_cmp proj a bs, List.length_cons]
      · rw [bubbleUpRC_cons_of_not_blt (by simpa using h)]
        dsimp only
        simp only [Cost.cmp_add, Cost.cmp_cmp1, bubbleUpRC_cmp proj b bs, List.length_cons]

/-- A pass performs at most one swap per comparison. -/
theorem bubbleUpRC_mv_le (proj : α → β) (a : α) :
    ∀ l : List α, (bubbleUpRC proj a l).2.mv ≤ 3 * l.length
  | [] => by simp [bubbleUpRC_nil]
  | b :: bs => by
      have ih₁ := bubbleUpRC_mv_le proj a bs
      have ih₂ := bubbleUpRC_mv_le proj b bs
      by_cases h : Cmp.blt (proj b) (proj a) = true
      · rw [bubbleUpRC_cons_of_blt h]
        dsimp only
        simp only [Cost.mv_add, Cost.mv_cmp1, Cost.mv_swap, List.length_cons]
        omega
      · rw [bubbleUpRC_cons_of_not_blt (by simpa using h)]
        dsimp only
        simp only [Cost.mv_add, Cost.mv_cmp1, List.length_cons]
        omega

/-! ## The sort -/

/-- `bubbleSortAux` carrying its cost. -/
def bubbleSortAuxC (proj : α → β) : Nat → List α → List α × Cost
  | 0, l => (l, 0)
  | _ + 1, [] => ([], 0)
  | n + 1, x :: xs =>
      let r := bubbleUpRC proj x xs
      let s := bubbleSortAuxC proj n r.1.1
      (s.1 ++ [r.1.2], r.2 + s.2)

/-- `bubbleSort` carrying its cost. -/
def bubbleSortC (proj : α → β) (l : List α) : List α × Cost :=
  bubbleSortAuxC proj l.length l

theorem bubbleSortAuxC_zero (proj : α → β) (l : List α) : bubbleSortAuxC proj 0 l = (l, 0) :=
  rfl

theorem bubbleSortAuxC_succ_nil (proj : α → β) (n : Nat) :
    bubbleSortAuxC proj (n + 1) [] = ([], 0) :=
  rfl

theorem bubbleSortAuxC_succ_cons (proj : α → β) (n : Nat) (x : α) (xs : List α) :
    bubbleSortAuxC proj (n + 1) (x :: xs) =
      (let r := bubbleUpRC proj x xs
       let s := bubbleSortAuxC proj n r.1.1
       (s.1 ++ [r.1.2], r.2 + s.2)) :=
  rfl

theorem bubbleSortAuxC_fst (proj : α → β) (fuel : Nat) :
    ∀ l : List α, l.length ≤ fuel → (bubbleSortAuxC proj fuel l).1 = bubbleSortAux proj fuel l := by
  induction fuel with
  | zero => intro l _; rfl
  | succ n ih =>
      intro l hl
      match l with
      | [] => rfl
      | x :: xs =>
        rw [bubbleSortAuxC_succ_cons, bubbleSortAux_succ_cons]
        dsimp only
        rw [bubbleUpRC_fst]
        have hlen : (bubbleUpR proj x xs).1.length ≤ n := by
          rw [bubbleUpR_length]
          simp only [List.length_cons] at hl
          omega
        rw [ih _ hlen]

theorem bubbleSortAuxC_cmp (proj : α → β) (fuel : Nat) :
    ∀ l : List α, l.length ≤ fuel → (bubbleSortAuxC proj fuel l).2.cmp = tri (l.length - 1) := by
  induction fuel with
  | zero =>
      intro l hl
      match l with
      | [] => rfl
      | x :: xs => exact absurd hl (Nat.not_succ_le_zero xs.length)
  | succ n ih =>
      intro l hl
      match l with
      | [] => rfl
      | x :: xs =>
        rw [bubbleSortAuxC_succ_cons]
        dsimp only
        have hlen : (bubbleUpRC proj x xs).1.1.length ≤ n := by
          rw [bubbleUpRC_length]
          simp only [List.length_cons] at hl
          omega
        rw [Cost.cmp_add, bubbleUpRC_cmp, ih _ hlen, bubbleUpRC_length]
        simp only [List.length_cons, Nat.add_sub_cancel]
        have htri := tri_eq_add_pred xs.length
        omega

theorem bubbleSortAuxC_mv_le (proj : α → β) (fuel : Nat) :
    ∀ l : List α, l.length ≤ fuel →
      (bubbleSortAuxC proj fuel l).2.mv ≤ 3 * tri (l.length - 1) := by
  induction fuel with
  | zero =>
      intro l hl
      match l with
      | [] => simp [bubbleSortAuxC_zero]
      | x :: xs => exact absurd hl (Nat.not_succ_le_zero xs.length)
  | succ n ih =>
      intro l hl
      match l with
      | [] => simp [bubbleSortAuxC_succ_nil]
      | x :: xs =>
        rw [bubbleSortAuxC_succ_cons]
        dsimp only
        have hlen : (bubbleUpRC proj x xs).1.1.length ≤ n := by
          rw [bubbleUpRC_length]
          simp only [List.length_cons] at hl
          omega
        have hpass := bubbleUpRC_mv_le proj x xs
        have hrec := ih _ hlen
        rw [Cost.mv_add, bubbleUpRC_length] at *
        simp only [List.length_cons, Nat.add_sub_cancel] at *
        have htri : tri xs.length = xs.length + tri (xs.length - 1) := tri_eq_add_pred xs.length
        omega

theorem bubbleSortC_fst (proj : α → β) (l : List α) :
    (bubbleSortC proj l).1 = bubbleSort proj l :=
  bubbleSortAuxC_fst proj l.length l (Nat.le_refl _)

/-- A bubble sort of `n` elements performs exactly `tri (n - 1)` comparisons. -/
theorem bubbleSortC_cmp (proj : α → β) (l : List α) :
    (bubbleSortC proj l).2.cmp = tri (l.length - 1) :=
  bubbleSortAuxC_cmp proj l.length l (Nat.le_refl _)

theorem bubbleSortC_mv_le (proj : α → β) (l : List α) :
    (bubbleSortC proj l).2.mv ≤ 3 * tri (l.length - 1) :=
  bubbleSortAuxC_mv_le proj l.length l (Nat.le_refl _)

/-- Bubble sort is `O(n^2)` in both units (with a uniform constant `3`). -/
theorem bubbleSortC_bigO (proj : α → β) :
    CostBigOWith 3 List.length (fun l => (bubbleSortC proj l).2) (fun n => n * n) := by
  intro l
  have hcmp := bubbleSortC_cmp proj l
  have hmv := bubbleSortC_mv_le proj l
  have htri := tri_pred_le_sq l.length
  show (bubbleSortC proj l).2 ≤ Cost.const (3 * (l.length * l.length))
  refine Cost.le_const ?_ ?_
  · omega
  · omega

end Tcs
