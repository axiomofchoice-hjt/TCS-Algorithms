/-
  Cost of `Tcs.Cyclesort.cyclesort`.

  The counting copy mirrors the C++ in `include/tcs/cyclesort.hpp` operation for
  operation, with the charge rules of `Tcs.Cost`:

  * `destination_range` scans the whole range, paying one key comparison per element
    and a second one when the strict test fails (`proj(key) > proj(*it)`), so at most
    `2 * a.size` comparisons per call; its `key` parameter is taken by value, which is
    one element move per call;
  * `std::find_if` calls its predicate on a *copy* of the element, so each scanned
    position costs one comparison and one move; the scan stops at the first element
    with a different key and hence takes at most `eqCount` steps;
  * `std::swap` is `Cost.swap` (three moves);
  * the `left <= it && it < right` range test compares iterators, not keys, and is
    therefore not charged a key comparison.

  With those charges the copy performs *exactly* as many key comparisons as the real
  C++ (the `destRangeC` + `firstNeC` counts below), and its move count is the C++'s
  (swaps plus `find_if` copies) plus one key copy per `destination_range` call.

  The number of swaps is what makes the algorithm interesting: every swap settles a
  position, so there are at most `a.size` of them (the verified model already proves
  `unsettledCount_swap_lt`). The move count is nevertheless quadratic, because every
  element copied into a `find_if` predicate and every `destination_range` key copy is
  a move: at most `a.size` scans of length `a.size`.

  The proofs use the potential `unsettledCount`: each swapping inner iteration drops
  it by at least one, which is exactly what bounds the total number of iterations by
  `2 * a.size` and hence both cost units by `7 * a.size ^ 2`.
-/
import Tcs.Cost
import Tcs.Cyclesort

namespace Tcs

open Cyclesort

variable {α : Type u} {β : Type v} [Cmp β]

/-! ## `destination_range` -/

/-- `destination_range` carrying its cost: `(gt, eq)` are the two counters of the C++
scan (`gt = ltCount`, `eq = eqCount`) and the cost is one comparison per element plus
a second one when the strict test fails. -/
def destRangeC (proj : α → β) : List α → β → (Nat × Nat) × Cost
  | [], _ => ((0, 0), 0)
  | x :: xs, k =>
    if Cmp.blt (proj x) k = true then
      let r := destRangeC proj xs k
      ((r.1.1 + 1, r.1.2), r.2 + Cost.cmp1)
    else if Cmp.beq (proj x) k = true then
      let r := destRangeC proj xs k
      ((r.1.1, r.1.2 + 1), r.2 + (Cost.cmp1 + Cost.cmp1))
    else
      let r := destRangeC proj xs k
      ((r.1.1, r.1.2), r.2 + (Cost.cmp1 + Cost.cmp1))

theorem destRangeC_nil (proj : α → β) (k : β) : destRangeC proj [] k = ((0, 0), 0) :=
  rfl

theorem destRangeC_cons (proj : α → β) (x : α) (xs : List α) (k : β) :
    destRangeC proj (x :: xs) k =
      (if Cmp.blt (proj x) k = true then
        (let r := destRangeC proj xs k
         ((r.1.1 + 1, r.1.2), r.2 + Cost.cmp1))
      else if Cmp.beq (proj x) k = true then
        (let r := destRangeC proj xs k
         ((r.1.1, r.1.2 + 1), r.2 + (Cost.cmp1 + Cost.cmp1)))
      else
        (let r := destRangeC proj xs k
         ((r.1.1, r.1.2), r.2 + (Cost.cmp1 + Cost.cmp1)))) :=
  rfl

/-- The two counters of the scan are exactly the two `countP`s of the model, so
`destination_range`'s block really is `[ltCount, ltCount + eqCount)`. -/
theorem destRangeC_fst (proj : α → β) : ∀ (l : List α) (k : β),
    (destRangeC proj l k).1 =
      (l.countP (fun x => Cmp.blt (proj x) k), l.countP (fun x => Cmp.beq (proj x) k))
  | [], k => rfl
  | x :: xs, k => by
      rw [destRangeC_cons]
      by_cases h : Cmp.blt (proj x) k = true
      · rw [ite_eq_left h]
        dsimp only
        rw [destRangeC_fst proj xs k]
        have hb : Cmp.beq (proj x) k = false := Cmp.not_beq_of_blt h
        rw [List.countP_cons_of_pos (p := fun x => Cmp.blt (proj x) k) h,
          List.countP_cons_of_neg (p := fun x => Cmp.beq (proj x) k) (by simp [hb])]
      · rw [ite_eq_right h]
        dsimp only
        rw [destRangeC_fst proj xs k]
        by_cases hb : Cmp.beq (proj x) k = true
        · rw [ite_eq_left hb]
          dsimp only
          rw [List.countP_cons_of_neg (p := fun x => Cmp.blt (proj x) k) h,
            List.countP_cons_of_pos (p := fun x => Cmp.beq (proj x) k) hb]
        · rw [ite_eq_right hb]
          dsimp only
          rw [List.countP_cons_of_neg (p := fun x => Cmp.blt (proj x) k) h,
            List.countP_cons_of_neg (p := fun x => Cmp.beq (proj x) k) hb]

/-- The scan performs no element moves (the key copy is charged by its caller). -/
theorem destRangeC_mv (proj : α → β) : ∀ (l : List α) (k : β), (destRangeC proj l k).2.mv = 0
  | [], k => rfl
  | x :: xs, k => by
      rw [destRangeC_cons]
      by_cases h : Cmp.blt (proj x) k = true
      · rw [ite_eq_left h]
        dsimp only
        simp only [Cost.mv_add, Cost.mv_cmp1, destRangeC_mv proj xs k, Nat.add_zero]
      · rw [ite_eq_right h]
        dsimp only
        by_cases hb : Cmp.beq (proj x) k = true
        · rw [ite_eq_left hb]
          dsimp only
          simp only [Cost.mv_add, Cost.mv_cmp1, destRangeC_mv proj xs k, Nat.add_zero]
        · rw [ite_eq_right hb]
          dsimp only
          simp only [Cost.mv_add, Cost.mv_cmp1, destRangeC_mv proj xs k, Nat.add_zero]

/-- At most two comparisons per scanned element: the strict test, plus the equality
test when the strict one fails. -/
theorem destRangeC_cmp_le (proj : α → β) : ∀ (l : List α) (k : β),
    (destRangeC proj l k).2.cmp ≤ 2 * l.length
  | [], k => by rw [destRangeC_nil]; simp
  | x :: xs, k => by
      rw [destRangeC_cons]
      have ih := destRangeC_cmp_le proj xs k
      by_cases h : Cmp.blt (proj x) k = true
      · rw [ite_eq_left h]
        dsimp only
        simp only [Cost.cmp_add, Cost.cmp_cmp1, List.length_cons]
        omega
      · rw [ite_eq_right h]
        dsimp only
        by_cases hb : Cmp.beq (proj x) k = true
        · rw [ite_eq_left hb]
          dsimp only
          simp only [Cost.cmp_add, Cost.cmp_cmp1, List.length_cons]
          omega
        · rw [ite_eq_right hb]
          dsimp only
          simp only [Cost.cmp_add, Cost.cmp_cmp1, List.length_cons]
          omega

/-! ## `std::find_if` -/

/-- `firstNe` carrying its cost: one comparison and one move (the by-value predicate
parameter) per scanned position. -/
def firstNeC (proj : α → β) (a : Array α) (k : β) : Nat → Nat → Option Nat × Cost
  | _, 0 => (none, 0)
  | lo, n + 1 =>
    if neKey proj a k lo = true then (some lo, Cost.cmp1 + Cost.mv1)
    else
      let r := firstNeC proj a k (lo + 1) n
      (r.1, r.2 + (Cost.cmp1 + Cost.mv1))

theorem firstNeC_zero (proj : α → β) (a : Array α) (k : β) (lo : Nat) :
    firstNeC proj a k lo 0 = (none, 0) :=
  rfl

theorem firstNeC_succ (proj : α → β) (a : Array α) (k : β) (lo n : Nat) :
    firstNeC proj a k lo (n + 1) =
      (if neKey proj a k lo = true then (some lo, Cost.cmp1 + Cost.mv1)
       else (let r := firstNeC proj a k (lo + 1) n
             (r.1, r.2 + (Cost.cmp1 + Cost.mv1)))) :=
  rfl

/-- Agreement with the verified search. -/
theorem firstNeC_fst (proj : α → β) (a : Array α) (k : β) :
    ∀ (lo n : Nat), (firstNeC proj a k lo n).1 = firstNe proj a k lo n
  | _, 0 => rfl
  | lo, n + 1 => by
      rw [firstNeC_succ]
      by_cases h : neKey proj a k lo = true
      · rw [ite_eq_left h]
        rw [show firstNe proj a k lo (n + 1)
            = (if neKey proj a k lo = true then some lo
               else firstNe proj a k (lo + 1) n) from rfl,
          ite_eq_left h]
      · rw [ite_eq_right h]
        dsimp only
        rw [show firstNe proj a k lo (n + 1)
            = (if neKey proj a k lo = true then some lo
               else firstNe proj a k (lo + 1) n) from rfl,
          ite_eq_right h]
        exact firstNeC_fst proj a k (lo + 1) n

/-- The scan stops after at most `n` comparisons. -/
theorem firstNeC_cmp_le (proj : α → β) (a : Array α) (k : β) :
    ∀ (lo n : Nat), (firstNeC proj a k lo n).2.cmp ≤ n
  | _, 0 => by rw [firstNeC_zero]; simp
  | lo, n + 1 => by
      rw [firstNeC_succ]
      by_cases h : neKey proj a k lo = true
      · rw [ite_eq_left h]
        simp only [Cost.cmp_add, Cost.cmp_cmp1, Cost.cmp_mv1, Nat.add_zero]
        omega
      · rw [ite_eq_right h]
        dsimp only
        have ih := firstNeC_cmp_le proj a k (lo + 1) n
        simp only [Cost.cmp_add, Cost.cmp_cmp1, Cost.cmp_mv1, Nat.add_zero]
        omega

/-- ... and after at most `n` predicate copies, i.e. moves. -/
theorem firstNeC_mv_le (proj : α → β) (a : Array α) (k : β) :
    ∀ (lo n : Nat), (firstNeC proj a k lo n).2.mv ≤ n
  | _, 0 => by rw [firstNeC_zero]; simp
  | lo, n + 1 => by
      rw [firstNeC_succ]
      by_cases h : neKey proj a k lo = true
      · rw [ite_eq_left h]
        simp only [Cost.mv_add, Cost.mv_cmp1, Cost.mv_mv1]
        omega
      · rw [ite_eq_right h]
        dsimp only
        have ih := firstNeC_mv_le proj a k (lo + 1) n
        simp only [Cost.mv_add, Cost.mv_cmp1, Cost.mv_mv1]
        omega

/-! ## Two bounds on the model's bookkeeping -/

/-- `unsettledCount` counts a filtered range, so it is at most the array length. -/
theorem unsettledCount_le_size (proj : α → β) (a : Array α) : unsettledCount proj a ≤ a.size := by
  unfold unsettledCount
  refine Nat.le_trans (List.length_filter_le _ _) ?_
  rw [List.length_range]
  exact Nat.le_refl _

/-- A key occurs at most `a.size` times. -/
theorem eqCount_le_size (proj : α → β) (a : Array α) (k : β) : eqCount proj a k ≤ a.size := by
  have h := ltCount_add_eqCount_le_size proj a k
  omega

/-- The `find_if` scan can never run past the array: if `firstNe` finds a partner in
the block `[ltCount, ltCount + eqCount)` then that position is in bounds. -/
theorem firstNe_lt_size {proj : α → β} {a : Array α} {k : β} {p : Nat}
    (h : firstNe proj a k (ltCount proj a k) (eqCount proj a k) = some p) : p < a.size := by
  have h1 := (firstNe_some h).2.1
  have h2 := ltCount_add_eqCount_le_size proj a k
  omega

/-! ## The inner `while (true)` -/

/-- `innerAux` carrying its cost.  A trip through the body pays the whole
`destination_range` scan (one comparison per element, two when the strict test fails),
the key copy into `destination_range`'s by-value parameter (one move), and, when a swap
happens, one comparison and one move per `find_if` step plus the swap itself.

The `left <= it && it < right` test compares *indices*, not keys, so it is not charged
as a key comparison; `destination_range`'s second comparison is.

The `0`-fuel case is not vacuous: the model stops there without entering the body, but
the C++ still runs the body once (`destination_range`, then the range test, which must
hold because a zero fuel means every position is settled).  Charging that final trip is
what makes the counts below match the real C++ exactly. -/
def innerAuxC (proj : α → β) : Nat → (a : Array α) → (it : Nat) → it < a.size → Array α × Cost
  | 0, a, it, hit => (a, (destRangeC proj a.toList (proj (a[it]'hit))).2 + Cost.mv1)
  | n + 1, a, it, hit =>
    let dc := destRangeC proj a.toList (proj (a[it]'hit))
    if _ : InBlock proj a it (proj (a[it]'hit)) then
      (a, dc.2 + Cost.mv1)
    else
      match hfn : firstNe proj a (proj (a[it]'hit)) (ltCount proj a (proj (a[it]'hit)))
          (eqCount proj a (proj (a[it]'hit))) with
      | none => (a, dc.2 + Cost.mv1)
      | some p =>
        let fc := firstNeC proj a (proj (a[it]'hit))
            (ltCount proj a (proj (a[it]'hit))) (eqCount proj a (proj (a[it]'hit)))
        let r := innerAuxC proj n (a.swap it p hit (by
            have h1 := (firstNe_some hfn).2.1
            have h2 := ltCount_add_eqCount_le_size proj a (proj (a[it]'hit))
            omega)) it (by rw [Array.size_swap]; exact hit)
        (r.1, (dc.2 + Cost.mv1) + (fc.2 + Cost.swap) + r.2)

theorem innerAuxC_zero (proj : α → β) (a : Array α) (it : Nat) (hit : it < a.size) :
    innerAuxC proj 0 a it hit =
      (a, (destRangeC proj a.toList (proj (a[it]'hit))).2 + Cost.mv1) :=
  rfl

theorem innerAuxC_succ (proj : α → β) (n : Nat) (a : Array α) (it : Nat) (hit : it < a.size) :
    innerAuxC proj (n + 1) a it hit =
      (let dc := destRangeC proj a.toList (proj (a[it]'hit))
       if _ : InBlock proj a it (proj (a[it]'hit)) then
         (a, dc.2 + Cost.mv1)
       else
         match hfn : firstNe proj a (proj (a[it]'hit)) (ltCount proj a (proj (a[it]'hit)))
             (eqCount proj a (proj (a[it]'hit))) with
         | none => (a, dc.2 + Cost.mv1)
         | some p =>
           let fc := firstNeC proj a (proj (a[it]'hit))
               (ltCount proj a (proj (a[it]'hit))) (eqCount proj a (proj (a[it]'hit)))
           let r := innerAuxC proj n (a.swap it p hit (by
               have h1 := (firstNe_some hfn).2.1
               have h2 := ltCount_add_eqCount_le_size proj a (proj (a[it]'hit))
               omega)) it (by rw [Array.size_swap]; exact hit)
           (r.1, (dc.2 + Cost.mv1) + (fc.2 + Cost.swap) + r.2)) :=
  rfl

/-- The model's inner loop, with the same case structure: this is what makes the
agreement proof below mechanical. -/
theorem innerAux_succ (proj : α → β) (n : Nat) (a : Array α) (it : Nat) (hit : it < a.size) :
    innerAux proj (n + 1) a it hit =
      (if _ : InBlock proj a it (proj (a[it]'hit)) then a
       else
         match hfn : firstNe proj a (proj (a[it]'hit)) (ltCount proj a (proj (a[it]'hit)))
             (eqCount proj a (proj (a[it]'hit))) with
         | none => a
         | some p =>
           innerAux proj n (a.swap it p hit (by
               have h1 := (firstNe_some hfn).2.1
               have h2 := ltCount_add_eqCount_le_size proj a (proj (a[it]'hit))
               omega)) it (by rw [Array.size_swap]; exact hit)) :=
  rfl

theorem innerAuxC_hit_irrel (proj : α → β) (n : Nat) (a : Array α) (it : Nat)
    (h₁ h₂ : it < a.size) : innerAuxC proj n a it h₁ = innerAuxC proj n a it h₂ :=
  congrArg (innerAuxC proj n a it) (Subsingleton.elim h₁ h₂)

/-- `innerAuxC` also does not depend on the (irrelevant) proof used for the partner's
swap: this lets the bound proofs replace the definition's inlined proof term by any
other proof of the same bound. -/
theorem innerAuxC_swap_irrel (proj : α → β) (n : Nat) (a : Array α) (it p : Nat)
    (hit : it < a.size) (hp : p < a.size) :
    ∀ (hj : p < a.size) (h₁ : it < (a.swap it p hit hj).size),
      innerAuxC proj n (a.swap it p hit hj) it h₁
        = innerAuxC proj n (a.swap it p hit hp) it (by rw [Array.size_swap]; exact hit) := by
  intro hj h₁
  have h : hj = hp := Subsingleton.elim hj hp
  cases h
  exact innerAuxC_hit_irrel proj n (a.swap it p hit hp) it _ _

/-- The counting inner loop computes what the model computes. -/
theorem innerAuxC_fst (proj : α → β) (n : Nat) :
    ∀ (a : Array α) (it : Nat) (hit : it < a.size),
      (innerAuxC proj n a it hit).1 = innerAux proj n a it hit := by
  induction n with
  | zero => intro a it hit; rfl
  | succ n ih =>
      intro a it hit
      rw [innerAuxC_succ, innerAux_succ]
      dsimp only
      by_cases hIn : InBlock proj a it (proj (a[it]'hit))
      · rw [dite_eq_left hIn, dite_eq_left hIn]
      · rw [dite_eq_right hIn, dite_eq_right hIn]
        split
        · rfl
        · rename_i p hfn
          dsimp only
          rw [ih]

theorem innerAuxC_size (proj : α → β) (n : Nat) (a : Array α) (it : Nat) (hit : it < a.size) :
    (innerAuxC proj n a it hit).1.size = a.size := by
  rw [innerAuxC_fst, innerAux_size]

/-- One swap drops `unsettledCount` by at least one: `unsettledCount_swap_lt`
specialised to the partner that the `find_if` scan returns. -/
theorem unsettledCount_swap_succ_le {proj : α → β} {a : Array α} {it p : Nat} (hit : it < a.size)
    (hIn : ¬ InBlock proj a it (proj (a[it]'hit))) (hp : p < a.size)
    (hfn : firstNe proj a (proj (a[it]'hit)) (ltCount proj a (proj (a[it]'hit)))
        (eqCount proj a (proj (a[it]'hit))) = some p) :
    unsettledCount proj (a.swap it p hit hp) + 1 ≤ unsettledCount proj a :=
  Nat.succ_le_of_lt (swap_partner_spec hit hIn hp hfn).1

/-- The final (breaking) trip of the inner loop: it costs one `destination_range` scan
and changes neither the array nor the potential.  All three ways of breaking out of the
loop (`n = 0`, `it` already in its block, no partner found) end in the same goals, so the
four-conjunct invariant is discharged here once. -/
private theorem innerAuxC_inv_break (proj : α → β) (a : Array α) (it : Nat) (hit : it < a.size) :
    ((destRangeC proj a.toList (proj (a[it]'hit))).2 + Cost.mv1).cmp
        + unsettledCount proj a * (3 * a.size)
      ≤ unsettledCount proj a * (3 * a.size) + (2 * a.size)
    ∧ ((destRangeC proj a.toList (proj (a[it]'hit))).2 + Cost.mv1).mv
      ≤ (unsettledCount proj a - unsettledCount proj a) * (a.size + 4) + 1
    ∧ a.size = a.size
    ∧ unsettledCount proj a ≤ unsettledCount proj a := by
  have hdc := destRangeC_cmp_le proj a.toList (proj (a[it]'hit))
  rw [Array.length_toList] at hdc
  have hmv : (destRangeC proj a.toList (proj (a[it]'hit))).2.mv = 0 :=
    destRangeC_mv proj a.toList (proj (a[it]'hit))
  refine ⟨?_, ?_, rfl, Nat.le_refl _⟩
  · simp only [Cost.cmp_add, Cost.cmp_mv1, Nat.add_zero]
    omega
  · simp only [Cost.mv_add, Cost.mv_mv1, Nat.zero_add, Nat.sub_self, Nat.zero_mul]
    omega

/-- The potential invariant of the inner loop.  Writing `U a` for
`unsettledCount proj a`, a swapping trip costs at most `3 * a.size` comparisons and
`a.size + 4` moves, a final (breaking) trip costs one `destination_range` scan, and
every swapping trip drops `U` by at least one; the two inequalities below express
exactly that.

The comparison inequality says that the cost plus `U` of the result, times the
per-trip comparison charge, fits in the starting potential plus one final trip; the
move inequality says that the cost is paid for by the potential actually consumed. -/
theorem innerAuxC_inv (proj : α → β) (n : Nat) (a : Array α) (it : Nat) (hit : it < a.size) :
    (innerAuxC proj n a it hit).2.cmp
        + unsettledCount proj (innerAuxC proj n a it hit).1 * (3 * a.size)
      ≤ unsettledCount proj a * (3 * a.size) + (2 * a.size)
    ∧ (innerAuxC proj n a it hit).2.mv
      ≤ (unsettledCount proj a - unsettledCount proj (innerAuxC proj n a it hit).1)
          * (a.size + 4) + 1
    ∧ (innerAuxC proj n a it hit).1.size = a.size
    ∧ unsettledCount proj (innerAuxC proj n a it hit).1 ≤ unsettledCount proj a := by
  induction n generalizing a it hit with
  | zero =>
      rw [innerAuxC_zero]
      dsimp only
      exact innerAuxC_inv_break proj a it hit
  | succ n ih =>
      by_cases hIn : InBlock proj a it (proj (a[it]'hit))
      · rw [innerAuxC_succ, dite_eq_left hIn]
        dsimp only
        exact innerAuxC_inv_break proj a it hit
      · rw [innerAuxC_succ, dite_eq_right hIn]
        dsimp only
        split
        · rename_i hfn
          exact innerAuxC_inv_break proj a it hit
        · rename_i p hfn
          have hp : p < a.size := firstNe_lt_size hfn
          rw [innerAuxC_swap_irrel proj n a it p hit hp]
          dsimp only
          obtain ⟨ih1, ih2, ih3, ih4⟩ :=
            ih (a.swap it p hit hp) it (by rw [Array.size_swap]; exact hit)
          have hsz : (a.swap it p hit hp).size = a.size := Array.size_swap
          simp only [hsz] at ih1 ih2
          have hdccmp : (destRangeC proj a.toList (proj (a[it]'hit))).2.cmp ≤ 2 * a.size := by
            have h := destRangeC_cmp_le proj a.toList (proj (a[it]'hit))
            rwa [Array.length_toList] at h
          have hdcmv : (destRangeC proj a.toList (proj (a[it]'hit))).2.mv = 0 :=
            destRangeC_mv proj a.toList (proj (a[it]'hit))
          have hfccmp : (firstNeC proj a (proj (a[it]'hit)) (ltCount proj a (proj (a[it]'hit)))
              (eqCount proj a (proj (a[it]'hit)))).2.cmp ≤ eqCount proj a (proj (a[it]'hit)) :=
            firstNeC_cmp_le proj a (proj (a[it]'hit)) (ltCount proj a (proj (a[it]'hit)))
              (eqCount proj a (proj (a[it]'hit)))
          have hfcmv : (firstNeC proj a (proj (a[it]'hit)) (ltCount proj a (proj (a[it]'hit)))
              (eqCount proj a (proj (a[it]'hit)))).2.mv ≤ eqCount proj a (proj (a[it]'hit)) :=
            firstNeC_mv_le proj a (proj (a[it]'hit)) (ltCount proj a (proj (a[it]'hit)))
              (eqCount proj a (proj (a[it]'hit)))
          have hw : eqCount proj a (proj (a[it]'hit)) ≤ a.size :=
            eqCount_le_size proj a (proj (a[it]'hit))
          have hsucc : unsettledCount proj (a.swap it p hit hp) + 1 ≤ unsettledCount proj a :=
            unsettledCount_swap_succ_le hit hIn hp hfn
          have hmul1 : unsettledCount proj (a.swap it p hit hp) * (3 * a.size)
              + (3 * a.size) ≤ unsettledCount proj a * (3 * a.size) := by
            have h := Nat.mul_le_mul_right (3 * a.size) hsucc
            rwa [Nat.add_mul, Nat.one_mul] at h
          have hmul2 : (a.size + 4)
              + (unsettledCount proj (a.swap it p hit hp)
                  - unsettledCount proj (innerAuxC proj n (a.swap it p hit hp) it
                      (by rw [Array.size_swap]; exact hit)).1) * (a.size + 4)
              ≤ (unsettledCount proj a
                  - unsettledCount proj (innerAuxC proj n (a.swap it p hit hp) it
                      (by rw [Array.size_swap]; exact hit)).1) * (a.size + 4) := by
            have h1 : unsettledCount proj (a.swap it p hit hp)
                  - unsettledCount proj (innerAuxC proj n (a.swap it p hit hp) it
                      (by rw [Array.size_swap]; exact hit)).1 + 1
                ≤ unsettledCount proj a
                  - unsettledCount proj (innerAuxC proj n (a.swap it p hit hp) it
                      (by rw [Array.size_swap]; exact hit)).1 := by omega
            have h2 := Nat.mul_le_mul_right (a.size + 4) h1
            rw [Nat.add_mul, Nat.one_mul] at h2
            omega
          refine ⟨?_, ?_, ?_, ?_⟩
          · simp only [Cost.cmp_add, Cost.cmp_mv1, Cost.cmp_swap, Nat.add_zero]
            omega
          · simp only [Cost.mv_add, Cost.mv_mv1, Cost.mv_swap]
            omega
          · rw [ih3, hsz]
          · omega

/-! ## The inner loop as a function of the current array -/

/-- `innerAux` fuelled by the number of unsettled positions, carrying its cost. -/
abbrev innerC (proj : α → β) (a : Array α) (it : Nat) (hit : it < a.size) : Array α × Cost :=
  innerAuxC proj (unsettledCount proj a) a it hit

theorem innerC_fst (proj : α → β) (a : Array α) (it : Nat) (hit : it < a.size) :
    (innerC proj a it hit).1 = inner proj a it hit :=
  innerAuxC_fst proj (unsettledCount proj a) a it hit

/-! ## The outer `for` -/

/-- The outer loop carrying its cost.  The proof that `it` is in bounds is not needed:
the counting function tests `it < a.size` itself, which keeps its recursive calls free
of dependent proof arguments. -/
def outerAuxC (proj : α → β) : Nat → (a : Array α) → (it : Nat) → Array α × Cost
  | 0, a, _ => (a, 0)
  | n + 1, a, it =>
    if h : it < a.size then
      let r := innerC proj a it h
      let s := outerAuxC proj n r.1 (it + 1)
      (s.1, r.2 + s.2)
    else (a, 0)

theorem outerAuxC_zero (proj : α → β) (a : Array α) (it : Nat) :
    outerAuxC proj 0 a it = (a, 0) :=
  rfl

theorem outerAuxC_succ (proj : α → β) (n : Nat) (a : Array α) (it : Nat) :
    outerAuxC proj (n + 1) a it =
      (if h : it < a.size then
        (let r := innerC proj a it h
         let s := outerAuxC proj n r.1 (it + 1)
         (s.1, r.2 + s.2))
       else (a, 0)) :=
  rfl

/-- The model's outer loop, with the same case structure. -/
theorem outerAux_succ (proj : α → β) (n : Nat) (a : Array α) (it : Nat) (hle : it ≤ a.size) :
    outerAux proj (n + 1) a it hle =
      (if h : it < a.size then
        outerAux proj n (inner proj a it h) (it + 1) (by rw [inner_size]; omega)
       else a) :=
  rfl

/-- The counting outer loop computes what the model computes. -/
theorem outerAuxC_fst (proj : α → β) (n : Nat) :
    ∀ (a : Array α) (it : Nat) (hle : it ≤ a.size),
      (outerAuxC proj n a it).1 = outerAux proj n a it hle := by
  induction n with
  | zero => intro a it hle; rfl
  | succ n ih =>
      intro a it hle
      rw [outerAuxC_succ, outerAux_succ]
      dsimp only
      by_cases h : it < a.size
      · rw [dite_eq_left h, dite_eq_left h]
        dsimp only
        rw [innerC_fst]
        exact ih _ _ _
      · rw [dite_eq_right h, dite_eq_right h]

/-- The same potential invariant for the outer loop.  Each outer iteration spends one
inner loop, whose charge is paid for by the `unsettledCount` it consumes, plus one
final trip charged to the `a.size - it` remaining outer iterations. -/
theorem outerAuxC_inv (proj : α → β) (n : Nat) (a : Array α) (it : Nat)
    (hn : a.size - it ≤ n) :
    (outerAuxC proj n a it).2.cmp
        + unsettledCount proj (outerAuxC proj n a it).1 * (3 * a.size)
      ≤ unsettledCount proj a * (3 * a.size) + (a.size - it) * (2 * a.size)
    ∧ (outerAuxC proj n a it).2.mv
      ≤ (unsettledCount proj a - unsettledCount proj (outerAuxC proj n a it).1)
          * (a.size + 4) + (a.size - it)
    ∧ (outerAuxC proj n a it).1.size = a.size
    ∧ unsettledCount proj (outerAuxC proj n a it).1 ≤ unsettledCount proj a := by
  induction n generalizing a it with
  | zero =>
      have hzero : a.size - it = 0 := by omega
      rw [outerAuxC_zero, hzero, Nat.zero_mul, Nat.add_zero]
      simp
  | succ n ih =>
      by_cases h : it < a.size
      · rw [outerAuxC_succ, dite_eq_left h]
        dsimp only [innerC]
        obtain ⟨hi1, hi2, hi3, hi4⟩ :=
          innerAuxC_inv proj (unsettledCount proj a) a it h
        have hn' : (innerAuxC proj (unsettledCount proj a) a it h).1.size - (it + 1) ≤ n := by
          rw [innerAuxC_size]; omega
        obtain ⟨ih1, ih2, ih3, ih4⟩ :=
          ih (innerAuxC proj (unsettledCount proj a) a it h).1 (it + 1) hn'
        have hsz : (innerAuxC proj (unsettledCount proj a) a it h).1.size = a.size :=
          innerAuxC_size proj (unsettledCount proj a) a it h
        simp only [hsz] at ih1 ih2
        have hc : (2 * a.size) + (a.size - (it + 1)) * (2 * a.size)
            = (a.size - it) * (2 * a.size) := by
          have h1 : 1 + (a.size - (it + 1)) = a.size - it := by omega
          rw [← h1, Nat.add_mul, Nat.one_mul]
        have hm : (unsettledCount proj a
                - unsettledCount proj (innerAuxC proj (unsettledCount proj a) a it h).1)
              * (a.size + 4)
            + (unsettledCount proj (innerAuxC proj (unsettledCount proj a) a it h).1
                - unsettledCount proj (outerAuxC proj n
                    (innerAuxC proj (unsettledCount proj a) a it h).1 (it + 1)).1)
              * (a.size + 4)
            = (unsettledCount proj a
                - unsettledCount proj (outerAuxC proj n
                    (innerAuxC proj (unsettledCount proj a) a it h).1 (it + 1)).1)
              * (a.size + 4) := by
          rw [← Nat.add_mul]
          congr 1
          omega
        refine ⟨?_, ?_, ?_, ?_⟩
        · simp only [Cost.cmp_add]
          omega
        · simp only [Cost.mv_add]
          omega
        · rw [ih3, hsz]
        · omega
      · have hzero : a.size - it = 0 := by omega
        rw [outerAuxC_succ, dite_eq_right h, hzero, Nat.zero_mul, Nat.add_zero]
        dsimp only
        simp

/-- Cycle sort carrying its cost. -/
def cyclesortC (proj : α → β) (a : Array α) : Array α × Cost :=
  outerAuxC proj a.size a 0

theorem cyclesortC_fst (proj : α → β) (a : Array α) :
    (cyclesortC proj a).1 = cyclesort proj a :=
  outerAuxC_fst proj a.size a 0 (Nat.zero_le _)

/-! ## Explicit polynomial bounds -/

/-- The comparison bound of the whole run, before substituting `unsettledCount ≤ a.size`:
the outer loop charges `A` final trips of `2 * A` comparisons and the swaps consume at
most `A` more trips of `3 * A`, so `5 * A * A` comparisons suffice. -/
theorem cyclesort_cmp_poly_le (A U : Nat) (hU : U ≤ A) :
    U * (3 * A) + A * (2 * A) ≤ 7 * (A * A) := by
  have h1 : U * (3 * A) ≤ A * (3 * A) := Nat.mul_le_mul_right _ hU
  have h2 : A * (3 * A) + A * (2 * A) = 5 * (A * A) := by
    rw [← Nat.mul_add]
    rw [show 3 * A + 2 * A = 5 * A by omega]
    rw [← Nat.mul_assoc, Nat.mul_comm A 5, Nat.mul_assoc]
  calc U * (3 * A) + A * (2 * A) ≤ A * (3 * A) + A * (2 * A) := Nat.add_le_add_right h1 _
    _ = 5 * (A * A) := h2
    _ ≤ 7 * (A * A) := by omega

/-- The move bound of the whole run, before substituting `unsettledCount ≤ a.size`. -/
theorem cyclesort_mv_poly_le (A : Nat) : A * (A + 4) + A ≤ 7 * (A * A) := by
  have h2 : A * (A + 4) + A = A * (A + 5) := by
    rw [Nat.mul_add A A 4, Nat.mul_add A A 5, Nat.mul_succ A 4]
    omega
  rw [h2]
  cases A with
  | zero => simp
  | succ m =>
      have h : (m + 1) + 5 ≤ 7 * (m + 1) := by omega
      calc (m + 1) * ((m + 1) + 5) ≤ (m + 1) * (7 * (m + 1)) := Nat.mul_le_mul_left _ h
        _ = 7 * ((m + 1) * (m + 1)) := by
              rw [← Nat.mul_assoc, Nat.mul_comm (m + 1) 7, Nat.mul_assoc]

/-- Cycle sort performs at most `7 * a.size ^ 2` key comparisons.  Each outer
iteration ends in one final `destination_range` scan of at most `2 * a.size`
comparisons, and the at most `a.size` swaps make the remaining scans cost at most
`3 * a.size` comparisons each, so `5 * a.size ^ 2` comparisons suffice. -/
theorem cyclesortC_cmp_le (proj : α → β) (a : Array α) :
    (cyclesortC proj a).2.cmp ≤ 7 * (a.size * a.size) := by
  have hinv := outerAuxC_inv proj a.size a 0 (by omega)
  have hU : unsettledCount proj a ≤ a.size := unsettledCount_le_size proj a
  have hle : (cyclesortC proj a).2.cmp
      ≤ unsettledCount proj a * (3 * a.size) + a.size * (2 * a.size) := by
    dsimp only [cyclesortC]
    have h := hinv.1
    simp only [Nat.sub_zero] at h
    omega
  calc (cyclesortC proj a).2.cmp
        ≤ unsettledCount proj a * (3 * a.size) + a.size * (2 * a.size) := hle
    _ ≤ 7 * (a.size * a.size) := cyclesort_cmp_poly_le a.size (unsettledCount proj a) hU

/-- Cycle sort performs at most `7 * a.size ^ 2` element moves.  Only the swaps are
`O(n)` (at most `a.size` of them, three moves each); the key copied into
`destination_range` and the element copied into every `find_if` predicate make the
total quadratic in the worst case. -/
theorem cyclesortC_mv_le (proj : α → β) (a : Array α) :
    (cyclesortC proj a).2.mv ≤ 7 * (a.size * a.size) := by
  have hinv := outerAuxC_inv proj a.size a 0 (by omega)
  have hU : unsettledCount proj a ≤ a.size := unsettledCount_le_size proj a
  have hle : (cyclesortC proj a).2.mv ≤ unsettledCount proj a * (a.size + 4) + a.size := by
    dsimp only [cyclesortC]
    have h := hinv.2.1
    simp only [Nat.sub_zero] at h
    have hsub : unsettledCount proj a - unsettledCount proj (outerAuxC proj a.size a 0).1
        ≤ unsettledCount proj a := Nat.sub_le _ _
    have hmul := Nat.mul_le_mul_right (a.size + 4) hsub
    omega
  calc (cyclesortC proj a).2.mv ≤ unsettledCount proj a * (a.size + 4) + a.size := hle
    _ ≤ a.size * (a.size + 4) + a.size := by
          have hmul := Nat.mul_le_mul_right (a.size + 4) hU
          omega
    _ ≤ 7 * (a.size * a.size) := cyclesort_mv_poly_le a.size

/-- Cycle sort is `O(n^2)` in comparisons. -/
theorem cyclesortC_cmp_bigO (proj : α → β) :
    IsBigOWith 7 (fun a : Array α => a.size) (fun a => (cyclesortC proj a).2.cmp)
      (fun n => n * n) :=
  fun a => cyclesortC_cmp_le proj a

/-- Cycle sort is `O(n^2)` in moves. -/
theorem cyclesortC_mv_bigO (proj : α → β) :
    IsBigOWith 7 (fun a : Array α => a.size) (fun a => (cyclesortC proj a).2.mv)
      (fun n => n * n) :=
  fun a => cyclesortC_mv_le proj a

/-! ## The number of swaps is linear

Cycle sort's selling point is that it performs `O(n)` writes even though it needs
`O(n ^ 2)` comparisons.  `cyclesortC`'s move count does not show that directly (the
by-value copies dominate), so a second counting copy tracks *only* the swaps, with the
same recursion shapes.  The same potential, `unsettledCount`, bounds them. -/

/-- `innerAux` counting only the swaps. -/
def innerAuxS (proj : α → β) : Nat → (a : Array α) → (it : Nat) → it < a.size → Array α × Nat
  | 0, a, _, _ => (a, 0)
  | n + 1, a, it, hit =>
    if _ : InBlock proj a it (proj (a[it]'hit)) then (a, 0)
    else
      match hfn : firstNe proj a (proj (a[it]'hit)) (ltCount proj a (proj (a[it]'hit)))
          (eqCount proj a (proj (a[it]'hit))) with
      | none => (a, 0)
      | some p =>
        let r := innerAuxS proj n (a.swap it p hit (by
            have h1 := (firstNe_some hfn).2.1
            have h2 := ltCount_add_eqCount_le_size proj a (proj (a[it]'hit))
            omega)) it (by rw [Array.size_swap]; exact hit)
        (r.1, r.2 + 1)

theorem innerAuxS_zero (proj : α → β) (a : Array α) (it : Nat) (hit : it < a.size) :
    innerAuxS proj 0 a it hit = (a, 0) :=
  rfl

theorem innerAuxS_succ (proj : α → β) (n : Nat) (a : Array α) (it : Nat) (hit : it < a.size) :
    innerAuxS proj (n + 1) a it hit =
      (if _ : InBlock proj a it (proj (a[it]'hit)) then (a, 0)
       else
         match hfn : firstNe proj a (proj (a[it]'hit)) (ltCount proj a (proj (a[it]'hit)))
             (eqCount proj a (proj (a[it]'hit))) with
         | none => (a, 0)
         | some p =>
           let r := innerAuxS proj n (a.swap it p hit (by
               have h1 := (firstNe_some hfn).2.1
               have h2 := ltCount_add_eqCount_le_size proj a (proj (a[it]'hit))
               omega)) it (by rw [Array.size_swap]; exact hit)
           (r.1, r.2 + 1)) :=
  rfl

theorem innerAuxS_hit_irrel (proj : α → β) (n : Nat) (a : Array α) (it : Nat)
    (h₁ h₂ : it < a.size) : innerAuxS proj n a it h₁ = innerAuxS proj n a it h₂ :=
  congrArg (innerAuxS proj n a it) (Subsingleton.elim h₁ h₂)

theorem innerAuxS_swap_irrel (proj : α → β) (n : Nat) (a : Array α) (it p : Nat)
    (hit : it < a.size) (hp : p < a.size) :
    ∀ (hj : p < a.size) (h₁ : it < (a.swap it p hit hj).size),
      innerAuxS proj n (a.swap it p hit hj) it h₁
        = innerAuxS proj n (a.swap it p hit hp) it (by rw [Array.size_swap]; exact hit) := by
  intro hj h₁
  have h : hj = hp := Subsingleton.elim hj hp
  cases h
  exact innerAuxS_hit_irrel proj n (a.swap it p hit hp) it _ _

theorem innerAuxS_size (proj : α → β) (n : Nat) (a : Array α) (it : Nat) (hit : it < a.size) :
    (innerAuxS proj n a it hit).1.size = a.size := by
  induction n generalizing a it hit with
  | zero => rfl
  | succ n ih =>
      rw [innerAuxS_succ]
      by_cases hIn : InBlock proj a it (proj (a[it]'hit))
      · rw [dite_eq_left hIn]
      · rw [dite_eq_right hIn]
        split
        · rename_i hfn
          rfl
        · rename_i p hfn
          dsimp only
          rw [ih, Array.size_swap]

/-- Every swap strictly decreases `unsettledCount`, which starts at most `a.size`. -/
theorem innerAuxS_inv (proj : α → β) (n : Nat) (a : Array α) (it : Nat) (hit : it < a.size) :
    (innerAuxS proj n a it hit).2 + unsettledCount proj (innerAuxS proj n a it hit).1
      ≤ unsettledCount proj a := by
  induction n generalizing a it hit with
  | zero => rw [innerAuxS_zero]; simp
  | succ n ih =>
      by_cases hIn : InBlock proj a it (proj (a[it]'hit))
      · rw [innerAuxS_succ, dite_eq_left hIn]
        simp
      · rw [innerAuxS_succ, dite_eq_right hIn]
        dsimp only
        split
        · rename_i hfn
          simp
        · rename_i p hfn
          have hp : p < a.size := firstNe_lt_size hfn
          rw [innerAuxS_swap_irrel proj n a it p hit hp]
          dsimp only
          have hrec := ih (a.swap it p hit hp) it (by rw [Array.size_swap]; exact hit)
          have hdec := unsettledCount_swap_succ_le hit hIn hp hfn
          omega

/-- `innerAux` fuelled by the number of unsettled positions, counting only swaps. -/
abbrev innerS (proj : α → β) (a : Array α) (it : Nat) (hit : it < a.size) : Array α × Nat :=
  innerAuxS proj (unsettledCount proj a) a it hit

/-- The outer loop counting only swaps. -/
def outerAuxS (proj : α → β) : Nat → (a : Array α) → (it : Nat) → Array α × Nat
  | 0, a, _ => (a, 0)
  | n + 1, a, it =>
    if h : it < a.size then
      let r := innerS proj a it h
      let s := outerAuxS proj n r.1 (it + 1)
      (s.1, r.2 + s.2)
    else (a, 0)

theorem outerAuxS_zero (proj : α → β) (a : Array α) (it : Nat) :
    outerAuxS proj 0 a it = (a, 0) :=
  rfl

theorem outerAuxS_succ (proj : α → β) (n : Nat) (a : Array α) (it : Nat) :
    outerAuxS proj (n + 1) a it =
      (if h : it < a.size then
        (let r := innerS proj a it h
         let s := outerAuxS proj n r.1 (it + 1)
         (s.1, r.2 + s.2))
       else (a, 0)) :=
  rfl

/-- The outer loop's swaps fit in the initial potential as well. -/
theorem outerAuxS_inv (proj : α → β) (n : Nat) (a : Array α) (it : Nat)
    (hn : a.size - it ≤ n) :
    (outerAuxS proj n a it).2 + unsettledCount proj (outerAuxS proj n a it).1
      ≤ unsettledCount proj a := by
  induction n generalizing a it with
  | zero => rw [outerAuxS_zero]; simp
  | succ n ih =>
      by_cases h : it < a.size
      · rw [outerAuxS_succ, dite_eq_left h]
        dsimp only [innerS]
        have hi := innerAuxS_inv proj (unsettledCount proj a) a it h
        have hn' : (innerAuxS proj (unsettledCount proj a) a it h).1.size - (it + 1) ≤ n := by
          rw [innerAuxS_size]; omega
        have ih' := ih (innerAuxS proj (unsettledCount proj a) a it h).1 (it + 1) hn'
        omega
      · rw [outerAuxS_succ, dite_eq_right h]
        simp

/-- Cycle sort counting only its swaps. -/
def cyclesortS (proj : α → β) (a : Array α) : Array α × Nat :=
  outerAuxS proj a.size a 0

/-- Cycle sort performs at most `a.size` swaps, hence at most `3 * a.size` moves
through `std::swap`: this is the C++'s "`O(n)` writes" claim. -/
theorem cyclesortS_le (proj : α → β) (a : Array α) : (cyclesortS proj a).2 ≤ a.size := by
  have h := outerAuxS_inv proj a.size a 0 (by omega)
  have hU : unsettledCount proj a ≤ a.size := unsettledCount_le_size proj a
  dsimp only [cyclesortS]
  omega

end Tcs
