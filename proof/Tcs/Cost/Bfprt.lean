/-
  Cost of median-of-medians selection (`include/tcs/bfprt.hpp`).

  This module gives a counting transcription `bfprtAuxC` of the verified model
  `Tcs.Bfprt.bfprtAux` (same recursion, same list manipulations) and bounds its
  worst-case cost. The counting rules are the ones documented in `Tcs.Cost`:

  * every group of five is sorted with the model's bubble sort, charged its exact
    cost `bubbleSortC` (10 comparisons, at most 30 moves);
  * moving a group's median into `[0, len/5)` is one `std::swap`, charged 3 moves;
  * the `len < 5` case is one bubble sort, again charged `bubbleSortC`;
  * each `std::partition` pass evaluates its predicate once per element
    (`std::partition` is required to do exactly that) and performs at most one
    swap per element; since the C++ lambda takes its argument by value, each
    predicate call also copies the element. We charge `l.length` comparisons,
    `l.length` argument copies and up to `3 * l.length` swap moves, i.e.
    `Cost.cmpN l.length + Cost.mvN (4 * l.length)`;
  * the rank tests around the partitions are index arithmetic; one key comparison
    is charged for them.

  The main results are the agreement `bfprtAuxC_fst`, the explicit linear bounds
  `bfprtAuxC_cmp_le` / `bfprtAuxC_mv_le` (both `<= 400 * n`) and the uniform big-O
  `bfprtAuxC_bigO : CostBigOWith 400 List.length ... (fun n => n)`.

  The linear bound is the median-of-medians argument, formalized as follows.

  * `groupPass_take_medians` / `groupPass_take_eq_medians`: because the C++ loop
    processes group `0` first, index `i` still holds group `i`'s median after the
    whole pass, so `(groupPass proj g l).take g` *is* the list of the `g` group
    medians `medianOf proj l i = (bubbleSort proj (group i))[2]`.
  * `three_mul_medians_count_le` / `_ge`: in a sorted group of five, three elements
    are `<=` the median (resp. `>=` it), so counting over the disjoint groups gives
    `3 * (#medians <= t) <= #(elements <= t)`, and dually.
  * `partition_lengths_le_of_medians`: the pivot is the rank-`g/2` element of those
    medians (`bfprtAux_spec` + `isKthSmallest_of_perm`), hence at least
    `3 * (g/2 + 1)` elements are `>=` it and at least `3 * (g - g/2)` are `<=` it,
    so the two recursive sides have length at most `n - 3 * (g - g/2)` and
    `n - 3 * (g/2 + 1)`; with `g = n/5` both are at most `(7/10) * n + c`.
  * `bfprtAuxC_le_linear`: with `g = n/5` and `B = n - 3 * (g - g/2)`,
    `g + B <= (9/10) * n`, and the recurrence `T n <= T g + T B + work`
    closes with constant `400`.

  The earlier quadratic fallback (`bfprtAuxC_cmp_le_quadratic`,
  `bfprtAuxC_mv_le_quadratic`, `bfprtAuxC_bigO_quadratic`, constant `100`) is kept:
  it rests only on `partition_lengths_le_of_rank`, and `cost_quad_arith`.

  History: an earlier version of the model (`Tcs.Bfprt`) ran `groupPass` in
  *decreasing* index order, which broke the first bullet; it has since been aligned
  with the C++ loop.
-/
import Tcs.Cost
import Tcs.Cost.Sort
import Tcs.Bfprt

namespace Tcs
namespace Bfprt

variable {α : Type u} {β : Type v} [Cmp β]

/-! ## The costed group pass -/

/-- `placeMedian` carrying its cost: the exact cost of the group's bubble sort plus
one `std::swap` of the median into the slot at index `i` (charged `3` moves). -/
def placeMedianC (proj : α → β) (i : Nat) (l : List α) : List α × Cost :=
  let r := bubbleSortC proj ((l.drop (5 * i)).take 5)
  (swapAt (l.take (5 * i) ++ r.1 ++ l.drop (5 * i + 5)) i (5 * i + 2), r.2 + Cost.mvN 3)

/-- Unfolding equation, so that the recursive definitions are never unfolded by
`simp`/`rw` (see the project brief). -/
theorem placeMedianC_eq (proj : α → β) (i : Nat) (l : List α) :
    placeMedianC proj i l =
      (let r := bubbleSortC proj ((l.drop (5 * i)).take 5)
       (swapAt (l.take (5 * i) ++ r.1 ++ l.drop (5 * i + 5)) i (5 * i + 2),
        r.2 + Cost.mvN 3)) :=
  rfl

/-- The counting `placeMedian` computes the model's `placeMedian`. -/
theorem placeMedianC_fst (proj : α → β) (i : Nat) (l : List α) :
    (placeMedianC proj i l).1 = placeMedian proj i l := by
  rw [placeMedianC_eq]
  dsimp only
  rw [bubbleSortC_fst]
  rfl

/-- The counting `placeMedian` keeps the length. -/
theorem placeMedianC_length (proj : α → β) (i : Nat) (l : List α) :
    (placeMedianC proj i l).1.length = l.length := by
  rw [placeMedianC_fst]
  exact (placeMedian_perm proj i l).length_eq

/-- `groupPass` carrying its cost: pass `i` first, exactly like the C++ loop. -/
def groupPassC (proj : α → β) : Nat → List α → List α × Cost
  | 0, l => (l, 0)
  | i + 1, l =>
      let r := groupPassC proj i l
      let s := placeMedianC proj i r.1
      (s.1, r.2 + s.2)

theorem groupPassC_zero (proj : α → β) (l : List α) : groupPassC proj 0 l = (l, 0) :=
  rfl

theorem groupPassC_succ (proj : α → β) (i : Nat) (l : List α) :
    groupPassC proj (i + 1) l =
      (let r := groupPassC proj i l
       let s := placeMedianC proj i r.1
       (s.1, r.2 + s.2)) :=
  rfl

/-- The counting group pass computes the model's `groupPass`. -/
theorem groupPassC_fst (proj : α → β) : ∀ i (l : List α),
    (groupPassC proj i l).1 = groupPass proj i l
  | 0, l => rfl
  | i + 1, l => by
      rw [groupPassC_succ, groupPass]
      dsimp only
      rw [placeMedianC_fst, groupPassC_fst proj i]

/-- The counting group pass keeps the length. -/
theorem groupPassC_length (proj : α → β) : ∀ i (l : List α),
    (groupPassC proj i l).1.length = l.length
  | 0, l => rfl
  | i + 1, l => by
      rw [groupPassC_succ]
      dsimp only
      rw [placeMedianC_length, groupPassC_length proj i]

/-- The length of a full group of five. -/
theorem group_take_length (l : List α) {i : Nat} (h : 5 * i + 5 ≤ l.length) :
    ((l.drop (5 * i)).take 5).length = 5 := by
  rw [List.length_take, List.length_drop]
  omega

theorem tri_four : tri 4 = 10 := rfl

/-- One group sort plus one median swap costs at most 10 comparisons. -/
theorem placeMedianC_cmp_le (proj : α → β) (i : Nat) (l : List α)
    (h : 5 * i + 5 ≤ l.length) : (placeMedianC proj i l).2.cmp ≤ 10 := by
  rw [placeMedianC_eq]
  dsimp only
  rw [Cost.cmp_add, bubbleSortC_cmp, group_take_length l h, Cost.cmp_mvN, tri_four]
  simp

/-- One group sort plus one median swap costs at most 33 moves. -/
theorem placeMedianC_mv_le (proj : α → β) (i : Nat) (l : List α)
    (h : 5 * i + 5 ≤ l.length) : (placeMedianC proj i l).2.mv ≤ 33 := by
  rw [placeMedianC_eq]
  dsimp only
  have hmv := bubbleSortC_mv_le proj ((l.drop (5 * i)).take 5)
  rw [group_take_length l h, tri_four] at hmv
  rw [Cost.mv_add, Cost.mv_mvN]
  omega

/-- The whole group pass costs at most `10 * g` comparisons. -/
theorem groupPassC_cmp_le (proj : α → β) :
    ∀ g (l : List α), 5 * g ≤ l.length → (groupPassC proj g l).2.cmp ≤ 10 * g
  | 0, l, _ => by simp [groupPassC_zero]
  | g + 1, l, h => by
      rw [groupPassC_succ]
      dsimp only
      have hlen : 5 * g ≤ (groupPassC proj g l).1.length := by
        rw [groupPassC_length]
        omega
      have hrec := groupPassC_cmp_le proj g l (by omega)
      have hstep := placeMedianC_cmp_le proj g (groupPassC proj g l).1 (by
        rw [groupPassC_length]; omega)
      rw [Cost.cmp_add]
      omega

/-- The whole group pass costs at most `33 * g` moves. -/
theorem groupPassC_mv_le (proj : α → β) :
    ∀ g (l : List α), 5 * g ≤ l.length → (groupPassC proj g l).2.mv ≤ 33 * g
  | 0, l, _ => by simp [groupPassC_zero]
  | g + 1, l, h => by
      rw [groupPassC_succ]
      dsimp only
      have hlen : 5 * g ≤ (groupPassC proj g l).1.length := by
        rw [groupPassC_length]
        omega
      have hrec := groupPassC_mv_le proj g l (by omega)
      have hstep := placeMedianC_mv_le proj g (groupPassC proj g l).1 (by
        rw [groupPassC_length]; omega)
      rw [Cost.mv_add]
      omega


/-! ## The group medians land in `[0, g)`

The C++ loop processes group `0` first, then group `1`, and so on. Because the
destination index `i` is smaller than every slot of group `i` and of every later
group, no later pass can disturb the value written at index `i`. The two lemmas
below make this precise: after `t` passes, indices `< t` hold the group medians and
the suffix from `5 * t` is untouched.

The median of group `j` is the index-`2` element of the group after `bubbleSort`. -/

/-- The median of group `j` of `l` (the `j`-th value the group pass writes into
`[0, len / 5)`). -/
def medianOf (proj : α → β) (l : List α) (j : Nat) (h : 5 * j + 5 ≤ l.length) : α :=
  (bubbleSort proj ((l.drop (5 * j)).take 5))[2]'(by
    rw [bubbleSort_length, List.length_take, List.length_drop]
    omega)

/-- The first `t` group medians of `l`, in order. -/
def medians (proj : α → β) (l : List α) (g : Nat) (hg : 5 * g ≤ l.length) :
    (t : Nat) → t ≤ g → List α
  | 0, _ => []
  | t + 1, ht =>
      medians proj l g hg t (Nat.le_of_lt (Nat.lt_of_succ_le ht)) ++
        [medianOf proj l t (by omega)]

theorem medians_succ (proj : α → β) (l : List α) (g : Nat) (hg : 5 * g ≤ l.length)
    (t : Nat) (ht : t + 1 ≤ g) :
    medians proj l g hg (t + 1) ht =
      medians proj l g hg t (Nat.le_of_lt (Nat.lt_of_succ_le ht)) ++
        [medianOf proj l t (by omega)] :=
  rfl

theorem medians_length (proj : α → β) (l : List α) (g : Nat) (hg : 5 * g ≤ l.length) :
    ∀ t (ht : t ≤ g), (medians proj l g hg t ht).length = t := by
  intro t
  induction t with
  | zero => intro ht; rfl
  | succ t ih =>
      intro ht
      rw [medians_succ, List.length_append, ih, List.length_singleton]

/-- The index-`2` element of the sorted group is `medianOf`. -/
theorem medianOf_getElem? (proj : α → β) (l : List α) (j : Nat) (h : 5 * j + 5 ≤ l.length) :
    (bubbleSort proj ((l.drop (5 * j)).take 5))[2]? = some (medianOf proj l j h) := by
  unfold medianOf
  exact List.getElem?_eq_getElem _

/-! ## `swapAt` at a distance -/

/-- Reading a swap at its left index (the two indices are distinct in every use). -/
theorem swapAt_getElem?_left (l : List α) {i j : Nat} (hij : i ≠ j) (hi : i < l.length)
    (hj : j < l.length) : (swapAt l i j)[i]? = l[j]? := by
  unfold swapAt
  rw [dite_eq_left ⟨hi, hj⟩, List.getElem?_set_ne (show j ≠ i by omega),
    List.getElem?_set_self hi, List.getElem?_eq_getElem hj]

/-- Reading a swap away from both indices. -/
theorem swapAt_getElem?_ne (l : List α) {i j k : Nat} (hi : i < l.length) (hj : j < l.length)
    (hki : k ≠ i) (hkj : k ≠ j) : (swapAt l i j)[k]? = l[k]? := by
  unfold swapAt
  rw [dite_eq_left ⟨hi, hj⟩, List.getElem?_set_ne (show j ≠ k by omega),
    List.getElem?_set_ne (show i ≠ k by omega)]

/-- A swap of two positions at or above `n` leaves the prefix of length `n` alone. -/
theorem cost_swapAt_take_of_le (l : List α) {i j n : Nat} (hi : i < l.length) (hj : j < l.length)
    (hin : n ≤ i) (hjn : n ≤ j) : (swapAt l i j).take n = l.take n := by
  apply List.ext_getElem?
  intro k
  rw [List.getElem?_take, List.getElem?_take]
  by_cases hk : k < n
  · rw [ite_eq_left hk, ite_eq_left hk]
    exact swapAt_getElem?_ne l hi hj (by omega) (by omega)
  · rw [ite_eq_right hk, ite_eq_right hk]

/-- A swap of two positions below `n` leaves the suffix from `n` alone. -/
theorem cost_swapAt_drop_of_lt (l : List α) {i j n : Nat} (hi : i < l.length) (hj : j < l.length)
    (hin : i < n) (hjn : j < n) : (swapAt l i j).drop n = l.drop n := by
  apply List.ext_getElem?
  intro k
  rw [List.getElem?_drop, List.getElem?_drop]
  exact swapAt_getElem?_ne l hi hj (by omega) (by omega)

/-! ## What one `placeMedian` does -/

/-- `placeMedian` unfolds to the swap of the sorted-group block. -/
theorem placeMedian_eq (proj : α → β) (i : Nat) (l : List α) :
    placeMedian proj i l =
      swapAt (l.take (5 * i) ++ bubbleSort proj ((l.drop (5 * i)).take 5) ++ l.drop (5 * i + 5))
        i (5 * i + 2) :=
  rfl

/-- A prefix of `5 * i` elements has length `5 * i`. -/
theorem take_five_mul_length (l : List α) (i : Nat) (h : 5 * i ≤ l.length) :
    (l.take (5 * i)).length = 5 * i := by
  rw [List.length_take]
  omega

/-- A full group of five, sorted, still has length five. -/
theorem sorted_group_length (proj : α → β) (l : List α) (i : Nat) (h : 5 * i + 5 ≤ l.length) :
    (bubbleSort proj ((l.drop (5 * i)).take 5)).length = 5 := by
  rw [bubbleSort_length, List.length_take, List.length_drop]
  omega

/-- The length of the list `placeMedian` swaps in. -/
theorem placeMedian_aux_length (proj : α → β) {i : Nat} {l : List α}
    (h : 5 * i + 5 ≤ l.length) :
    (l.take (5 * i) ++ bubbleSort proj ((l.drop (5 * i)).take 5) ++ l.drop (5 * i + 5)).length
      = l.length := by
  rw [List.length_append, List.length_append, take_five_mul_length l i (by omega),
    sorted_group_length proj l i h, List.length_drop]
  omega

/-- `placeMedian` leaves positions below `i` alone. -/
theorem placeMedian_take (proj : α → β) (i : Nat) (l : List α) (h : 5 * i + 5 ≤ l.length) :
    (placeMedian proj i l).take i = l.take i := by
  have hlen := placeMedian_aux_length proj (i := i) (l := l) h
  have hi : i < (l.take (5 * i) ++ bubbleSort proj ((l.drop (5 * i)).take 5)
      ++ l.drop (5 * i + 5)).length := by rw [hlen]; omega
  have hj : 5 * i + 2 < (l.take (5 * i) ++ bubbleSort proj ((l.drop (5 * i)).take 5)
      ++ l.drop (5 * i + 5)).length := by rw [hlen]; omega
  have hswap : (placeMedian proj i l).take i =
      (swapAt (l.take (5 * i) ++ bubbleSort proj ((l.drop (5 * i)).take 5)
        ++ l.drop (5 * i + 5)) i (5 * i + 2)).take i := by rw [placeMedian_eq]
  rw [hswap, cost_swapAt_take_of_le _ hi hj (Nat.le_refl i) (by omega),
    List.take_append_of_le_length (by rw [List.length_append, take_five_mul_length l i (by omega),
      sorted_group_length proj l i h]; omega),
    List.take_append_of_le_length (by rw [take_five_mul_length l i (by omega)]; omega),
    List.take_take, Nat.min_eq_left (by omega)]

/-- `placeMedian` leaves the suffix from `5 * i + 5` alone. -/
theorem placeMedian_drop (proj : α → β) (i : Nat) (l : List α) (h : 5 * i + 5 ≤ l.length) :
    (placeMedian proj i l).drop (5 * i + 5) = l.drop (5 * i + 5) := by
  have hlen := placeMedian_aux_length proj (i := i) (l := l) h
  have hi : i < (l.take (5 * i) ++ bubbleSort proj ((l.drop (5 * i)).take 5)
      ++ l.drop (5 * i + 5)).length := by rw [hlen]; omega
  have hj : 5 * i + 2 < (l.take (5 * i) ++ bubbleSort proj ((l.drop (5 * i)).take 5)
      ++ l.drop (5 * i + 5)).length := by rw [hlen]; omega
  have hAB : (l.take (5 * i) ++ bubbleSort proj ((l.drop (5 * i)).take 5)).length = 5 * i + 5 := by
    rw [List.length_append, take_five_mul_length l i (by omega), sorted_group_length proj l i h]
  have hswap : (placeMedian proj i l).drop (5 * i + 5) =
      (swapAt (l.take (5 * i) ++ bubbleSort proj ((l.drop (5 * i)).take 5)
        ++ l.drop (5 * i + 5)) i (5 * i + 2)).drop (5 * i + 5) := by rw [placeMedian_eq]
  rw [hswap, cost_swapAt_drop_of_lt _ hi hj (by omega) (by omega),
    List.drop_append_of_le_length (by omega), List.drop_eq_nil_of_le (by omega)]
  rfl

/-- The value `placeMedian i` writes at index `i` is the median of group `i`. -/
theorem placeMedian_getElem_self (proj : α → β) (i : Nat) (l : List α)
    (h : 5 * i + 5 ≤ l.length) :
    (placeMedian proj i l)[i]? = (bubbleSort proj ((l.drop (5 * i)).take 5))[2]? := by
  have hlen := placeMedian_aux_length proj (i := i) (l := l) h
  have hi : i < (l.take (5 * i) ++ bubbleSort proj ((l.drop (5 * i)).take 5)
      ++ l.drop (5 * i + 5)).length := by rw [hlen]; omega
  have hj : 5 * i + 2 < (l.take (5 * i) ++ bubbleSort proj ((l.drop (5 * i)).take 5)
      ++ l.drop (5 * i + 5)).length := by rw [hlen]; omega
  have hAB : (l.take (5 * i) ++ bubbleSort proj ((l.drop (5 * i)).take 5)).length = 5 * i + 5 := by
    rw [List.length_append, take_five_mul_length l i (by omega), sorted_group_length proj l i h]
  have hA : (l.take (5 * i)).length = 5 * i := take_five_mul_length l i (by omega)
  have hswap : (placeMedian proj i l)[i]? =
      (swapAt (l.take (5 * i) ++ bubbleSort proj ((l.drop (5 * i)).take 5)
        ++ l.drop (5 * i + 5)) i (5 * i + 2))[i]? := by rw [placeMedian_eq]
  rw [hswap, swapAt_getElem?_left _ (by omega) hi hj,
    List.getElem?_append_left (by omega), List.getElem?_append_right (by omega), hA,
    show 5 * i + 2 - 5 * i = 2 by omega]

/-- The model's `groupPass` unfolds one pass. -/
theorem groupPass_succ_eq (proj : α → β) (i : Nat) (l : List α) :
    groupPass proj (i + 1) l = placeMedian proj i (groupPass proj i l) :=
  rfl

/-- After `t` passes the first `t` slots hold the group medians, and the suffix from
`5 * t` is untouched. -/
theorem groupPass_take_drop (proj : α → β) (l : List α) (g : Nat) (hg : 5 * g ≤ l.length) :
    ∀ t (ht : t ≤ g),
      (groupPass proj t l).take t = medians proj l g hg t ht ∧
      (groupPass proj t l).drop (5 * t) = l.drop (5 * t) := by
  intro t
  induction t with
  | zero => intro ht; exact ⟨rfl, rfl⟩
  | succ t ih =>
      intro ht
      have ht' : t ≤ g := Nat.le_of_lt (Nat.lt_of_succ_le ht)
      obtain ⟨ih_take, ih_drop⟩ := ih ht'
      have hlt : 5 * t + 5 ≤ (groupPass proj t l).length := by
        rw [(groupPass_perm proj t l).length_eq]
        omega
      refine ⟨?_, ?_⟩
      · rw [groupPass_succ_eq, List.take_add_one,
          placeMedian_take proj t (groupPass proj t l) hlt, ih_take]
        have hget : (placeMedian proj t (groupPass proj t l))[t]? =
            some (medianOf proj l t (by omega)) := by
          rw [placeMedian_getElem_self proj t (groupPass proj t l) hlt, ih_drop]
          exact medianOf_getElem? proj l t (by omega)
        rw [hget]
        rfl
      · rw [groupPass_succ_eq, show 5 * (t + 1) = 5 * t + 5 by omega,
          placeMedian_drop proj t (groupPass proj t l) hlt,
          ← List.drop_drop (i := 5) (j := 5 * t), ih_drop, List.drop_drop]

/-- The first `g` slots of the group pass are exactly the list of medians. -/
theorem groupPass_take_eq_medians (proj : α → β) (l : List α) (g : Nat)
    (hg : 5 * g ≤ l.length) :
    (groupPass proj g l).take g = medians proj l g hg g (Nat.le_refl g) :=
  (groupPass_take_drop proj l g hg g (Nat.le_refl g)).1

/-- `!(key < pv)` is `pv <= key`. -/
theorem not_blt_eq_ble (proj : α → β) (pv x : α) :
    (!(Cmp.blt (proj x) (proj pv))) = Cmp.ble (proj pv) (proj x) := by
  by_cases h : Cmp.blt (proj x) (proj pv) = true
  · rw [h]; simp [Cmp.not_ble_of_blt h]
  · have h' : Cmp.blt (proj x) (proj pv) = false := by
      cases hb : Cmp.blt (proj x) (proj pv) with
      | false => rfl
      | true => exact absurd hb h
    rw [h']; simp [Cmp.ble_of_not_blt h']

/-- `key < pv` and `pv <= key` split a list. -/
theorem countP_blt_add_ble (proj : α → β) (l : List α) (pv : α) :
    l.countP (fun x => Cmp.blt (proj x) (proj pv)) +
      l.countP (fun x => Cmp.ble (proj pv) (proj x)) = l.length := by
  rw [countP_congr (fun x => (not_blt_eq_ble proj pv x).symm) l]
  exact countP_add_countP_not (fun x => Cmp.blt (proj x) (proj pv)) l

/-- `key <= pv` splits into `key < pv` and `key = pv`. -/
theorem countP_ble_eq_blt_add_beq (proj : α → β) (l : List α) (pv : α) :
    l.countP (fun x => Cmp.ble (proj x) (proj pv)) =
      l.countP (fun x => Cmp.blt (proj x) (proj pv)) +
        l.countP (fun x => Cmp.beq (proj x) (proj pv)) := by
  rw [countP_congr (fun x => Cmp.ble_eq_blt_or_beq (proj x) (proj pv)) l]
  exact countP_or (fun x h => Cmp.not_blt_and_beq (proj x) (proj pv) h) l

/-- Elements strictly below a key are not equal to it. -/
theorem not_beq_of_blt {a b : β} (h : Cmp.blt a b = true) : Cmp.beq a b = false := by
  cases hb : Cmp.beq a b with
  | false => rfl
  | true => exact absurd ⟨h, hb⟩ (Cmp.not_blt_and_beq a b)

/-! ## Three elements per median

A sorted group of five has its index-`2` element as median, so if that median is
`<= t` then three of the group's elements are `<= t` (the median and the two below
it), and symmetrically if it is `>= t` then three are `>= t`. Summing this over the
groups gives the median-of-medians count.

`countP_take_le` is the (constructive) fact that a prefix never counts more
elements than the whole list. -/

/-- A `countP` over a prefix is at most the `countP` over the whole list. -/
theorem countP_take_le {γ : Type w} (p : γ → Bool) (l : List γ) (m : Nat) :
    (l.take m).countP p ≤ l.countP p := by
  have h : (l.take m).countP p + (l.drop m).countP p = l.countP p := by
    rw [← List.countP_append, List.take_append_drop]
  omega

/-- A list of length five is five elements. -/
theorem length_five_iff {G : List α} (h : G.length = 5) :
    ∃ a b c d e, G = [a, b, c, d, e] := by
  cases G with
  | nil => simp at h
  | cons a G1 =>
    cases G1 with
    | nil => simp at h
    | cons b G2 =>
      cases G2 with
      | nil => simp at h
      | cons c G3 =>
        cases G3 with
        | nil => simp at h
        | cons d G4 =>
          cases G4 with
          | nil => simp at h
          | cons e G5 =>
            cases G5 with
            | nil => exact ⟨a, b, c, d, e, rfl⟩
            | cons f G6 => simp at h

/-- A singleton `countP`. -/
theorem countP_singleton_of_pos {P : α → Bool} {x : α} (h : P x = true) :
    [x].countP P = 1 := by
  rw [List.countP_cons_of_pos (p := P) h, List.countP_nil]

theorem countP_singleton_of_neg {P : α → Bool} {x : α} (h : P x = false) :
    [x].countP P = 0 := by
  rw [List.countP_cons_of_neg (p := P) (by rw [h]; exact Bool.false_ne_true), List.countP_nil]

/-- In a sorted group of five, if the index-`2` element is `<= t` then three
elements of the group are `<= t`. -/
theorem sorted_five_count_le (proj : α → β) {G : List α} {c t : α}
    (hs : Sorted (KeyLe proj) G) (hGl : G.length = 5) (hc : G[2]? = some c)
    (hct : Cmp.ble (proj c) (proj t) = true) :
    3 ≤ G.countP (fun x => Cmp.ble (proj x) (proj t)) := by
  obtain ⟨a, b, c0, d, e, rfl⟩ := length_five_iff hGl
  have hc0 : c0 = c := by simpa using hc
  have hct0 : Cmp.ble (proj c0) (proj t) = true := by rw [← hc0] at hct; exact hct
  have hab : Cmp.ble (proj a) (proj b) = true :=
    List.rel_of_pairwise_cons hs (show b ∈ [b, c0, d, e] by simp)
  have hbc : Cmp.ble (proj b) (proj c0) = true :=
    List.rel_of_pairwise_cons (List.Pairwise.of_cons hs) (show c0 ∈ [c0, d, e] by simp)
  have hat : Cmp.ble (proj a) (proj t) = true := Cmp.ble_trans hab (Cmp.ble_trans hbc hct0)
  have hbt : Cmp.ble (proj b) (proj t) = true := Cmp.ble_trans hbc hct0
  rw [show ([a, b, c0, d, e] : List α) = [a, b, c0] ++ [d, e] by rfl, List.countP_append,
    List.countP_cons_of_pos (p := fun x => Cmp.ble (proj x) (proj t)) hat,
    List.countP_cons_of_pos (p := fun x => Cmp.ble (proj x) (proj t)) hbt,
    List.countP_cons_of_pos (p := fun x => Cmp.ble (proj x) (proj t)) hct0]
  omega

/-- In a sorted group of five, if the index-`2` element is `>= t` then three
elements of the group are `>= t`. -/
theorem sorted_five_count_ge (proj : α → β) {G : List α} {c t : α}
    (hs : Sorted (KeyLe proj) G) (hGl : G.length = 5) (hc : G[2]? = some c)
    (htc : Cmp.ble (proj t) (proj c) = true) :
    3 ≤ G.countP (fun x => Cmp.ble (proj t) (proj x)) := by
  obtain ⟨a, b, c0, d, e, rfl⟩ := length_five_iff hGl
  have hc0 : c0 = c := by simpa using hc
  have htc0 : Cmp.ble (proj t) (proj c0) = true := by rw [← hc0] at htc; exact htc
  have hcd : Cmp.ble (proj c0) (proj d) = true :=
    List.rel_of_pairwise_cons (List.Pairwise.of_cons (List.Pairwise.of_cons hs))
      (show d ∈ [d, e] by simp)
  have hde : Cmp.ble (proj d) (proj e) = true :=
    List.rel_of_pairwise_cons (List.Pairwise.of_cons (List.Pairwise.of_cons
      (List.Pairwise.of_cons hs))) (show e ∈ [e] by simp)
  have htd : Cmp.ble (proj t) (proj d) = true := Cmp.ble_trans htc0 hcd
  have hte : Cmp.ble (proj t) (proj e) = true := Cmp.ble_trans htc0 (Cmp.ble_trans hcd hde)
  rw [show ([a, b, c0, d, e] : List α) = [a, b] ++ [c0, d, e] by rfl, List.countP_append,
    List.countP_cons_of_pos (p := fun x => Cmp.ble (proj t) (proj x)) htc0,
    List.countP_cons_of_pos (p := fun x => Cmp.ble (proj t) (proj x)) htd,
    List.countP_cons_of_pos (p := fun x => Cmp.ble (proj t) (proj x)) hte]
  omega

/-- `l.take (5 * t + 5)` is the first `t` groups followed by group `t`. -/
theorem take_add_groups (l : List α) (t : Nat) (h : 5 * t ≤ l.length) :
    l.take (5 * t + 5) = l.take (5 * t) ++ (l.drop (5 * t)).take 5 := by
  have hlen : (l.take (5 * t)).length = 5 * t := take_five_mul_length l t h
  apply List.ext_getElem?
  intro k
  by_cases hk : k < 5 * t
  · rw [List.getElem?_append_left (by rw [hlen]; exact hk),
      List.getElem?_take_of_lt (by omega), List.getElem?_take_of_lt hk]
  · by_cases hk5 : k < 5 * t + 5
    · rw [List.getElem?_append_right (by rw [hlen]; omega), hlen]
      simp only [List.getElem?_take]
      rw [ite_eq_left (by omega : k < 5 * t + 5), ite_eq_left (by omega : k - 5 * t < 5),
        List.getElem?_drop]
      congr 1
      omega
    · rw [List.getElem?_eq_none_iff.mpr (by rw [List.length_take]; omega),
        List.getElem?_append_right (by rw [hlen]; omega), hlen]
      simp only [List.getElem?_take]
      rw [ite_eq_right (by omega : ¬ k - 5 * t < 5)]

/-- A group index below `g` has its full five slots in range. -/
theorem five_mul_add_le {j g : Nat} {l : List α} (hj : j < g) (hg : 5 * g ≤ l.length) :
    5 * j + 5 ≤ l.length := by
  omega

/-- The counting heart of the median-of-medians argument: three times the number of
medians with `P` true is at most the number of elements of `l.take (5 * t)` with `P`
true. -/
theorem three_mul_medians_count (proj : α → β) (l : List α) (g : Nat) (hg : 5 * g ≤ l.length)
    (P : α → Bool)
    (hgroup : ∀ j (hj : j < g), P (medianOf proj l j (five_mul_add_le hj hg)) = true →
        3 ≤ ((l.drop (5 * j)).take 5).countP P) :
    ∀ t (ht : t ≤ g), 3 * ((medians proj l g hg t ht).countP P) ≤ (l.take (5 * t)).countP P := by
  intro t
  induction t with
  | zero => intro ht; simp [medians]
  | succ t ih =>
      intro ht
      have ht' : t ≤ g := Nat.le_of_lt (Nat.lt_of_succ_le ht)
      have htg : t < g := Nat.lt_of_succ_le ht
      have iht := ih ht'
      have htake := take_add_groups l t (by omega)
      cases hb : P (medianOf proj l t (five_mul_add_le htg hg)) with
      | true =>
          have h3 := hgroup t htg hb
          rw [medians_succ, List.countP_append,
            show 5 * (t + 1) = 5 * t + 5 by omega, htake, List.countP_append,
            countP_singleton_of_pos (P := P) hb]
          omega
      | false =>
          rw [medians_succ, List.countP_append,
            show 5 * (t + 1) = 5 * t + 5 by omega, htake, List.countP_append,
            countP_singleton_of_neg (P := P) hb]
          omega

/-- Three elements per median, `<=` direction. -/
theorem three_mul_medians_count_le (proj : α → β) (l : List α) (g : Nat) (hg : 5 * g ≤ l.length)
    (t : α) :
    3 * ((medians proj l g hg g (Nat.le_refl g)).countP
        (fun x => Cmp.ble (proj x) (proj t))) ≤
      l.countP (fun x => Cmp.ble (proj x) (proj t)) := by
  refine Nat.le_trans (three_mul_medians_count proj l g hg _ ?_ g (Nat.le_refl g))
    (countP_take_le _ l (5 * g))
  intro j hj hP
  have hlt : 5 * j + 5 ≤ l.length := five_mul_add_le hj hg
  have h3 := sorted_five_count_le proj (bubbleSort_sorted proj ((l.drop (5 * j)).take 5))
    (sorted_group_length proj l j hlt) (medianOf_getElem? proj l j hlt) hP
  rwa [countP_eq_of_perm (bubbleSort_perm proj ((l.drop (5 * j)).take 5))] at h3

/-- Three elements per median, `>=` direction. -/
theorem three_mul_medians_count_ge (proj : α → β) (l : List α) (g : Nat) (hg : 5 * g ≤ l.length)
    (t : α) :
    3 * ((medians proj l g hg g (Nat.le_refl g)).countP
        (fun x => Cmp.ble (proj t) (proj x))) ≤
      l.countP (fun x => Cmp.ble (proj t) (proj x)) := by
  refine Nat.le_trans (three_mul_medians_count proj l g hg _ ?_ g (Nat.le_refl g))
    (countP_take_le _ l (5 * g))
  intro j hj hP
  have hlt : 5 * j + 5 ≤ l.length := five_mul_add_le hj hg
  have h3 := sorted_five_count_ge proj (bubbleSort_sorted proj ((l.drop (5 * j)).take 5))
    (sorted_group_length proj l j hlt) (medianOf_getElem? proj l j hlt) hP
  rwa [countP_eq_of_perm (bubbleSort_perm proj ((l.drop (5 * j)).take 5))] at h3

/-! ## The two recursive sides are at most `7n/10 + c`

The rank of the pivot in the first `g` slots combines with the three-elements-per-
median counts to bound both sides of the partition that the algorithm recurses
into. The generic lemma takes the two count lower bounds as hypotheses; the
median-of-medians lemma derives them. -/

/-- The two recursive sides of the partition, given lower bounds on the number of
elements `<= pv` (which bounds the `> pv` side) and `>= pv` (which bounds the
`< pv` side). -/
theorem partition_lengths_le_of_counts (proj : α → β) {l l₁ mm l₂ : List α} {pv : α}
    {g k₁ k₂ : Nat} (hl₁ : l₁.Perm l) (hmm : mm.Perm (l₁.take g))
    (hl₂ : l₂ = mm ++ l₁.drop g)
    (hle : k₁ ≤ l₂.countP (fun x => Cmp.ble (proj x) (proj pv)))
    (hge : k₂ ≤ l₂.countP (fun x => Cmp.ble (proj pv) (proj x))) :
    (partition (fun x => Cmp.blt (proj x) (proj pv)) l₂).1.length ≤ l.length - k₂ ∧
      (partition (fun x => Cmp.beq (proj x) (proj pv))
          (partition (fun x => Cmp.blt (proj x) (proj pv)) l₂).2).2.length
        ≤ l.length - k₁ := by
  have hl₂perm : l₂.Perm l₁ := by
    rw [hl₂]
    exact (List.Perm.append_right _ hmm).trans (List.Perm.of_eq (List.take_append_drop g l₁))
  have hl₂len : l₂.length = l.length := by
    rw [hl₂perm.length_eq, hl₁.length_eq]
  constructor
  · rw [partition_fst_length]
    have hcomp := countP_blt_add_ble proj l₂ pv
    rw [hl₂len] at hcomp
    omega
  · have hbeq : l₂.countP (fun x => Cmp.beq (proj x) (proj pv)) =
        (partition (fun x => Cmp.blt (proj x) (proj pv)) l₂).2.countP
          (fun x => Cmp.beq (proj x) (proj pv)) := by
      have hsplit : l₂.countP (fun x => Cmp.beq (proj x) (proj pv)) =
          (partition (fun x => Cmp.blt (proj x) (proj pv)) l₂).1.countP
            (fun x => Cmp.beq (proj x) (proj pv)) +
          (partition (fun x => Cmp.blt (proj x) (proj pv)) l₂).2.countP
            (fun x => Cmp.beq (proj x) (proj pv)) := by
        rw [← countP_eq_of_perm (partition_perm (fun x => Cmp.blt (proj x) (proj pv)) l₂),
          List.countP_append]
      have hzero : (partition (fun x => Cmp.blt (proj x) (proj pv)) l₂).1.countP
          (fun x => Cmp.beq (proj x) (proj pv)) = 0 :=
        countP_eq_zero_of_all (fun x hx => not_beq_of_blt
          (partition_fst_all (p := fun x => Cmp.blt (proj x) (proj pv)) (l := l₂) x hx))
      omega
    have hcount : l₂.countP (fun x => Cmp.ble (proj x) (proj pv)) =
        (partition (fun x => Cmp.blt (proj x) (proj pv)) l₂).1.length +
          (partition (fun x => Cmp.beq (proj x) (proj pv))
            (partition (fun x => Cmp.blt (proj x) (proj pv)) l₂).2).1.length := by
      rw [countP_ble_eq_blt_add_beq, ← partition_fst_length
          (fun x => Cmp.blt (proj x) (proj pv)) l₂, hbeq,
        ← partition_fst_length (fun x => Cmp.beq (proj x) (proj pv))
          (partition (fun x => Cmp.blt (proj x) (proj pv)) l₂).2]
    have hsum := partition_lengths_sum (fun x => Cmp.blt (proj x) (proj pv))
      (fun x => Cmp.beq (proj x) (proj pv)) l₂
    omega

/-- The median-of-medians rank bound: the two sides are at most
`n - 3 * (g - g/2)` and `n - 3 * (g/2 + 1)`. -/
theorem partition_lengths_le_of_medians (proj : α → β) {l l₁ mm l₂ : List α} {pv : α} {g : Nat}
    (hl₁ : l₁.Perm l) (hmm : mm.Perm (l₁.take g)) (hl₂ : l₂ = mm ++ l₁.drop g)
    (hg5 : 5 * g ≤ l.length) (hgg : 1 ≤ g)
    (hmed : l₁.take g = medians proj l g hg5 g (Nat.le_refl g))
    (hrank : IsKthSmallest proj (l₁.take g) (g / 2) pv) :
    (partition (fun x => Cmp.blt (proj x) (proj pv)) l₂).1.length ≤ l.length - 3 * (g - g / 2) ∧
      (partition (fun x => Cmp.beq (proj x) (proj pv))
          (partition (fun x => Cmp.blt (proj x) (proj pv)) l₂).2).2.length
        ≤ l.length - 3 * (g / 2 + 1) := by
  have hl₂perm : l₂.Perm l₁ := by
    rw [hl₂]
    exact (List.Perm.append_right _ hmm).trans (List.Perm.of_eq (List.take_append_drop g l₁))
  have htake : (l₁.take g).length = g := by rw [hmed, medians_length]
  have hle : 3 * (g / 2 + 1) ≤ l₂.countP (fun x => Cmp.ble (proj x) (proj pv)) := by
    have hr := hrank.2
    unfold uptoCount at hr
    have h1 : g / 2 + 1 ≤ (l₁.take g).countP (fun x => Cmp.ble (proj x) (proj pv)) := hr
    have h2 : (l₁.take g).countP (fun x => Cmp.ble (proj x) (proj pv)) =
        (medians proj l g hg5 g (Nat.le_refl g)).countP
          (fun x => Cmp.ble (proj x) (proj pv)) := by rw [hmed]
    have h3 := three_mul_medians_count_le proj l g hg5 pv
    have h4 : l.countP (fun x => Cmp.ble (proj x) (proj pv)) =
        l₂.countP (fun x => Cmp.ble (proj x) (proj pv)) :=
      (countP_eq_of_perm (hl₂perm.trans hl₁)).symm
    omega
  have hge : 3 * (g - g / 2) ≤ l₂.countP (fun x => Cmp.ble (proj pv) (proj x)) := by
    have hcomp := countP_blt_add_ble proj (l₁.take g) pv
    rw [htake] at hcomp
    have hbl := hrank.1
    unfold belowCount at hbl
    have h1 : g - g / 2 ≤ (l₁.take g).countP (fun x => Cmp.ble (proj pv) (proj x)) := by omega
    have h2 : (l₁.take g).countP (fun x => Cmp.ble (proj pv) (proj x)) =
        (medians proj l g hg5 g (Nat.le_refl g)).countP
          (fun x => Cmp.ble (proj pv) (proj x)) := by rw [hmed]
    have h3 := three_mul_medians_count_ge proj l g hg5 pv
    have h4 : l.countP (fun x => Cmp.ble (proj pv) (proj x)) =
        l₂.countP (fun x => Cmp.ble (proj pv) (proj x)) :=
      (countP_eq_of_perm (hl₂perm.trans hl₁)).symm
    omega
  exact partition_lengths_le_of_counts proj hl₁ hmm hl₂ hle hge

/-! ## The costed selection

The counting transcription mirrors the model's recursion: the group pass, the
recursive median selection, the two partition passes and the recursive selection
of one side. Only the costs differ from `bfprtAux`.

The `std::partition` charge is the worst case described in the header: exactly
`l.length` predicate evaluations (one comparison each) and at most one swap
(`3` moves) per element, plus one move per predicate call because the C++ lambda
takes its argument by value; we charge `Cost.cmpN l.length + Cost.mvN (4 * l.length)`
for each of the two passes. The rank tests that choose the recursive side are
index arithmetic; one key comparison is charged for them. -/

/-- `bfprtAux` carrying its cost. -/
def bfprtAuxC (proj : α → β) : Nat → Nat → List α → List α × Cost
  | 0, _, l => (l, 0)
  | fuel + 1, k, l =>
    if l.length < 5 then
      let r := bubbleSortC proj l
      (r.1, r.2)
    else
      let g := l.length / 5
      let lr := groupPassC proj g l
      let mmr := bfprtAuxC proj fuel (g / 2) (lr.1.take g)
      let l₂ := mmr.1 ++ lr.1.drop g
      let base := lr.2 + mmr.2
      match l₂[g / 2]? with
      | none => (lr.1, base)
      | some pv =>
        let p₁ := partition (fun x => Cmp.blt (proj x) (proj pv)) l₂
        let p₂ := partition (fun x => Cmp.beq (proj x) (proj pv)) p₁.2
        let pc := Cost.cmp1 + (Cost.cmpN l₂.length + Cost.mvN (4 * l₂.length)) +
          (Cost.cmpN l₂.length + Cost.mvN (4 * l₂.length))
        if k < p₁.1.length then
          let rr := bfprtAuxC proj fuel k p₁.1
          (rr.1 ++ (p₂.1 ++ p₂.2), base + pc + rr.2)
        else if p₁.1.length + p₂.1.length ≤ k then
          let rr := bfprtAuxC proj fuel (k - p₁.1.length - p₂.1.length) p₂.2
          ((p₁.1 ++ p₂.1) ++ rr.1, base + pc + rr.2)
        else ((p₁.1 ++ p₂.1) ++ p₂.2, base + pc)

theorem bfprtAuxC_zero (proj : α → β) (k : Nat) (l : List α) :
    bfprtAuxC proj 0 k l = (l, 0) :=
  rfl

/-- Agreement with the verified model: the counting transcription computes exactly
the same list. The cost component plays no role in `.1`. -/
theorem bfprtAuxC_fst (proj : α → β) (fuel : Nat) :
    ∀ k (l : List α), l.length ≤ fuel → (bfprtAuxC proj fuel k l).1 = bfprtAux proj fuel k l := by
  induction fuel with
  | zero => intro k l _; rfl
  | succ fuel ih =>
      intro k l hl
      rw [bfprtAuxC, bfprtAux]
      by_cases hsmall : l.length < 5
      · simp only [hsmall, ite_true]
        rw [bubbleSortC_fst]
      · simp only [hsmall, ite_false]
        rw [groupPassC_fst]
        generalize hg : l.length / 5 = g
        generalize hl₁ : groupPass proj g l = l₁
        have hglen : g ≤ l.length := by rw [← hg]; exact Nat.div_le_self _ _
        have hl₁len : l₁.length = l.length := by
          rw [← hl₁]; exact (groupPass_perm proj g l).length_eq
        have htake : (l₁.take g).length = g := by
          rw [List.length_take, hl₁len, Nat.min_eq_left hglen]
        have hgfuel : (l₁.take g).length ≤ fuel := by
          rw [htake]
          omega
        rw [ih (g / 2) (l₁.take g) hgfuel]
        generalize hmm : bfprtAux proj fuel (g / 2) (l₁.take g) = mm
        generalize hl₂ : mm ++ l₁.drop g = l₂
        cases hsome : l₂[g / 2]? with
        | none => rfl
        | some pv =>
            dsimp only
            generalize hA : (partition (fun x => Cmp.blt (proj x) (proj pv)) l₂).1 = A
            generalize hR : (partition (fun x => Cmp.blt (proj x) (proj pv)) l₂).2 = R
            generalize hB : (partition (fun x => Cmp.beq (proj x) (proj pv)) R).1 = B
            generalize hC : (partition (fun x => Cmp.beq (proj x) (proj pv)) R).2 = C
            have hl₂len : l₂.length = l.length := by
              rw [← hl₂, List.length_append, ← hmm,
                (bfprtAux_perm proj fuel (g / 2) (l₁.take g) hgfuel).length_eq, htake,
                List.length_drop, hl₁len]
              omega
            have hsum : A.length + B.length + C.length = l₂.length := by
              have h := partition_lengths_sum (fun x => Cmp.blt (proj x) (proj pv))
                (fun x => Cmp.beq (proj x) (proj pv)) l₂
              rw [hA, hR, hB, hC] at h
              exact h
            have hpvmem : pv ∈ l₂ := List.mem_iff_getElem?.mpr ⟨g / 2, hsome⟩
            have hpvR : pv ∈ R := by
              rw [← hR]
              exact partition_mem_snd hpvmem (Cmp.blt_irrefl (proj pv))
            have hQpv : Cmp.beq (proj pv) (proj pv) = true :=
              Cmp.beq_iff.mpr ⟨Cmp.ble_refl _, Cmp.ble_refl _⟩
            have hpvB : pv ∈ B := by
              rw [← hB]
              exact partition_mem_fst hpvR hQpv
            have hBpos : 0 < B.length := List.length_pos_of_mem hpvB
            have hAfuel : A.length ≤ fuel := by omega
            have hCfuel : C.length ≤ fuel := by omega
            by_cases h1 : k < A.length
            · simp only [h1, ite_true]
              rw [ih k A hAfuel]
            · simp only [h1, ite_false]
              by_cases h2 : A.length + B.length ≤ k
              · simp only [h2, ite_true]
                rw [ih _ C hCfuel]
              · simp only [h2, ite_false]
/-! ## Where the linear bound would come from

The median-of-medians argument wants, for the pivot `pv`, at least `3 * (g / 2 + 1)`
elements of the range with key `<= pv` and at least `3 * (g - g / 2)` with key
`>= pv`, coming from the medians of the groups. That "three elements per median"
step is the only part of the linear proof that needs the group pass to place the
*original* group medians in `[0, g)`.

The two counting lemmas below are the part that is true independently of any group
structure: the first `g` slots of the group pass are elements of the range, and the
pivot is their rank-`g/2` element, so at least `g / 2 + 1` elements are `<=` it and
at least `g - g / 2` are `>=` it. Those bounds already give `O(n^2)`. -/


/-- The two recursive sides of the partition are bounded by the rank of the pivot:
the pivot is the rank-`g/2` element of the first `g` slots, so at least `g/2 + 1`
elements of the range are `<=` it and at least `g - g/2` are `>=` it. -/
theorem partition_lengths_le_of_rank (proj : α → β) {l l₁ mm l₂ : List α} {pv : α} {g : Nat}
    (hl₁ : l₁.Perm l) (hmm : mm.Perm (l₁.take g)) (hl₂ : l₂ = mm ++ l₁.drop g)
    (htake : (l₁.take g).length = g) (hgg : 1 ≤ g)
    (hrank : IsKthSmallest proj (l₁.take g) (g / 2) pv) :
    (partition (fun x => Cmp.blt (proj x) (proj pv)) l₂).1.length ≤ l.length - (g - g / 2) ∧
      (partition (fun x => Cmp.beq (proj x) (proj pv))
          (partition (fun x => Cmp.blt (proj x) (proj pv)) l₂).2).2.length
        ≤ l.length - (g / 2 + 1) := by
  have hl₂perm : l₂.Perm l₁ := by
    rw [hl₂]
    exact (List.Perm.append_right _ hmm).trans (List.Perm.of_eq (List.take_append_drop g l₁))
  have hl₂len : l₂.length = l.length := by
    rw [hl₂perm.length_eq, hl₁.length_eq]
  have htake_le : ∀ Q : α → Bool,
      (l₁.take g).countP Q ≤ l₂.countP Q := by
    intro Q
    exact Nat.le_trans (countP_take_le Q l₁ g)
      (by rw [← countP_eq_of_perm hl₂perm]; exact Nat.le_refl _)
  constructor
  · rw [partition_fst_length]
    have hcomp := countP_blt_add_ble proj l₂ pv
    rw [hl₂len] at hcomp
    have hge : g - g / 2 ≤ l₂.countP (fun x => Cmp.ble (proj pv) (proj x)) := by
      have hc := countP_blt_add_ble proj (l₁.take g) pv
      rw [htake] at hc
      have h₁ : g - g / 2 ≤ (l₁.take g).countP (fun x => Cmp.ble (proj pv) (proj x)) := by
        have hbl := hrank.1
        unfold belowCount at hbl
        omega
      exact Nat.le_trans h₁ (htake_le _)
    omega
  · have hbeq : l₂.countP (fun x => Cmp.beq (proj x) (proj pv)) =
        (partition (fun x => Cmp.blt (proj x) (proj pv)) l₂).2.countP
          (fun x => Cmp.beq (proj x) (proj pv)) := by
      have hsplit : l₂.countP (fun x => Cmp.beq (proj x) (proj pv)) =
          (partition (fun x => Cmp.blt (proj x) (proj pv)) l₂).1.countP
            (fun x => Cmp.beq (proj x) (proj pv)) +
          (partition (fun x => Cmp.blt (proj x) (proj pv)) l₂).2.countP
            (fun x => Cmp.beq (proj x) (proj pv)) := by
        rw [← countP_eq_of_perm (partition_perm (fun x => Cmp.blt (proj x) (proj pv)) l₂),
          List.countP_append]
      have hzero : (partition (fun x => Cmp.blt (proj x) (proj pv)) l₂).1.countP
          (fun x => Cmp.beq (proj x) (proj pv)) = 0 :=
        countP_eq_zero_of_all (fun x hx => not_beq_of_blt
          (partition_fst_all (p := fun x => Cmp.blt (proj x) (proj pv)) (l := l₂) x hx))
      omega
    have hcount : l₂.countP (fun x => Cmp.ble (proj x) (proj pv)) =
        (partition (fun x => Cmp.blt (proj x) (proj pv)) l₂).1.length +
          (partition (fun x => Cmp.beq (proj x) (proj pv))
            (partition (fun x => Cmp.blt (proj x) (proj pv)) l₂).2).1.length := by
      rw [countP_ble_eq_blt_add_beq, ← partition_fst_length
          (fun x => Cmp.blt (proj x) (proj pv)) l₂, hbeq,
        ← partition_fst_length (fun x => Cmp.beq (proj x) (proj pv))
          (partition (fun x => Cmp.blt (proj x) (proj pv)) l₂).2]
    have hsum := partition_lengths_sum (fun x => Cmp.blt (proj x) (proj pv))
      (fun x => Cmp.beq (proj x) (proj pv)) l₂
    have hle : g / 2 + 1 ≤ l₂.countP (fun x => Cmp.ble (proj x) (proj pv)) := by
      have h₁ : g / 2 + 1 ≤ (l₁.take g).countP (fun x => Cmp.ble (proj x) (proj pv)) := by
        have h := hrank.2
        unfold uptoCount at h
        omega
      exact Nat.le_trans h₁ (htake_le _)
    omega
/-! ## The quadratic bound

The group pass is charged `10 * g` comparisons and `33 * g` moves, the two
partitions `1 + 8 * n`, and each recursive call `100 * len^2`. The two recursive
lists have length at most `g = n / 5` and `B = n - (g - g / 2)`; since
`g^2 + B^2 <= (n/5)^2 + (9n/10)^2 <= (85/100) n^2 < n^2`, the quadratic bound
closes. (The linear bound would need `g + B < n`, which the *three elements per
median* rank lemma supplies; see the report and `partition_lengths_le_of_rank`.)

The arithmetic below is stated over `Nat` with the divisions spelled out, so that
`omega` can finish every step; the two genuinely non-linear facts are
`100 * (n/5)^2 <= 4 * n^2` (from `5 * (n/5) <= n`) and
`100 * B^2 <= 87 * n^2` (from `14 * B <= 13 * n`). -/

theorem cost_mul_five_sq (g : Nat) : (5 * g) * (5 * g) = 25 * (g * g) := by
  rw [Nat.mul_assoc 5 g (5 * g), Nat.mul_comm g (5 * g), Nat.mul_assoc 5 g g,
    ← Nat.mul_assoc 5 5 (g * g)]

theorem cost_mul_fourteen_sq (b : Nat) : (14 * b) * (14 * b) = 196 * (b * b) := by
  rw [Nat.mul_assoc 14 b (14 * b), Nat.mul_comm b (14 * b), Nat.mul_assoc 14 b b,
    ← Nat.mul_assoc 14 14 (b * b)]

theorem cost_mul_thirteen_sq (n : Nat) : (13 * n) * (13 * n) = 169 * (n * n) := by
  rw [Nat.mul_assoc 13 n (13 * n), Nat.mul_comm n (13 * n), Nat.mul_assoc 13 n n,
    ← Nat.mul_assoc 13 13 (n * n)]

theorem cost_four_25 (X : Nat) : 4 * (25 * X) = 100 * X := by rw [← Nat.mul_assoc]

theorem cost_100_196 (X : Nat) : 100 * (196 * X) = 19600 * X := by rw [← Nat.mul_assoc]

theorem cost_100_169 (X : Nat) : 100 * (169 * X) = 16900 * X := by rw [← Nat.mul_assoc]

theorem cost_196_100 (X : Nat) : 196 * (100 * X) = 19600 * X := (Nat.mul_assoc 196 100 X).symm

theorem cost_196_87 (X : Nat) : 196 * (87 * X) = 17052 * X := (Nat.mul_assoc 196 87 X).symm

/-- `n` is at most `14 * ceil(g/2)` for `g = n / 5`. -/
theorem cost_n_le_14_half (n : Nat) (hn : 5 ≤ n) :
    n ≤ 14 * ((n / 5) - (n / 5) / 2) := by
  omega

/-- Hence `B = n - ceil(g/2)` is at most `(13/14) * n`. -/
theorem cost_B_le (n : Nat) (hn : 5 ≤ n) :
    14 * (n - ((n / 5) - (n / 5) / 2)) ≤ 13 * n := by
  rw [Nat.mul_sub_left_distrib]
  have h : n ≤ 14 * ((n / 5) - (n / 5) / 2) := cost_n_le_14_half n hn
  omega

/-- `100 * (n/5)^2 <= 4 * n^2`. -/
theorem cost_g_sq (n : Nat) : 100 * ((n / 5) * (n / 5)) ≤ 4 * (n * n) := by
  have h5 : 5 * (n / 5) ≤ n := Nat.mul_div_le n 5
  have h : (5 * (n / 5)) * (5 * (n / 5)) ≤ n * n := Nat.mul_le_mul h5 h5
  rw [cost_mul_five_sq] at h
  have h2 := Nat.mul_le_mul_left 4 h
  rw [cost_four_25] at h2
  exact h2

/-- `100 * B^2 <= 87 * n^2` with `B = n - ceil(g/2)`, `g = n / 5`. -/
theorem cost_B_sq (n : Nat) (hn : 5 ≤ n) :
    100 * ((n - ((n / 5) - (n / 5) / 2)) * (n - ((n / 5) - (n / 5) / 2))) ≤ 87 * (n * n) := by
  have h := Nat.mul_le_mul (cost_B_le n hn) (cost_B_le n hn)
  rw [cost_mul_fourteen_sq, cost_mul_thirteen_sq] at h
  have h2 : 19600 * ((n - ((n / 5) - (n / 5) / 2)) * (n - ((n / 5) - (n / 5) / 2)))
      ≤ 16900 * (n * n) := by
    have h1 := Nat.mul_le_mul_left 100 h
    rwa [cost_100_196, cost_100_169] at h1
  have h3 : 19600 * ((n - ((n / 5) - (n / 5) / 2)) * (n - ((n / 5) - (n / 5) / 2)))
      ≤ 17052 * (n * n) := Nat.le_trans h2 (Nat.mul_le_mul_right _ (by decide))
  have h4 : 196 * (100 * ((n - ((n / 5) - (n / 5) / 2)) * (n - ((n / 5) - (n / 5) / 2))))
      ≤ 196 * (87 * (n * n)) := by
    rwa [← cost_196_100, ← cost_196_87] at h3
  exact Nat.le_of_mul_le_mul_left h4 (by decide)

/-- The arithmetic step of the recurrence: the work at a node of size `n` plus the
two recursive bounds fits into `100 * n^2`. -/
theorem cost_quad_arith (n : Nat) (hn : 5 ≤ n) :
    33 * (n / 5) + 100 * ((n / 5) * (n / 5)) + (1 + 8 * n) +
      100 * ((n - ((n / 5) - (n / 5) / 2)) * (n - ((n / 5) - (n / 5) / 2)))
      ≤ 100 * (n * n) := by
  have h1 := cost_g_sq n
  have h2 := cost_B_sq n hn
  have hlin : 33 * (n / 5) + (1 + 8 * n) ≤ 9 * (n * n) := by
    have hd : 33 * (n / 5) ≤ 33 * n := Nat.mul_le_mul_left 33 (Nat.div_le_self n 5)
    have h5n : 5 * n ≤ n * n := Nat.mul_le_mul_right n hn
    have h45 : 45 * n ≤ 9 * (n * n) := by
      have h := Nat.mul_le_mul_left 9 h5n
      rwa [show 9 * (5 * n) = 45 * n by rw [← Nat.mul_assoc]] at h
    omega
  omega

/-- **Quadratic cost bound.** The counting selection spends at most `100 * n^2` in
both units. The proof uses only the rank of the pivot in the first `g` slots: at
least `g/2 + 1` elements are `<=` it and at least `g - g/2` are `>=` it, so the
recursive sides have length at most `g` and `B = n - (g - g/2)`, and
`g^2 + B^2 <= (85/100) n^2 < n^2`.

The *linear* bound would need `g + B < n`, i.e. the three-elements-per-median rank
lemma. That lemma is not available for this model: `groupPass` applies the group
operations in *decreasing* index order, so a later `placeMedian i` sorts a group
whose slots have already been overwritten. See the report and the counterexample
`groupPass` on `[5,4,3,2,1,10,9,8,7,6,15,14,13,12,11]`. -/
theorem bfprtAuxC_le_quadratic (proj : α → β) (fuel : Nat) :
    ∀ k (l : List α), l.length ≤ fuel →
      (bfprtAuxC proj fuel k l).2 ≤ Cost.const (100 * (l.length * l.length)) := by
  induction fuel with
  | zero => intro k l _; rw [bfprtAuxC_zero]; exact Cost.zero_le _
  | succ fuel ih =>
      intro k l hl
      rw [bfprtAuxC]
      by_cases hsmall : l.length < 5
      · simp only [hsmall, ite_true]
        refine Cost.le_const ?_ ?_
        · rw [bubbleSortC_cmp]
          have htri := tri_pred_le_sq l.length
          omega
        · have hm := bubbleSortC_mv_le proj l
          have htri := tri_pred_le_sq l.length
          omega
      · simp only [hsmall, ite_false]
        rw [groupPassC_fst]
        generalize hg : l.length / 5 = g
        generalize hl₁ : groupPass proj g l = l₁
        have hglen : g ≤ l.length := by rw [← hg]; exact Nat.div_le_self _ _
        have hl₁len : l₁.length = l.length := by
          rw [← hl₁]; exact (groupPass_perm proj g l).length_eq
        have htake : (l₁.take g).length = g := by
          rw [List.length_take, hl₁len, Nat.min_eq_left hglen]
        have hgfuel : (l₁.take g).length ≤ fuel := by rw [htake]; omega
        rw [bfprtAuxC_fst proj fuel (g / 2) (l₁.take g) hgfuel]
        generalize hmm : bfprtAux proj fuel (g / 2) (l₁.take g) = mm
        generalize hl₂ : mm ++ l₁.drop g = l₂
        have hl₂len : l₂.length = l.length := by
          rw [← hl₂, List.length_append, ← hmm,
            (bfprtAux_perm proj fuel (g / 2) (l₁.take g) hgfuel).length_eq, htake,
            List.length_drop, hl₁len]
          omega
        have hgrp5 : 5 * g ≤ l.length := by rw [← hg]; exact Nat.mul_div_le _ _
        have hq := cost_quad_arith l.length (by omega)
        rw [hg] at hq
        have hgc : (groupPassC proj g l).2 ≤ Cost.const (33 * g) := by
          refine Cost.le_const ?_ ?_
          · have h := groupPassC_cmp_le proj g l hgrp5; omega
          · have h := groupPassC_mv_le proj g l hgrp5; omega
        have hgc_cmp : (groupPassC proj g l).2.cmp ≤ 33 * g := by
          have h := Cost.cmp_le_of_le hgc; rwa [Cost.cmp_const] at h
        have hgc_mv : (groupPassC proj g l).2.mv ≤ 33 * g := by
          have h := Cost.mv_le_of_le hgc; rwa [Cost.mv_const] at h
        have hmc : (bfprtAuxC proj fuel (g / 2) (l₁.take g)).2 ≤ Cost.const (100 * (g * g)) := by
          have h := ih (g / 2) (l₁.take g) hgfuel
          rwa [htake] at h
        have hmc_cmp : (bfprtAuxC proj fuel (g / 2) (l₁.take g)).2.cmp ≤ 100 * (g * g) := by
          have h := Cost.cmp_le_of_le hmc; rwa [Cost.cmp_const] at h
        have hmc_mv : (bfprtAuxC proj fuel (g / 2) (l₁.take g)).2.mv ≤ 100 * (g * g) := by
          have h := Cost.mv_le_of_le hmc; rwa [Cost.mv_const] at h
        have hpc : (Cost.cmp1 + (Cost.cmpN l₂.length + Cost.mvN (4 * l₂.length)) +
            (Cost.cmpN l₂.length + Cost.mvN (4 * l₂.length))) ≤ Cost.const (1 + 8 * l.length) := by
          refine Cost.le_const ?_ ?_
          · simp only [Cost.cmp_add, Cost.cmp_cmp1, Cost.cmp_cmpN, Cost.cmp_mvN, hl₂len]
            omega
          · simp only [Cost.mv_add, Cost.mv_cmp1, Cost.mv_cmpN, Cost.mv_mvN, hl₂len]
            omega
        have hpc_cmp : (Cost.cmp1 + (Cost.cmpN l₂.length + Cost.mvN (4 * l₂.length)) +
            (Cost.cmpN l₂.length + Cost.mvN (4 * l₂.length))).cmp ≤ 1 + 8 * l.length := by
          have h := Cost.cmp_le_of_le hpc; rwa [Cost.cmp_const] at h
        have hpc_mv : (Cost.cmp1 + (Cost.cmpN l₂.length + Cost.mvN (4 * l₂.length)) +
            (Cost.cmpN l₂.length + Cost.mvN (4 * l₂.length))).mv ≤ 1 + 8 * l.length := by
          have h := Cost.mv_le_of_le hpc; rwa [Cost.mv_const] at h
        cases hsome : l₂[g / 2]? with
        | none =>
            refine Cost.le_const ?_ ?_
            · simp only [Cost.cmp_add]
              omega
            · simp only [Cost.mv_add]
              omega
        | some pv =>
            dsimp only
            generalize hA : (partition (fun x => Cmp.blt (proj x) (proj pv)) l₂).1 = A
            generalize hR : (partition (fun x => Cmp.blt (proj x) (proj pv)) l₂).2 = R
            generalize hB : (partition (fun x => Cmp.beq (proj x) (proj pv)) R).1 = B
            generalize hC : (partition (fun x => Cmp.beq (proj x) (proj pv)) R).2 = C
            have hspec := bfprtAux_spec proj fuel (g / 2) (l₁.take g) hgfuel
            have hmmperm : mm.Perm (l₁.take g) := by rw [← hmm]; exact hspec.1
            have hmm_len : mm.length = g := by rw [hmmperm.length_eq, htake]
            have hkg : g / 2 < (l₁.take g).length := by rw [htake]; omega
            obtain ⟨xs, ys, y, hdec, hxs, hrank_y⟩ := hspec.2 hkg
            have hg1 : 1 ≤ g := by omega
            have hpv_y : l₂[g / 2]? = some y := by
              have h1 : g / 2 < mm.length := by
                rw [hmm_len]
                exact Nat.div_lt_self (by omega) (by decide)
              rw [← hl₂, List.getElem?_append_left h1, ← hmm, hdec]
              rw [List.getElem?_append_right (by omega)]
              rw [hxs]
              simp
            have hpv_eq : pv = y := by
              rw [hpv_y] at hsome
              exact (Option.some.inj hsome).symm
            have hrank : IsKthSmallest proj (l₁.take g) (g / 2) pv := by
              rw [hpv_eq]
              exact isKthSmallest_of_perm hspec.1 hrank_y
            have hpart := partition_lengths_le_of_rank proj
              (l := l) (l₁ := l₁) (mm := mm) (l₂ := l₂) (pv := pv) (g := g)
              (by rw [← hl₁]; exact groupPass_perm proj g l) hmmperm (by rw [← hl₂])
              htake (by omega) hrank
            rw [hA, hR, hC] at hpart
            have hAfuel : A.length ≤ fuel := by omega
            have hCfuel : C.length ≤ fuel := by omega
            have hCB : C.length ≤ l.length - (g - g / 2) := by have h := hpart.2; omega
            have hAcost : (bfprtAuxC proj fuel k A).2 ≤
                Cost.const (100 * ((l.length - (g - g / 2)) * (l.length - (g - g / 2)))) := by
              have h := ih k A hAfuel
              have hle : A.length ≤ l.length - (g - g / 2) := hpart.1
              exact Cost.le_trans h (Cost.const_le_const
                (Nat.mul_le_mul_left 100 (Nat.mul_le_mul hle hle)))
            have hCcost : (bfprtAuxC proj fuel (k - A.length - B.length) C).2 ≤
                Cost.const (100 * ((l.length - (g - g / 2)) * (l.length - (g - g / 2)))) := by
              have h := ih (k - A.length - B.length) C hCfuel
              exact Cost.le_trans h (Cost.const_le_const
                (Nat.mul_le_mul_left 100 (Nat.mul_le_mul hCB hCB)))
            have hAcost_cmp : (bfprtAuxC proj fuel k A).2.cmp ≤
                100 * ((l.length - (g - g / 2)) * (l.length - (g - g / 2))) := by
              have h := Cost.cmp_le_of_le hAcost; rwa [Cost.cmp_const] at h
            have hAcost_mv : (bfprtAuxC proj fuel k A).2.mv ≤
                100 * ((l.length - (g - g / 2)) * (l.length - (g - g / 2))) := by
              have h := Cost.mv_le_of_le hAcost; rwa [Cost.mv_const] at h
            have hCcost_cmp : (bfprtAuxC proj fuel (k - A.length - B.length) C).2.cmp ≤
                100 * ((l.length - (g - g / 2)) * (l.length - (g - g / 2))) := by
              have h := Cost.cmp_le_of_le hCcost; rwa [Cost.cmp_const] at h
            have hCcost_mv : (bfprtAuxC proj fuel (k - A.length - B.length) C).2.mv ≤
                100 * ((l.length - (g - g / 2)) * (l.length - (g - g / 2))) := by
              have h := Cost.mv_le_of_le hCcost; rwa [Cost.mv_const] at h
            by_cases h1 : k < A.length
            · simp only [h1, ite_true]
              refine Cost.le_const ?_ ?_
              · simp only [Cost.cmp_add, Cost.cmp_cmp1, Cost.cmp_cmpN, Cost.cmp_mvN, hl₂len]
                omega
              · simp only [Cost.mv_add, Cost.mv_cmp1, Cost.mv_cmpN, Cost.mv_mvN, hl₂len]
                omega
            · simp only [h1, ite_false]
              by_cases h2 : A.length + B.length ≤ k
              · simp only [h2, ite_true]
                refine Cost.le_const ?_ ?_
                · simp only [Cost.cmp_add, Cost.cmp_cmp1, Cost.cmp_cmpN, Cost.cmp_mvN, hl₂len]
                  omega
                · simp only [Cost.mv_add, Cost.mv_cmp1, Cost.mv_cmpN, Cost.mv_mvN, hl₂len]
                  omega
              · simp only [h2, ite_false]
                refine Cost.le_const ?_ ?_
                · simp only [Cost.cmp_add, Cost.cmp_cmp1, Cost.cmp_cmpN, Cost.cmp_mvN, hl₂len]
                  omega
                · simp only [Cost.mv_add, Cost.mv_cmp1, Cost.mv_cmpN, Cost.mv_mvN, hl₂len]
                  omega

/-- Quadratic comparison bound. -/
theorem bfprtAuxC_cmp_le_quadratic (proj : α → β) (fuel k : Nat) (l : List α)
    (hl : l.length ≤ fuel) :
    (bfprtAuxC proj fuel k l).2.cmp ≤ 100 * (l.length * l.length) := by
  have h := Cost.cmp_le_of_le (bfprtAuxC_le_quadratic proj fuel k l hl)
  rwa [Cost.cmp_const] at h

/-- Quadratic move bound. -/
theorem bfprtAuxC_mv_le_quadratic (proj : α → β) (fuel k : Nat) (l : List α)
    (hl : l.length ≤ fuel) :
    (bfprtAuxC proj fuel k l).2.mv ≤ 100 * (l.length * l.length) := by
  have h := Cost.mv_le_of_le (bfprtAuxC_le_quadratic proj fuel k l hl)
  rwa [Cost.mv_const] at h

/-- The counting selection is `O(n^2)` in both units (uniform bound, constant 100). -/
theorem bfprtAuxC_bigO_quadratic (proj : α → β) (k : Nat) :
    CostBigOWith 100 List.length (fun l => (bfprtAuxC proj l.length k l).2) (fun n => n * n) :=
  fun l => bfprtAuxC_le_quadratic proj l.length k l (Nat.le_refl _)


/-! ## The medians land in `[0, g)`

A concrete check of the model's group pass (increasing order): on this list the
three group medians `3`, `8`, `13` end up at positions `0`, `1`, `2`, exactly as in
the C++ loop. -/

example : groupPass (fun n : Nat => n) 3 [5, 4, 3, 2, 1, 10, 9, 8, 7, 6, 15, 14, 13, 12, 11]
    = [3, 8, 13, 4, 5, 6, 7, 2, 9, 10, 11, 12, 1, 14, 15] := rfl

/-- The three medians the group pass places in `[0, g)`. -/
example : (bubbleSort (fun n : Nat => n) [5, 4, 3, 2, 1])[2]? = some 3 := rfl

example : (bubbleSort (fun n : Nat => n) [10, 9, 8, 7, 6])[2]? = some 8 := rfl

example : (bubbleSort (fun n : Nat => n) [15, 14, 13, 12, 11])[2]? = some 13 := rfl

/-- The arithmetic of the linear recurrence: the work at a node of size `n` plus
`400 * (g + B)` with `g = n / 5` and `B = n - 3 * (g - g / 2)` fits into `400 * n`. -/
theorem cost_linear_arith (n : Nat) (hn : 5 ≤ n) :
    33 * (n / 5) + 400 * (n / 5) + (1 + 8 * n) +
      400 * (n - 3 * ((n / 5) - (n / 5) / 2)) ≤ 400 * n := by
  omega


/-- **Linear cost bound.** The counting selection spends at most `400 * n` in both
units. The two recursive sides have length at most `g = n / 5` and
`B = n - 3 * (g - g / 2)`, whose sum is at most `(9/10) * n`. -/
theorem bfprtAuxC_le_linear (proj : α → β) (fuel : Nat) :
    ∀ k (l : List α), l.length ≤ fuel →
      (bfprtAuxC proj fuel k l).2 ≤ Cost.const (400 * l.length) := by
  induction fuel with
  | zero => intro k l _; rw [bfprtAuxC_zero]; exact Cost.zero_le _
  | succ fuel ih =>
      intro k l hl
      rw [bfprtAuxC]
      by_cases hsmall : l.length < 5
      · simp only [hsmall, ite_true]
        refine Cost.le_const ?_ ?_
        · rw [bubbleSortC_cmp]
          have htri := tri_pred_le_sq l.length
          have hsq : l.length * l.length ≤ 4 * l.length :=
            Nat.mul_le_mul_right l.length (by omega)
          omega
        · have hm := bubbleSortC_mv_le proj l
          have htri := tri_pred_le_sq l.length
          have hsq : l.length * l.length ≤ 4 * l.length :=
            Nat.mul_le_mul_right l.length (by omega)
          omega
      · simp only [hsmall, ite_false]
        rw [groupPassC_fst]
        generalize hg : l.length / 5 = g
        generalize hl₁ : groupPass proj g l = l₁
        have hglen : g ≤ l.length := by rw [← hg]; exact Nat.div_le_self _ _
        have hl₁len : l₁.length = l.length := by
          rw [← hl₁]; exact (groupPass_perm proj g l).length_eq
        have htake : (l₁.take g).length = g := by
          rw [List.length_take, hl₁len, Nat.min_eq_left hglen]
        have hgfuel : (l₁.take g).length ≤ fuel := by rw [htake]; omega
        rw [bfprtAuxC_fst proj fuel (g / 2) (l₁.take g) hgfuel]
        generalize hmm : bfprtAux proj fuel (g / 2) (l₁.take g) = mm
        generalize hl₂ : mm ++ l₁.drop g = l₂
        have hl₂len : l₂.length = l.length := by
          rw [← hl₂, List.length_append, ← hmm,
            (bfprtAux_perm proj fuel (g / 2) (l₁.take g) hgfuel).length_eq, htake,
            List.length_drop, hl₁len]
          omega
        have hgrp5 : 5 * g ≤ l.length := by rw [← hg]; exact Nat.mul_div_le _ _
        have hq := cost_linear_arith l.length (by omega)
        rw [hg] at hq
        have hgc : (groupPassC proj g l).2 ≤ Cost.const (33 * g) := by
          refine Cost.le_const ?_ ?_
          · have h := groupPassC_cmp_le proj g l hgrp5; omega
          · have h := groupPassC_mv_le proj g l hgrp5; omega
        have hgc_cmp : (groupPassC proj g l).2.cmp ≤ 33 * g := by
          have h := Cost.cmp_le_of_le hgc; rwa [Cost.cmp_const] at h
        have hgc_mv : (groupPassC proj g l).2.mv ≤ 33 * g := by
          have h := Cost.mv_le_of_le hgc; rwa [Cost.mv_const] at h
        have hmc : (bfprtAuxC proj fuel (g / 2) (l₁.take g)).2 ≤ Cost.const (400 * g) := by
          have h := ih (g / 2) (l₁.take g) hgfuel
          rwa [htake] at h
        have hmc_cmp : (bfprtAuxC proj fuel (g / 2) (l₁.take g)).2.cmp ≤ 400 * g := by
          have h := Cost.cmp_le_of_le hmc; rwa [Cost.cmp_const] at h
        have hmc_mv : (bfprtAuxC proj fuel (g / 2) (l₁.take g)).2.mv ≤ 400 * g := by
          have h := Cost.mv_le_of_le hmc; rwa [Cost.mv_const] at h
        have hpc : (Cost.cmp1 + (Cost.cmpN l₂.length + Cost.mvN (4 * l₂.length)) +
            (Cost.cmpN l₂.length + Cost.mvN (4 * l₂.length))) ≤ Cost.const (1 + 8 * l.length) := by
          refine Cost.le_const ?_ ?_
          · simp only [Cost.cmp_add, Cost.cmp_cmp1, Cost.cmp_cmpN, Cost.cmp_mvN, hl₂len]
            omega
          · simp only [Cost.mv_add, Cost.mv_cmp1, Cost.mv_cmpN, Cost.mv_mvN, hl₂len]
            omega
        have hpc_cmp : (Cost.cmp1 + (Cost.cmpN l₂.length + Cost.mvN (4 * l₂.length)) +
            (Cost.cmpN l₂.length + Cost.mvN (4 * l₂.length))).cmp ≤ 1 + 8 * l.length := by
          have h := Cost.cmp_le_of_le hpc; rwa [Cost.cmp_const] at h
        have hpc_mv : (Cost.cmp1 + (Cost.cmpN l₂.length + Cost.mvN (4 * l₂.length)) +
            (Cost.cmpN l₂.length + Cost.mvN (4 * l₂.length))).mv ≤ 1 + 8 * l.length := by
          have h := Cost.mv_le_of_le hpc; rwa [Cost.mv_const] at h
        cases hsome : l₂[g / 2]? with
        | none =>
            refine Cost.le_const ?_ ?_
            · simp only [Cost.cmp_add]
              omega
            · simp only [Cost.mv_add]
              omega
        | some pv =>
            dsimp only
            generalize hA : (partition (fun x => Cmp.blt (proj x) (proj pv)) l₂).1 = A
            generalize hR : (partition (fun x => Cmp.blt (proj x) (proj pv)) l₂).2 = R
            generalize hB : (partition (fun x => Cmp.beq (proj x) (proj pv)) R).1 = B
            generalize hC : (partition (fun x => Cmp.beq (proj x) (proj pv)) R).2 = C
            have hspec := bfprtAux_spec proj fuel (g / 2) (l₁.take g) hgfuel
            have hmmperm : mm.Perm (l₁.take g) := by rw [← hmm]; exact hspec.1
            have hmm_len : mm.length = g := by rw [hmmperm.length_eq, htake]
            have hkg : g / 2 < (l₁.take g).length := by rw [htake]; omega
            obtain ⟨xs, ys, y, hdec, hxs, hrank_y⟩ := hspec.2 hkg
            have hg1 : 1 ≤ g := by omega
            have hpv_y : l₂[g / 2]? = some y := by
              have h1 : g / 2 < mm.length := by
                rw [hmm_len]
                exact Nat.div_lt_self (by omega) (by decide)
              rw [← hl₂, List.getElem?_append_left h1, ← hmm, hdec]
              rw [List.getElem?_append_right (by omega)]
              rw [hxs]
              simp
            have hpv_eq : pv = y := by
              rw [hpv_y] at hsome
              exact (Option.some.inj hsome).symm
            have hrank : IsKthSmallest proj (l₁.take g) (g / 2) pv := by
              rw [hpv_eq]
              exact isKthSmallest_of_perm hspec.1 hrank_y
            have hmed : l₁.take g = medians proj l g hgrp5 g (Nat.le_refl g) := by
              rw [← hl₁]
              exact groupPass_take_eq_medians proj l g hgrp5
            have hpart := partition_lengths_le_of_medians proj
              (l := l) (l₁ := l₁) (mm := mm) (l₂ := l₂) (pv := pv) (g := g)
              (by rw [← hl₁]; exact groupPass_perm proj g l) hmmperm (by rw [← hl₂])
              hgrp5 (by omega) hmed hrank
            rw [hA, hR, hC] at hpart
            have hAfuel : A.length ≤ fuel := by omega
            have hCfuel : C.length ≤ fuel := by omega
            have hCB : C.length ≤ l.length - 3 * (g - g / 2) := by
              have hle3 : 3 * (g - g / 2) ≤ 3 * (g / 2 + 1) :=
                Nat.mul_le_mul_left 3 (by omega)
              exact Nat.le_trans hpart.2 (Nat.sub_le_sub_left hle3 l.length)
            have hAcost : (bfprtAuxC proj fuel k A).2 ≤
                Cost.const (400 * (l.length - 3 * (g - g / 2))) := by
              have h := ih k A hAfuel
              have hle : A.length ≤ l.length - 3 * (g - g / 2) := hpart.1
              exact Cost.le_trans h (Cost.const_le_const
                (Nat.mul_le_mul_left 400 hle))
            have hCcost : (bfprtAuxC proj fuel (k - A.length - B.length) C).2 ≤
                Cost.const (400 * (l.length - 3 * (g - g / 2))) := by
              have h := ih (k - A.length - B.length) C hCfuel
              exact Cost.le_trans h (Cost.const_le_const
                (Nat.mul_le_mul_left 400 hCB))
            have hAcost_cmp : (bfprtAuxC proj fuel k A).2.cmp ≤
                400 * (l.length - 3 * (g - g / 2)) := by
              have h := Cost.cmp_le_of_le hAcost; rwa [Cost.cmp_const] at h
            have hAcost_mv : (bfprtAuxC proj fuel k A).2.mv ≤
                400 * (l.length - 3 * (g - g / 2)) := by
              have h := Cost.mv_le_of_le hAcost; rwa [Cost.mv_const] at h
            have hCcost_cmp : (bfprtAuxC proj fuel (k - A.length - B.length) C).2.cmp ≤
                400 * (l.length - 3 * (g - g / 2)) := by
              have h := Cost.cmp_le_of_le hCcost; rwa [Cost.cmp_const] at h
            have hCcost_mv : (bfprtAuxC proj fuel (k - A.length - B.length) C).2.mv ≤
                400 * (l.length - 3 * (g - g / 2)) := by
              have h := Cost.mv_le_of_le hCcost; rwa [Cost.mv_const] at h
            by_cases h1 : k < A.length
            · simp only [h1, ite_true]
              refine Cost.le_const ?_ ?_
              · simp only [Cost.cmp_add, Cost.cmp_cmp1, Cost.cmp_cmpN, Cost.cmp_mvN, hl₂len]
                omega
              · simp only [Cost.mv_add, Cost.mv_cmp1, Cost.mv_cmpN, Cost.mv_mvN, hl₂len]
                omega
            · simp only [h1, ite_false]
              by_cases h2 : A.length + B.length ≤ k
              · simp only [h2, ite_true]
                refine Cost.le_const ?_ ?_
                · simp only [Cost.cmp_add, Cost.cmp_cmp1, Cost.cmp_cmpN, Cost.cmp_mvN, hl₂len]
                  omega
                · simp only [Cost.mv_add, Cost.mv_cmp1, Cost.mv_cmpN, Cost.mv_mvN, hl₂len]
                  omega
              · simp only [h2, ite_false]
                refine Cost.le_const ?_ ?_
                · simp only [Cost.cmp_add, Cost.cmp_cmp1, Cost.cmp_cmpN, Cost.cmp_mvN, hl₂len]
                  omega
                · simp only [Cost.mv_add, Cost.mv_cmp1, Cost.mv_cmpN, Cost.mv_mvN, hl₂len]
                  omega


theorem bfprtAuxC_cmp_le (proj : α → β) (fuel k : Nat) (l : List α) (hl : l.length ≤ fuel) :
    (bfprtAuxC proj fuel k l).2.cmp ≤ 400 * l.length := by
  have h := Cost.cmp_le_of_le (bfprtAuxC_le_linear proj fuel k l hl)
  rwa [Cost.cmp_const] at h

/-- **Linear move bound** (`bfprtAuxC_mv_le`). -/
theorem bfprtAuxC_mv_le (proj : α → β) (fuel k : Nat) (l : List α) (hl : l.length ≤ fuel) :
    (bfprtAuxC proj fuel k l).2.mv ≤ 400 * l.length := by
  have h := Cost.mv_le_of_le (bfprtAuxC_le_linear proj fuel k l hl)
  rwa [Cost.mv_const] at h

/-- **The counting selection is `O(n)`** (uniform bound, constant 400). -/
theorem bfprtAuxC_bigO (proj : α → β) (k : Nat) :
    CostBigOWith 400 List.length (fun l => (bfprtAuxC proj l.length k l).2) (fun n => n) :=
  fun l => bfprtAuxC_le_linear proj l.length k l (Nat.le_refl _)

end Bfprt
end Tcs
