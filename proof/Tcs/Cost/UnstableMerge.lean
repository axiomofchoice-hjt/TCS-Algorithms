/-
  Cost of `inplace_unstable_merge` (`include/tcs/inplace/unstable_merge.hpp`).

  The two block phases of the C++ routine are modelled one level up in
  `Tcs.UnstableMerge` (on the list of blocks, by `blkMerge` / `blockMergeStd`), which is
  order-equivalent but not literally the C++ element order.  Following the design of the
  module brief, the *result* of the costing pipeline is the model's result (so that
  correctness is inherited from `unstableMerge_sorted_and_perm`), while the *cost* is a
  separate loop-level simulation of the C++ on the same structures:

  * `selSortC`  — the selection sort of the blocks by the `(first key, last key)` pair.
    Each scan step performs the C++ pair comparison `a > c || (a == c && b > d)`, charged
    its maximum of `3` key comparisons; each `swap_ranges` of a `bs`-block costs `3 * bs`
    moves (the C++ charges `3 * (q - p)` for `std::swap_ranges(p, q, r)`).
  * `pairwiseC` — the pairwise block merge.  Every turn calls `mergeSwapLoopC` on a
    two-block window (fuel `2 * bs`, the C++ `merge_with_swap` window) and swaps one
    block when another block follows, so one turn is at most `2 * bs` comparisons and
    `3 * (2 * bs) + 3 * bs = 9 * bs` moves.
  * the tail `bubbleSortC` and the final `mergeByRotationC` are taken from the already
    verified cost modules.

  The last section proves the linear bound.  Because `Nat.sqrt_le` / `Nat.lt_succ_sqrt`
  in core depend on `Classical.choice`, the two `Nat.sqrt` bounds used here are reproved
  constructively at the top of this file.  The bounds carry the algorithm's precondition
  `k ≤ l.length`; without it the clamped `Nat` arithmetic lets the aligned prefix leave
  the array and the suffix/merge phases degenerate (see the report).
-/
import Tcs.Cost
import Tcs.Cost.Sort
import Tcs.Cost.Merge
import Tcs.UnstableMerge

namespace Tcs

variable {α : Type u} {β : Type v} [Cmp β]

/-! ## Constructive bounds for `Nat.sqrt` -/

/-- The arithmetic-geometric mean inequality for naturals. -/
theorem um_am_gm : {a b : Nat} → 4 * a * b ≤ (a + b) * (a + b)
  | 0, _ => by rw [Nat.mul_zero, Nat.zero_mul]; exact Nat.zero_le _
  | _, 0 => by rw [Nat.mul_zero]; exact Nat.zero_le _
  | a + 1, b + 1 => by
    simpa only [Nat.mul_add, Nat.add_mul, show (4 : Nat) = 1 + 1 + 1 + 1 from rfl, Nat.one_mul,
      Nat.mul_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_le_add_iff_left]
      using Nat.add_le_add_right (@um_am_gm a b) 4

/-- Cancel a common factor on the right.  This is a constructive replacement for core's
`Nat.lt_of_mul_lt_mul_right`, which depends on `Classical.choice`. -/
theorem um_mul_lt_cancel_right {a b c : Nat} (h : b * a < c * a) : b < c :=
  Nat.lt_of_not_le fun hcb => absurd (Nat.mul_le_mul_right a hcb) (Nat.not_le_of_lt h)

/-- One Newton step from a positive guess already lands above `sqrt n`.  This is the
invariant that keeps the iteration from undershooting. -/
theorem um_lt_sq_div {g n m s : Nat} (hg : 0 < g) (hm : m = s / 2) (hs : s = g + n / g) :
    n < (m + 1) * (m + 1) := by
  have h4 : n < g * (n / g) + g := by
    have h := Nat.lt_mul_div_succ n hg
    rw [Nat.mul_add, Nat.mul_one] at h
    exact h
  have hstep : g * g + n < (m + 1) * (2 * g) := by
    calc g * g + n < g * (s + 1) := by
          rw [hs]; simp only [Nat.mul_add, Nat.mul_one]; omega
      _ ≤ g * (2 * (m + 1)) := Nat.mul_le_mul_left g (by omega)
      _ = (m + 1) * (2 * g) := by simp only [Nat.mul_left_comm, Nat.mul_comm]
  have hk : n * ((2 * g) * (2 * g)) ≤ (g * g + n) * (g * g + n) := by
    have heq : n * ((2 * g) * (2 * g)) = 4 * (g * g) * n := by
      rw [Nat.mul_mul_mul_comm 2 g 2 g, Nat.mul_comm n]
    rw [heq]
    exact um_am_gm (a := g * g) (b := n)
  have hgoal : n * ((2 * g) * (2 * g)) < ((m + 1) * (m + 1)) * ((2 * g) * (2 * g)) := by
    refine Nat.lt_of_le_of_lt hk ?_
    rw [← Nat.mul_mul_mul_comm (m + 1) (2 * g) (m + 1) (2 * g)]
    exact Nat.mul_self_lt_mul_self hstep
  exact um_mul_lt_cancel_right hgoal

/-- The Newton iteration never overshoots `n`. -/
theorem um_sqrt_iter_sq_le (n : Nat) :
    ∀ guess, Nat.sqrt.iter n guess * Nat.sqrt.iter n guess ≤ n :=
  Nat.sqrt.iter.induct n (fun g => Nat.sqrt.iter n g * Nat.sqrt.iter n g ≤ n)
    (fun g hlt ih => by
      rw [Nat.sqrt.iter.eq_1, dite_eq_left hlt]
      exact ih)
    (fun g hnot => by
      rw [Nat.sqrt.iter.eq_1, dite_eq_right hnot]
      by_cases hg : g = 0
      · subst g; simp
      · have hgpos : 0 < g := Nat.pos_of_ne_zero hg
        have hle : g ≤ n / g := by
          have h1 : g ≤ (g + n / g) / 2 := Nat.le_of_not_lt hnot
          have h2 : g * 2 ≤ g + n / g := (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mp h1
          omega
        exact (Nat.le_div_iff_mul_le hgpos).mp hle)

/-- Along a guess above `sqrt n`, the iteration stays above it. -/
theorem um_sqrt_iter_lt_succ_sq (n : Nat) :
    ∀ guess, n < (guess + 1) * (guess + 1) →
      n < (Nat.sqrt.iter n guess + 1) * (Nat.sqrt.iter n guess + 1) :=
  Nat.sqrt.iter.induct n
    (fun g => n < (g + 1) * (g + 1) →
      n < (Nat.sqrt.iter n g + 1) * (Nat.sqrt.iter n g + 1))
    (fun g hlt ih hg => by
      rw [Nat.sqrt.iter.eq_1, dite_eq_left hlt]
      apply ih
      by_cases hg0 : g = 0
      · subst g
        simpa using hg
      · exact um_lt_sq_div (Nat.pos_of_ne_zero hg0) rfl rfl)
    (fun g hnot hg => by
      rw [Nat.sqrt.iter.eq_1, dite_eq_right hnot]
      exact hg)

/-- Constructive lower bound: `Nat.sqrt n * Nat.sqrt n ≤ n`.  (Core's `Nat.sqrt_le`
depends on `Classical.choice`.) -/
theorem um_sqrt_mul_self_le (n : Nat) : Nat.sqrt n * Nat.sqrt n ≤ n := by
  rw [Nat.sqrt.eq_def]
  by_cases h : n ≤ 1
  · rw [ite_eq_left h]
    match n with
    | 0 => simp
    | 1 => simp
    | m + 2 => omega
  · rw [ite_eq_right h]
    exact um_sqrt_iter_sq_le n _

/-- Constructive upper bound: `n < (Nat.sqrt n + 1) * (Nat.sqrt n + 1)`.  (Core's
`Nat.lt_succ_sqrt` depends on `Classical.choice`.) -/
theorem um_sqrt_lt_succ_sq (n : Nat) : n < (Nat.sqrt n + 1) * (Nat.sqrt n + 1) := by
  rw [Nat.sqrt.eq_def]
  by_cases h : n ≤ 1
  · rw [ite_eq_left h]
    match n with
    | 0 => decide
    | 1 => decide
    | m + 2 => omega
  · rw [ite_eq_right h]
    have hlog := Nat.lt_log2_self (n := n)
    have hle : n.log2 + 1 ≤ 2 * (n.log2 / 2 + 1) := by omega
    have hp : 2 ^ (n.log2 + 1) ≤ 2 ^ (2 * (n.log2 / 2 + 1)) :=
      Nat.pow_le_pow_right (by decide : 0 < 2) hle
    have hsq : 2 ^ (2 * (n.log2 / 2 + 1)) ≤
        (2 ^ (n.log2 / 2 + 1) + 1) * (2 ^ (n.log2 / 2 + 1) + 1) := by
      have heq1 : 2 * (n.log2 / 2 + 1) = (n.log2 / 2 + 1) + (n.log2 / 2 + 1) := by
        rw [Nat.mul_comm, Nat.mul_two]
      have heq2 : 2 ^ ((n.log2 / 2 + 1) + (n.log2 / 2 + 1)) =
          2 ^ (n.log2 / 2 + 1) * 2 ^ (n.log2 / 2 + 1) := Nat.pow_add 2 _ _
      rw [heq1, heq2]
      exact Nat.mul_self_le_mul_self (Nat.le_succ _)
    refine um_sqrt_iter_lt_succ_sq n _ ?_
    rw [Nat.one_shiftLeft]
    exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hlog hp) hsq

/-! ## `block_selection_sort` -/

/-- One outer scan of the C++ `block_selection_sort`, from a current minimum `cur`.
`moved` records the C++'s `min != cur` test: it is set as soon as a scanned block becomes
the new minimum.  The result list has the winner removed and the starting block put back
in the winner's place, so `winner :: rest` permutes `cur :: rest`. -/
def selScanC (proj : α → β) :
    List α → Bool → List (List α) → (List α × Bool × List (List α)) × Cost
  | cur, moved, [] => ((cur, moved, []), 0)
  | cur, moved, b :: rest =>
      let r := selScanC proj cur moved rest
      if PairLe proj r.1.1 b then
        ((r.1.1, r.1.2.1, b :: r.1.2.2), r.2 + Cost.cmpN 3)
      else
        ((b, true, r.1.1 :: r.1.2.2), r.2 + Cost.cmpN 3)

theorem selScanC_nil (proj : α → β) (cur : List α) (moved : Bool) :
    selScanC proj cur moved [] = ((cur, moved, []), 0) :=
  rfl

theorem selScanC_cons (proj : α → β) (cur : List α) (moved : Bool)
    (b : List α) (rest : List (List α)) :
    selScanC proj cur moved (b :: rest) =
      (let r := selScanC proj cur moved rest
       if PairLe proj r.1.1 b then
         ((r.1.1, r.1.2.1, b :: r.1.2.2), r.2 + Cost.cmpN 3)
       else
         ((b, true, r.1.1 :: r.1.2.2), r.2 + Cost.cmpN 3)) :=
  rfl

/-- A scan only permutes. -/
theorem selScanC_perm (proj : α → β) :
    ∀ (cur : List α) (moved : Bool) (rest : List (List α)),
      List.Perm ((selScanC proj cur moved rest).1.1 :: (selScanC proj cur moved rest).1.2.2)
        (cur :: rest) := by
  intro cur moved rest
  induction rest generalizing cur moved with
  | nil => rw [selScanC_nil]
  | cons b rest ih =>
      rw [selScanC_cons]
      dsimp only
      by_cases h : PairLe proj (selScanC proj cur moved rest).1.1 b = true
      · rw [ite_eq_left h]
        exact ((List.Perm.swap _ b _).symm.trans (List.Perm.cons b (ih cur moved))).trans
          (List.Perm.swap b cur rest).symm
      · rw [ite_eq_right h]
        exact (List.Perm.cons b (ih cur moved)).trans (List.Perm.swap b cur rest).symm

/-- A scan keeps the block count. -/
theorem selScanC_length (proj : α → β) :
    ∀ (cur : List α) (moved : Bool) (rest : List (List α)),
      (selScanC proj cur moved rest).1.2.2.length = rest.length := by
  intro cur moved rest
  induction rest generalizing cur moved with
  | nil => rw [selScanC_nil]
  | cons b rest ih =>
      rw [selScanC_cons]
      dsimp only
      by_cases h : PairLe proj (selScanC proj cur moved rest).1.1 b = true
      · rw [ite_eq_left h]
        simp only [List.length_cons, ih]
      · rw [ite_eq_right h]
        simp only [List.length_cons, ih]

/-- Each scan step performs exactly `3` key comparisons. -/
theorem selScanC_cmp (proj : α → β) :
    ∀ (cur : List α) (moved : Bool) (rest : List (List α)),
      (selScanC proj cur moved rest).2.cmp = 3 * rest.length := by
  intro cur moved rest
  induction rest generalizing cur moved with
  | nil => rw [selScanC_nil]; simp
  | cons b rest ih =>
      rw [selScanC_cons]
      dsimp only
      by_cases h : PairLe proj (selScanC proj cur moved rest).1.1 b = true
      · rw [ite_eq_left h]
        simp only [Cost.cmp_add, Cost.cmp_cmpN, ih, List.length_cons]
        omega
      · rw [ite_eq_right h]
        simp only [Cost.cmp_add, Cost.cmp_cmpN, ih, List.length_cons]
        omega

/-- A scan never moves an element by itself (the swap is charged by the caller). -/
theorem selScanC_mv (proj : α → β) :
    ∀ (cur : List α) (moved : Bool) (rest : List (List α)),
      (selScanC proj cur moved rest).2.mv = 0 := by
  intro cur moved rest
  induction rest generalizing cur moved with
  | nil => rw [selScanC_nil]; simp
  | cons b rest ih =>
      rw [selScanC_cons]
      dsimp only
      by_cases h : PairLe proj (selScanC proj cur moved rest).1.1 b = true
      · rw [ite_eq_left h]
        simp only [Cost.mv_add, Cost.mv_cmpN, ih]
      · rw [ite_eq_right h]
        simp only [Cost.mv_add, Cost.mv_cmpN, ih]

/-- `block_selection_sort` with an explicit step budget; the recursion is structural in
the budget so that the equations hold definitionally. -/
def selSortAuxC (proj : α → β) (bs : Nat) : Nat → List (List α) → List (List α) × Cost
  | 0, _ => ([], 0)
  | _ + 1, [] => ([], 0)
  | fuel + 1, b :: rest =>
      let r := selScanC proj b false rest
      let s := selSortAuxC proj bs fuel r.1.2.2
      (r.1.1 :: s.1, r.2 + (if r.1.2.1 then Cost.mvN (3 * bs) else 0) + s.2)

/-- The C++ `block_selection_sort` over a list of blocks, carrying its cost: for every
position, scan the remaining blocks for the smallest `(first key, last key)` pair (three
key comparisons per step) and `swap_ranges` a whole block (`3 * bs` moves) when the
minimum moved. -/
def selSortC (proj : α → β) (bs : Nat) (blks : List (List α)) : List (List α) × Cost :=
  selSortAuxC proj bs blks.length blks

theorem selSortAuxC_zero (proj : α → β) (bs : Nat) (blks : List (List α)) :
    selSortAuxC proj bs 0 blks = ([], 0) :=
  rfl

theorem selSortAuxC_succ_nil (proj : α → β) (bs : Nat) (fuel : Nat) :
    selSortAuxC proj bs (fuel + 1) [] = ([], 0) :=
  rfl

theorem selSortAuxC_succ_cons (proj : α → β) (bs : Nat) (fuel : Nat)
    (b : List α) (rest : List (List α)) :
    selSortAuxC proj bs (fuel + 1) (b :: rest) =
      (let r := selScanC proj b false rest
       let s := selSortAuxC proj bs fuel r.1.2.2
       (r.1.1 :: s.1, r.2 + (if r.1.2.1 then Cost.mvN (3 * bs) else 0) + s.2)) :=
  rfl

/-- The selection sort only permutes the block list. -/
theorem selSortAuxC_perm (proj : α → β) (bs : Nat) (fuel : Nat) :
    ∀ blks : List (List α), blks.length ≤ fuel → (selSortAuxC proj bs fuel blks).1.Perm blks := by
  induction fuel with
  | zero =>
      intro blks hlen
      match blks with
      | [] => rw [selSortAuxC_zero]
      | b :: rest => exact absurd hlen (Nat.not_succ_le_zero rest.length)
  | succ fuel ih =>
      intro blks hlen
      match blks with
      | [] => rw [selSortAuxC_succ_nil]
      | b :: rest =>
          rw [selSortAuxC_succ_cons]
          dsimp only
          have hscan := selScanC_perm proj b false rest
          have hlen' : (selScanC proj b false rest).1.2.2.length ≤ fuel := by
            rw [selScanC_length]
            simp only [List.length_cons] at hlen
            omega
          exact (List.Perm.cons _ (ih _ hlen')).trans hscan

/-- The selection sort performs at most `3 * tri (n - 1)` key comparisons. -/
theorem selSortAuxC_cmp_le (proj : α → β) (bs : Nat) (fuel : Nat) :
    ∀ blks : List (List α), blks.length ≤ fuel →
      (selSortAuxC proj bs fuel blks).2.cmp ≤ 3 * tri (blks.length - 1) := by
  induction fuel with
  | zero =>
      intro blks hlen
      match blks with
      | [] => rw [selSortAuxC_zero]; simp
      | b :: rest => exact absurd hlen (Nat.not_succ_le_zero rest.length)
  | succ fuel ih =>
      intro blks hlen
      match blks with
      | [] => rw [selSortAuxC_succ_nil]; simp
      | b :: rest =>
          rw [selSortAuxC_succ_cons]
          dsimp only
          have hlen' : (selScanC proj b false rest).1.2.2.length ≤ fuel := by
            rw [selScanC_length]
            simp only [List.length_cons] at hlen
            omega
          have hrec := ih _ hlen'
          rw [selScanC_length] at hrec
          have hscan := selScanC_cmp proj b false rest
          have hmoved : (if (selScanC proj b false rest).1.2.1 then Cost.mvN (3 * bs) else 0).cmp
              = 0 := by
            by_cases hm : (selScanC proj b false rest).1.2.1 = true
            · rw [ite_eq_left hm]; simp
            · rw [ite_eq_right hm]; simp
          simp only [Cost.cmp_add, hscan, hmoved]
          simp only [List.length_cons, Nat.add_sub_cancel]
          have htri := tri_eq_add_pred rest.length
          rw [htri, Nat.mul_add]
          omega

/-- The selection sort performs at most `3 * bs` moves per position. -/
theorem selSortAuxC_mv_le (proj : α → β) (bs : Nat) (fuel : Nat) :
    ∀ blks : List (List α), blks.length ≤ fuel →
      (selSortAuxC proj bs fuel blks).2.mv ≤ 3 * bs * (blks.length - 1) := by
  induction fuel with
  | zero =>
      intro blks hlen
      match blks with
      | [] => rw [selSortAuxC_zero]; simp
      | b :: rest => exact absurd hlen (Nat.not_succ_le_zero rest.length)
  | succ fuel ih =>
      intro blks hlen
      match blks with
      | [] => rw [selSortAuxC_succ_nil]; simp
      | b :: rest =>
          rw [selSortAuxC_succ_cons]
          dsimp only
          cases rest with
          | nil =>
              rw [selScanC_nil]
              cases fuel with
              | zero => rw [selSortAuxC_zero]; simp
              | succ f => rw [selSortAuxC_succ_nil]; simp
          | cons c rest' =>
              have hlen' : (selScanC proj b false (c :: rest')).1.2.2.length ≤ fuel := by
                rw [selScanC_length]
                simp only [List.length_cons] at hlen ⊢
                omega
              have hrec := ih _ hlen'
              rw [selScanC_length] at hrec
              simp only [List.length_cons, Nat.add_sub_cancel] at hrec
              have hmoved : (if (selScanC proj b false (c :: rest')).1.2.1 then
                  Cost.mvN (3 * bs) else 0).mv ≤ 3 * bs := by
                by_cases hm : (selScanC proj b false (c :: rest')).1.2.1 = true
                · rw [ite_eq_left hm]; simp
                · rw [ite_eq_right hm]; simp
              rw [Cost.mv_add, Cost.mv_add, selScanC_mv, Nat.zero_add]
              simp only [List.length_cons, Nat.add_sub_cancel]
              rw [Nat.mul_succ]
              omega

theorem selSortC_fst_eq (proj : α → β) (bs : Nat) (blks : List (List α)) :
    (selSortC proj bs blks).1 = (selSortAuxC proj bs blks.length blks).1 :=
  rfl

theorem selSortC_perm (proj : α → β) (bs : Nat) (blks : List (List α)) :
    (selSortC proj bs blks).1.Perm blks :=
  selSortAuxC_perm proj bs blks.length blks (Nat.le_refl _)

theorem selSortC_length (proj : α → β) (bs : Nat) (blks : List (List α)) :
    (selSortC proj bs blks).1.length = blks.length :=
  (selSortC_perm proj bs blks).length_eq

theorem selSortC_cmp_le (proj : α → β) (bs : Nat) (blks : List (List α)) :
    (selSortC proj bs blks).2.cmp ≤ 3 * tri (blks.length - 1) :=
  selSortAuxC_cmp_le proj bs blks.length blks (Nat.le_refl _)

theorem selSortC_mv_le (proj : α → β) (bs : Nat) (blks : List (List α)) :
    (selSortC proj bs blks).2.mv ≤ 3 * bs * (blks.length - 1) :=
  selSortAuxC_mv_le proj bs blks.length blks (Nat.le_refl _)

/-! ## `block_merge_pairwise` -/

/-- The C++ `block_merge_pairwise` loop with its cost.  `done` is the finished prefix,
`D` the block carried along (never read, only its length matters), `H`/`Z` the two live
blocks; a turn merges `H` and `Z` through `mergeSwapLoopC` on the two-block window and
swaps one block whenever a further block follows. -/
def pairwiseGoC (proj : α → β) (bs : Nat) :
    Nat → List (List α) → List α → List (List α) → List (List α) × Cost
  | 0, done, D, rest => (done ++ D :: rest, 0)
  | fuel + 1, done, D, H :: Z :: (W :: rest') =>
      let s := pairwiseGoC proj bs fuel (done ++ [(mergeTwo proj H Z).take bs]) D
        ((mergeTwo proj H Z).drop bs :: W :: rest')
      (s.1, (mergeSwapLoopC proj (2 * bs) (D ++ H ++ Z) 0 bs (2 * bs) (2 * bs) (3 * bs)).2
        + Cost.mvN (3 * bs) + s.2)
  | _ + 1, done, D, H :: Z :: [] =>
      (done ++ [(mergeTwo proj H Z).take bs, (mergeTwo proj H Z).drop bs, D],
        (mergeSwapLoopC proj (2 * bs) (D ++ H ++ Z) 0 bs (2 * bs) (2 * bs) (3 * bs)).2)
  | _ + 1, done, D, rest => (done ++ D :: rest, 0)

/-- The C++ `block_merge_pairwise` on a whole block list, carrying its cost. -/
def pairwiseC (proj : α → β) (bs : Nat) : List (List α) → List (List α) × Cost
  | [] => ([], 0)
  | b0 :: rest => pairwiseGoC proj bs rest.length [] b0 rest

/-- The four reduction equations of the costing loop, stated as `rfl` lemmas so that
the overlapping-pattern side conditions of the generated equation lemmas never appear. -/
theorem pairwiseGoC_zero (proj : α → β) (bs : Nat) (done : List (List α)) (D : List α)
    (rest : List (List α)) :
    pairwiseGoC proj bs 0 done D rest = (done ++ D :: rest, 0) :=
  rfl

theorem pairwiseGoC_nil (proj : α → β) (bs : Nat) (fuel : Nat) (done : List (List α))
    (D : List α) :
    pairwiseGoC proj bs (fuel + 1) done D [] = (done ++ D :: [], 0) :=
  rfl

theorem pairwiseGoC_single (proj : α → β) (bs : Nat) (fuel : Nat) (done : List (List α))
    (D H : List α) :
    pairwiseGoC proj bs (fuel + 1) done D [H] = (done ++ D :: [H], 0) :=
  rfl

theorem pairwiseGoC_two (proj : α → β) (bs : Nat) (fuel : Nat) (done : List (List α))
    (D H Z : List α) :
    pairwiseGoC proj bs (fuel + 1) done D [H, Z] =
      (done ++ [(mergeTwo proj H Z).take bs, (mergeTwo proj H Z).drop bs, D],
        (mergeSwapLoopC proj (2 * bs) (D ++ H ++ Z) 0 bs (2 * bs) (2 * bs) (3 * bs)).2) :=
  rfl

theorem pairwiseGoC_three (proj : α → β) (bs : Nat) (fuel : Nat) (done : List (List α))
    (D H Z W : List α) (rest : List (List α)) :
    pairwiseGoC proj bs (fuel + 1) done D (H :: Z :: W :: rest) =
      (let s := pairwiseGoC proj bs fuel (done ++ [(mergeTwo proj H Z).take bs]) D
         ((mergeTwo proj H Z).drop bs :: W :: rest)
       (s.1, (mergeSwapLoopC proj (2 * bs) (D ++ H ++ Z) 0 bs (2 * bs) (2 * bs) (3 * bs)).2
         + Cost.mvN (3 * bs) + s.2)) :=
  rfl

theorem blockMergeStd_nil (proj : α → β) (bs : Nat) (fuel : Nat) (done : List (List α))
    (D : List α) :
    blockMergeStd proj bs (fuel + 1) done D [] = done ++ D :: [] :=
  rfl

theorem blockMergeStd_single (proj : α → β) (bs : Nat) (fuel : Nat) (done : List (List α))
    (D H : List α) :
    blockMergeStd proj bs (fuel + 1) done D [H] = done ++ D :: [H] :=
  rfl

theorem blockMergeStd_two (proj : α → β) (bs : Nat) (fuel : Nat) (done : List (List α))
    (D H Z : List α) :
    blockMergeStd proj bs (fuel + 1) done D [H, Z] =
      done ++ [(mergeTwo proj H Z).take bs, (mergeTwo proj H Z).drop bs, D] :=
  rfl

theorem blockMergeStd_three (proj : α → β) (bs : Nat) (fuel : Nat) (done : List (List α))
    (D H Z W : List α) (rest : List (List α)) :
    blockMergeStd proj bs (fuel + 1) done D (H :: Z :: W :: rest) =
      blockMergeStd proj bs fuel (done ++ [(mergeTwo proj H Z).take bs]) D
        ((mergeTwo proj H Z).drop bs :: W :: rest) :=
  rfl

/-- The costing loop computes the model's `blockMergeStd` state; they differ only in the
element order inside the equal-key groups, which the cost cannot see. -/
theorem pairwiseGoC_fst (proj : α → β) (bs : Nat) :
    ∀ (fuel : Nat) (done : List (List α)) (D : List α) (rest : List (List α)),
      (pairwiseGoC proj bs fuel done D rest).1 = blockMergeStd proj bs fuel done D rest := by
  intro fuel
  induction fuel with
  | zero => intro done D rest; rw [pairwiseGoC.eq_1, blockMergeStd.eq_1]
  | succ fuel ih =>
      intro done D rest
      cases rest with
      | nil => rw [pairwiseGoC_nil, blockMergeStd_nil]
      | cons H rest1 =>
          cases rest1 with
          | nil => rw [pairwiseGoC_single, blockMergeStd_single]
          | cons Z rest2 =>
              cases rest2 with
              | nil => rw [pairwiseGoC_two, blockMergeStd_two]
              | cons W rest3 =>
                  rw [pairwiseGoC_three, blockMergeStd_three]
                  dsimp only
                  exact ih _ _ _

theorem pairwiseC_fst_eq (proj : α → β) (bs : Nat) (blks : List (List α)) :
    (pairwiseC proj bs blks).1 = blockMergePairwise proj bs blks := by
  match blks with
  | [] => rw [pairwiseC.eq_1]; rfl
  | b0 :: rest => rw [pairwiseC.eq_2, pairwiseGoC_fst]; rfl

theorem pairwiseC_flatten_perm (proj : α → β) (bs : Nat) (blks : List (List α)) :
    (pairwiseC proj bs blks).1.flatten.Perm blks.flatten := by
  rw [pairwiseC_fst_eq]
  exact blockMergePairwise_flatten_perm proj bs blks

theorem pairwiseC_flatten_length (proj : α → β) (bs : Nat) (blks : List (List α)) :
    (pairwiseC proj bs blks).1.flatten.length = blks.flatten.length :=
  (pairwiseC_flatten_perm proj bs blks).length_eq

/-- One pairwise turn performs at most `2 * bs` key comparisons. -/
theorem pairwiseGoC_cmp_le (proj : α → β) (bs : Nat) :
    ∀ (fuel : Nat) (done : List (List α)) (D : List α) (rest : List (List α)),
      (pairwiseGoC proj bs fuel done D rest).2.cmp ≤ 2 * bs * rest.length := by
  intro fuel
  induction fuel with
  | zero => intro done D rest; rw [pairwiseGoC_zero]; simp
  | succ fuel ih =>
      intro done D rest
      cases rest with
      | nil => rw [pairwiseGoC_nil]; simp
      | cons H rest1 =>
          cases rest1 with
          | nil => rw [pairwiseGoC_single]; simp
          | cons Z rest2 =>
              cases rest2 with
              | nil =>
                  rw [pairwiseGoC_two]
                  dsimp only
                  have h := mergeSwapLoopC_cmp_le proj (2 * bs) (D ++ H ++ Z) 0 bs (2 * bs)
                    (2 * bs) (3 * bs)
                  rw [show (([H, Z] : List (List α)).length) = 2 from rfl]
                  have h2 : 2 * bs ≤ 2 * bs * 2 := Nat.le_mul_of_pos_right (2 * bs)
                    (by decide : 0 < 2)
                  omega
              | cons W rest3 =>
                  rw [pairwiseGoC_three]
                  dsimp only
                  have h1 := mergeSwapLoopC_cmp_le proj (2 * bs) (D ++ H ++ Z) 0 bs (2 * bs)
                    (2 * bs) (3 * bs)
                  have h2 := ih (done ++ [(mergeTwo proj H Z).take bs]) D
                    ((mergeTwo proj H Z).drop bs :: W :: rest3)
                  simp only [Cost.cmp_add, Cost.cmp_mvN] at *
                  rw [show (H :: Z :: W :: rest3).length =
                    ((mergeTwo proj H Z).drop bs :: W :: rest3).length + 1 from rfl, Nat.mul_succ]
                  omega

/-- One pairwise turn performs at most `9 * bs` moves: the merge swaps within a two-block
window (`3 * 2 * bs`) plus the conditional block `swap_ranges` (`3 * bs`). -/
theorem pairwiseGoC_mv_le (proj : α → β) (bs : Nat) :
    ∀ (fuel : Nat) (done : List (List α)) (D : List α) (rest : List (List α)),
      (pairwiseGoC proj bs fuel done D rest).2.mv ≤ 9 * bs * rest.length := by
  intro fuel
  induction fuel with
  | zero => intro done D rest; rw [pairwiseGoC_zero]; simp
  | succ fuel ih =>
      intro done D rest
      cases rest with
      | nil => rw [pairwiseGoC_nil]; simp
      | cons H rest1 =>
          cases rest1 with
          | nil => rw [pairwiseGoC_single]; simp
          | cons Z rest2 =>
              cases rest2 with
              | nil =>
                  rw [pairwiseGoC_two]
                  dsimp only
                  have h := mergeSwapLoopC_mv_le proj (2 * bs) (D ++ H ++ Z) 0 bs (2 * bs)
                    (2 * bs) (3 * bs)
                  rw [show (([H, Z] : List (List α)).length) = 2 from rfl]
                  have h2 : 3 * (2 * bs) ≤ 9 * bs * 2 := by
                    have h3 : 3 * (2 * bs) = 6 * bs := by rw [← Nat.mul_assoc]
                    have h9 : 9 * bs * 2 = 18 * bs := by
                      rw [Nat.mul_assoc, Nat.mul_comm bs 2, ← Nat.mul_assoc]
                    rw [h3, h9]
                    exact Nat.mul_le_mul_right bs (by decide : 6 ≤ 18)
                  omega
              | cons W rest3 =>
                  rw [pairwiseGoC_three]
                  dsimp only
                  have h1 := mergeSwapLoopC_mv_le proj (2 * bs) (D ++ H ++ Z) 0 bs (2 * bs)
                    (2 * bs) (3 * bs)
                  have h2 := ih (done ++ [(mergeTwo proj H Z).take bs]) D
                    ((mergeTwo proj H Z).drop bs :: W :: rest3)
                  have hcomb : 3 * (2 * bs) + 3 * bs ≤ 9 * bs := by
                    have h3 : 3 * (2 * bs) = 6 * bs := by rw [← Nat.mul_assoc]
                    omega
                  simp only [Cost.mv_add, Cost.mv_mvN] at *
                  rw [show (H :: Z :: W :: rest3).length =
                    ((mergeTwo proj H Z).drop bs :: W :: rest3).length + 1 from rfl, Nat.mul_succ]
                  omega

theorem pairwiseC_cmp_le (proj : α → β) (bs : Nat) (blks : List (List α)) :
    (pairwiseC proj bs blks).2.cmp ≤ 2 * bs * blks.length := by
  match blks with
  | [] => rw [pairwiseC.eq_1]; simp
  | b0 :: rest =>
      rw [pairwiseC.eq_2]
      have h := pairwiseGoC_cmp_le proj bs rest.length [] b0 rest
      rw [show (b0 :: rest).length = rest.length + 1 from rfl, Nat.mul_succ]
      omega

theorem pairwiseC_mv_le (proj : α → β) (bs : Nat) (blks : List (List α)) :
    (pairwiseC proj bs blks).2.mv ≤ 9 * bs * blks.length := by
  match blks with
  | [] => rw [pairwiseC.eq_1]; simp
  | b0 :: rest =>
      rw [pairwiseC.eq_2]
      have h := pairwiseGoC_mv_le proj bs rest.length [] b0 rest
      rw [show (b0 :: rest).length = rest.length + 1 from rfl, Nat.mul_succ]
      omega

/-! ## The whole pipeline -/

/-- Cost of the C++ `inplace_unstable_merge`.  It is a loop-level simulation of the same
data structures: the alignment `std::rotate`, the two block phases, the tail
`bubble_sort` and the final `inplace_merge_with_rotation`.  The *result* of the pipeline
is the model's (`Tcs.unstableMerge`); only the operation counts are simulated here. -/
def unstableMergeCost (proj : α → β) (l : List α) (k : Nat) : Cost :=
  if l.length ≤ 1 then 0
  else
    let bs := Nat.sqrt l.length
    let la := k / bs * bs
    let ra := (l.length - k) / bs * bs
    let al := la + ra
    let A1 := l.take la
    let B1 := (l.drop k).take ra
    let rotL := rotRange l la k (k + ra)
    let blks0 := chunks bs (la / bs) A1 ++ chunks bs (ra / bs) B1
    let blks1 := (selSortC proj bs blks0).1
    let blks2 := (pairwiseC proj bs blks1).1
    let l2 := blks2.flatten ++ (rotL.drop al)
    let l3 := l2.take (al - bs) ++ bubbleSort proj (l2.drop (al - bs))
    -- `std::ranges::rotate(first + la, mid, mid + ra)` rotates `[la, k + ra)`, whose
    -- length is `k + ra - la = ra + k % bs`.
    Cost.rot (ra + k % bs)
      + (selSortC proj bs blks0).2
      + (pairwiseC proj bs blks1).2
      + (bubbleSortC proj (l2.drop (al - bs))).2
      + (mergeByRotationC proj l3 0 (al - bs) l.length).2

/-- The C++ `inplace_unstable_merge` paired with its cost.  The first component is the
verified model's result, so correctness is inherited from
`Tcs.unstableMerge_sorted_and_perm`. -/
def unstableMergeC (proj : α → β) (l : List α) (k : Nat) : List α × Cost :=
  (unstableMerge proj l k, unstableMergeCost proj l k)

theorem unstableMergeC_fst (proj : α → β) (l : List α) (k : Nat) :
    (unstableMergeC proj l k).1 = unstableMerge proj l k :=
  rfl

/-- The `Array`-level statement, matching the C++ signature
`inplace_unstable_merge(first, mid, last)`.  The array splice itself is not charged (the
C++ works in place); the cost is the one computed on `a.toList`. -/
def unstableMergeArrayC (proj : α → β) (a : Array α) (mid : Nat) : Array α × Cost :=
  (unstableMergeArray proj a mid, unstableMergeCost proj a.toList mid)

theorem unstableMergeArrayC_fst (proj : α → β) (a : Array α) (mid : Nat) :
    (unstableMergeArrayC proj a mid).1 = unstableMergeArray proj a mid :=
  rfl

/-! ## The linear bound -/

/-- `(bs + 1) ^ 2 = bs * (bs + 2) + 1`. -/
theorem um_sq_succ (bs : Nat) : (bs + 1) * (bs + 1) = bs * (bs + 2) + 1 := by
  rw [Nat.add_mul, Nat.mul_add bs bs 1, Nat.mul_one, Nat.one_mul, Nat.mul_add bs bs 2]
  omega

theorem um_sq_add_two_le {bs n : Nat} (hbs : 1 ≤ bs) (h1 : bs * bs ≤ n) (h2 : bs ≤ n) :
    (bs + 2) * (bs + 2) ≤ 9 * n := by
  rw [Nat.add_mul, Nat.mul_add bs bs 2, Nat.mul_add 2 bs 2]
  omega

theorem um_sq_three_add_one_le {bs n : Nat} (hbs : 1 ≤ bs) (h1 : bs * bs ≤ n) :
    (3 * bs + 1) * (3 * bs + 1) ≤ 16 * n := by
  rw [Nat.add_mul, Nat.mul_add (3 * bs) (3 * bs) 1, Nat.mul_one, Nat.one_mul,
    Nat.mul_mul_mul_comm 3 bs 3 bs]
  have := Nat.le_mul_self bs
  omega

theorem um_sq_three_le {bs n : Nat} (h1 : bs * bs ≤ n) : (3 * bs) * (3 * bs) ≤ 9 * n := by
  rw [Nat.mul_mul_mul_comm 3 bs 3 bs]
  exact Nat.mul_le_mul_left 9 h1

set_option maxHeartbeats 1000000 in
/-- **The whole pipeline is linear.**  With `bs = Nat.sqrt l.length` the aligned prefix
holds `al / bs ≤ bs + 2` whole blocks, so the selection sort costs `3 * tri (nb - 1)`
comparisons, the pairwise phase `2 * bs * nb`, the tail bubble sort
`tri (suffix - 1)` with `suffix ≤ 3 * bs`, and the final rotation merge
`tri (min (al - bs) (n - al + bs)) + n` with `min ... ≤ 3 * bs`.  Summed with the
`std::rotate` (`2 * ra`) this is at most `100 * n` in both units. -/
theorem unstableMergeCost_bounds (proj : α → β) (l : List α) (k : Nat)
    (hk : k ≤ l.length) :
    (unstableMergeCost proj l k).cmp ≤ 100 * l.length ∧
      (unstableMergeCost proj l k).mv ≤ 100 * l.length := by
  rw [unstableMergeCost]
  by_cases h : l.length ≤ 1
  · rw [ite_eq_left h]
    exact ⟨by simp, by simp⟩
  · rw [ite_eq_right h]
    dsimp only
    generalize hbsdef : Nat.sqrt l.length = bs
    generalize hladef : k / bs * bs = la
    generalize hradef : (l.length - k) / bs * bs = ra
    generalize haldef : la + ra = al
    generalize hA1def : l.take la = A1
    generalize hB1def : (l.drop k).take ra = B1
    generalize hrotdef : rotRange l la k (k + ra) = rotL
    generalize hblks0def : chunks bs (la / bs) A1 ++ chunks bs (ra / bs) B1 = blks0
    generalize hblks1def : (selSortC proj bs blks0).1 = blks1
    generalize hblks2def : (pairwiseC proj bs blks1).1 = blks2
    generalize hl2def : blks2.flatten ++ (rotL.drop al) = l2
    generalize hl3def : l2.take (al - bs) ++ bubbleSort proj (l2.drop (al - bs)) = l3
    have hn : 2 ≤ l.length := by omega
    have hbs : 0 < bs := by rw [← hbsdef]; exact sqrt_pos_of_pos (by omega)
    have hbs1 : 1 ≤ bs := hbs
    have hbs2 : bs * bs ≤ l.length := by rw [← hbsdef]; exact um_sqrt_mul_self_le l.length
    have hbsup : l.length < (bs + 1) * (bs + 1) := by
      rw [← hbsdef]; exact um_sqrt_lt_succ_sq l.length
    have hla : la ≤ k := by rw [← hladef]; exact Nat.div_mul_le_self k bs
    have hra : ra ≤ l.length - k := by
      rw [← hradef]; exact Nat.div_mul_le_self (l.length - k) bs
    have hbsle : bs ≤ l.length := by
      have h1 : bs ≤ bs * bs := by
        have h2 := Nat.mul_le_mul_left bs hbs1
        simpa using h2
      omega
    have halle : al ≤ l.length := by rw [← haldef]; omega
    have hA1len : A1.length = la := by
      rw [← hA1def, List.length_take, Nat.min_eq_left (by omega)]
    have hB1len : B1.length = ra := by
      rw [← hB1def, List.length_take, List.length_drop, Nat.min_eq_left (by omega)]
    have hla' : la / bs * bs = la := by
      rw [← hladef]
      exact Nat.div_mul_cancel ⟨k / bs, Nat.mul_comm _ _⟩
    have hra' : ra / bs * bs = ra := by
      rw [← hradef]
      exact Nat.div_mul_cancel ⟨(l.length - k) / bs, Nat.mul_comm _ _⟩
    have hblks0len : blks0.length = la / bs + ra / bs := by
      rw [← hblks0def, List.length_append, chunks_length A1 hbs (by omega),
        chunks_length B1 hbs (by omega)]
    have hblks0all : ∀ b ∈ blks0, b.length = bs := by
      intro b hb
      rw [← hblks0def, List.mem_append] at hb
      rcases hb with hb | hb
      · exact chunksAux_all_length hbs (la / bs) A1 (by omega) b hb
      · exact chunksAux_all_length hbs (ra / bs) B1 (by omega) b hb
    have hflat0 : blks0.flatten.length = al := by
      rw [← hblks0def, List.flatten_append, chunks_flatten, chunks_flatten, hla', hra',
        List.take_of_length_le (by omega), List.take_of_length_le (by omega),
        List.length_append, hA1len, hB1len, ← haldef]
    have hblksmul : blks0.length * bs = al := by
      have h1 := length_flatten_eq hblks0all
      omega
    have hnb : blks0.length ≤ bs + 2 := by
      have h1 : blks0.length * bs ≤ bs * (bs + 2) := by
        have h4 : (bs + 1) * (bs + 1) = bs * (bs + 2) + 1 := um_sq_succ bs
        omega
      have h5 : bs * blks0.length ≤ bs * (bs + 2) := by
        rw [Nat.mul_comm bs blks0.length]; exact h1
      exact Nat.le_of_mul_le_mul_left h5 hbs
    have hblks1len : blks1.length = blks0.length := by
      rw [← hblks1def]; exact selSortC_length proj bs blks0
    have hblks1flat : blks1.flatten.length = al := by
      rw [← hblks1def]
      exact (List.Perm.flatten (selSortC_perm proj bs blks0)).length_eq.trans hflat0
    have hblks2flat : blks2.flatten.length = al := by
      rw [← hblks2def]
      exact (pairwiseC_flatten_length proj bs blks1).trans hblks1flat
    have hrotlen : rotL.length = l.length := by
      rw [← hrotdef]
      exact rotRange_length (by omega) (by omega) (by omega)
    have hl2len : l2.length = l.length := by
      rw [← hl2def, List.length_append, hblks2flat, List.length_drop, hrotlen]
      omega
    have hkla : k - la = k % bs := by
      rw [← hladef, Nat.mul_comm (k / bs) bs, ← Nat.mod_eq_sub_mul_div]
    have hnra : (l.length - k) - ra = (l.length - k) % bs := by
      rw [← hradef, Nat.mul_comm ((l.length - k) / bs) bs, ← Nat.mod_eq_sub_mul_div]
    have hmodk : k % bs < bs := Nat.mod_lt k hbs
    have hmodn : (l.length - k) % bs < bs := Nat.mod_lt _ hbs
    have hnal : l.length - al ≤ 2 * bs := by
      have hsplit : l.length - al = (k - la) + ((l.length - k) - ra) := by
        rw [← haldef]; omega
      omega
    have hsuf : l.length - (al - bs) ≤ 3 * bs := by omega
    have hsuf2 : (l2.drop (al - bs)).length ≤ 3 * bs := by
      rw [List.length_drop, hl2len]; exact hsuf
    have hbubble_cmp : (bubbleSortC proj (l2.drop (al - bs))).2.cmp ≤ 9 * l.length := by
      have h1 : tri ((l2.drop (al - bs)).length - 1) ≤ 9 * l.length := by
        have h2 := tri_pred_le_sq ((l2.drop (al - bs)).length)
        have h3 : (l2.drop (al - bs)).length * (l2.drop (al - bs)).length ≤
            (3 * bs) * (3 * bs) := Nat.mul_self_le_mul_self hsuf2
        have h4 : (3 * bs) * (3 * bs) ≤ 9 * l.length := um_sq_three_le hbs2
        omega
      have h5 := bubbleSortC_cmp proj (l2.drop (al - bs))
      omega
    have hbubble_mv : (bubbleSortC proj (l2.drop (al - bs))).2.mv ≤ 27 * l.length := by
      have h1 : tri ((l2.drop (al - bs)).length - 1) ≤ 9 * l.length := by
        have h2 := tri_pred_le_sq ((l2.drop (al - bs)).length)
        have h3 : (l2.drop (al - bs)).length * (l2.drop (al - bs)).length ≤
            (3 * bs) * (3 * bs) := Nat.mul_self_le_mul_self hsuf2
        have h4 : (3 * bs) * (3 * bs) ≤ 9 * l.length := um_sq_three_le hbs2
        omega
      have h5 := bubbleSortC_mv_le proj (l2.drop (al - bs))
      omega
    have hsel_cmp : (selSortC proj bs blks0).2.cmp ≤ 27 * l.length := by
      have h1 : blks0.length * blks0.length ≤ 9 * l.length := by
        have h2 : blks0.length * blks0.length ≤ (bs + 2) * (bs + 2) :=
          Nat.mul_self_le_mul_self hnb
        have h3 : (bs + 2) * (bs + 2) ≤ 9 * l.length := um_sq_add_two_le hbs1 hbs2 hbsle
        omega
      have h4 := tri_pred_le_sq blks0.length
      have h5 := selSortC_cmp_le proj bs blks0
      omega
    have hsel_mv : (selSortC proj bs blks0).2.mv ≤ 3 * l.length := by
      have h1 : bs * (blks0.length - 1) ≤ al := by
        have h2 : bs * (blks0.length - 1) ≤ bs * blks0.length :=
          Nat.mul_le_mul_left bs (Nat.sub_le _ _)
        have h3 : bs * blks0.length = al := by rw [Nat.mul_comm]; exact hblksmul
        omega
      have h4 := selSortC_mv_le proj bs blks0
      rw [Nat.mul_assoc] at h4
      omega
    have hpair_cmp : (pairwiseC proj bs blks1).2.cmp ≤ 2 * l.length := by
      have h1 : bs * blks1.length = al := by
        rw [hblks1len, Nat.mul_comm]; exact hblksmul
      have h2 := pairwiseC_cmp_le proj bs blks1
      rw [Nat.mul_assoc] at h2
      omega
    have hpair_mv : (pairwiseC proj bs blks1).2.mv ≤ 9 * l.length := by
      have h1 : bs * blks1.length = al := by
        rw [hblks1len, Nat.mul_comm]; exact hblksmul
      have h2 := pairwiseC_mv_le proj bs blks1
      rw [Nat.mul_assoc] at h2
      omega
    have hmin : min (al - bs) (l.length - (al - bs)) ≤ 3 * bs :=
      Nat.le_trans (Nat.min_le_right _ _) hsuf
    have htri : tri (min (al - bs) (l.length - (al - bs))) ≤ 16 * l.length := by
      have h1 := tri_mono hmin
      have h2 := tri_le_sq (3 * bs)
      have h3 : (3 * bs + 1) * (3 * bs + 1) ≤ 16 * l.length :=
        um_sq_three_add_one_le (bs := bs) (n := l.length) hbs1 hbs2
      omega
    have hmerge_cmp : (mergeByRotationC proj l3 0 (al - bs) l.length).2.cmp ≤
        17 * l.length := by
      have h1 := mergeByRotationC_cmp_le proj l3 0 (al - bs) l.length
      rw [Nat.sub_zero, Nat.sub_zero] at h1
      omega
    have hmerge_mv : (mergeByRotationC proj l3 0 (al - bs) l.length).2.mv ≤
        34 * l.length := by
      have h1 := mergeByRotationC_mv_le proj l3 0 (al - bs) l.length
      rw [Nat.sub_zero, Nat.sub_zero] at h1
      omega
    have hra_le : ra ≤ l.length := by omega
    have hmod_le : k % bs ≤ l.length := by omega
    simp only [Cost.cmp_add, Cost.cmp_rot, Cost.mv_add, Cost.mv_rot]
    exact ⟨by omega, by omega⟩

theorem unstableMergeCost_cmp_le (proj : α → β) (l : List α) (k : Nat)
    (hk : k ≤ l.length) :
    (unstableMergeCost proj l k).cmp ≤ 100 * l.length :=
  (unstableMergeCost_bounds proj l k hk).1

theorem unstableMergeCost_mv_le (proj : α → β) (l : List α) (k : Nat)
    (hk : k ≤ l.length) :
    (unstableMergeCost proj l k).mv ≤ 100 * l.length :=
  (unstableMergeCost_bounds proj l k hk).2

theorem unstableMergeC_cmp_le (proj : α → β) (l : List α) (k : Nat)
    (hk : k ≤ l.length) :
    (unstableMergeC proj l k).2.cmp ≤ 100 * l.length :=
  unstableMergeCost_cmp_le proj l k hk

theorem unstableMergeC_mv_le (proj : α → β) (l : List α) (k : Nat)
    (hk : k ≤ l.length) :
    (unstableMergeC proj l k).2.mv ≤ 100 * l.length :=
  unstableMergeCost_mv_le proj l k hk

/-- `inplace_unstable_merge` is `O(n)` in both units.  Because a fixed split index `k`
must satisfy `k ≤ l.length`, the family is indexed by a split function that respects the
precondition. -/
theorem unstableMergeC_bigO (proj : α → β) (kf : List α → Nat)
    (hk : ∀ l, kf l ≤ l.length) :
    CostBigOWith 100 List.length (fun l => (unstableMergeC proj l (kf l)).2) (fun n => n) := by
  intro l
  show (unstableMergeC proj l (kf l)).2 ≤ Cost.const (100 * l.length)
  exact Cost.le_const (unstableMergeC_cmp_le proj l (kf l) (hk l))
    (unstableMergeC_mv_le proj l (kf l) (hk l))

/-- `inplace_unstable_merge` is `O(n)` with the split index part of the input, so the
precondition `k ≤ l.length` is a property of the family member. -/
theorem unstableMergeC_bigO' (proj : α → β) :
    CostBigOWith 100 (fun p : {p : List α × Nat // p.2 ≤ p.1.length} => p.1.1.length)
      (fun p => (unstableMergeC proj p.1.1 p.1.2).2) (fun n => n) := by
  intro p
  exact Cost.le_const (unstableMergeC_cmp_le proj p.1.1 p.1.2 p.2)
    (unstableMergeC_mv_le proj p.1.1 p.1.2 p.2)

theorem unstableMergeArrayC_cmp_le (proj : α → β) (a : Array α) (mid : Nat)
    (hmid : mid ≤ a.size) :
    (unstableMergeArrayC proj a mid).2.cmp ≤ 100 * a.size := by
  have h := unstableMergeCost_cmp_le proj a.toList mid (by simpa using hmid)
  rwa [Array.length_toList] at h

theorem unstableMergeArrayC_mv_le (proj : α → β) (a : Array α) (mid : Nat)
    (hmid : mid ≤ a.size) :
    (unstableMergeArrayC proj a mid).2.mv ≤ 100 * a.size := by
  have h := unstableMergeCost_mv_le proj a.toList mid (by simpa using hmid)
  rwa [Array.length_toList] at h

/-- The array entry point (the C++ signature) is `O(n)`, with the split index part of the
input. -/
theorem unstableMergeArrayC_bigO (proj : α → β) :
    CostBigOWith 100 (fun p : {p : Array α × Nat // p.2 ≤ p.1.size} => p.1.1.size)
      (fun p => (unstableMergeArrayC proj p.1.1 p.1.2).2) (fun n => n) := by
  intro p
  exact Cost.le_const (unstableMergeArrayC_cmp_le proj p.1.1 p.1.2 p.2)
    (unstableMergeArrayC_mv_le proj p.1.1 p.1.2 p.2)

end Tcs
