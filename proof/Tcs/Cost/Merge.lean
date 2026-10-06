/-
  Cost of the two merge primitives of the in-place unstable merge
  (`include/tcs/inplace/unstable_merge.hpp`): `merge_with_swap` and
  `inplace_merge_with_rotation`.

  Each counting copy has literally the same control flow as the verified model
  `Tcs.Merge`, so the agreement theorems `_fst` are proved by the same induction as
  the model (the counting functions only thread a `Cost` through).

  Counting rules (`Tcs.Cost`):
  * `merge_with_swap`: one `std::swap` (`Cost.swap`, 3 moves) per turn, plus one key
    comparison on every turn that is not the "right run exhausted" shortcut;
  * `inplace_merge_with_rotation`: one key comparison per scan step (`scanRight` /
    `scanLeft`) and `Cost.rot m` (2 moves per element) per `std::rotate`.
-/
import Tcs.Cost
import Tcs.Merge

namespace Tcs

variable {α : Type u} {β : Type v} [Cmp β]

/-! ## `merge_with_swap` -/

/-- `Tcs.Merge.mergeSwapLoop` carrying its cost. Every turn swaps once; a turn that is
not the "right run exhausted" shortcut also performs one key comparison. -/
def mergeSwapLoopC (proj : α → β) :
    Nat → List α → Nat → Nat → Nat → Nat → Nat → List α × Cost
  | 0, l, _, _, _, _, _ => (l, 0)
  | fuel + 1, l, out, left, mid, right, last =>
      if _ : left < mid ∨ right < last then
        if _ : right = last then
          if hl : left < l.length then
            let r := mergeSwapLoopC proj fuel (Bfprt.swapAt l out left) (out + 1) (left + 1)
              mid right last
            (r.1, r.2 + Cost.swap)
          else (l, 0)
        else
          if hl : left < l.length then
            if hr : right < l.length then
              if _ : left < mid ∧ Cmp.ble (proj l[left]) (proj l[right]) then
                let r := mergeSwapLoopC proj fuel (Bfprt.swapAt l out left) (out + 1) (left + 1)
                  mid right last
                (r.1, r.2 + (Cost.cmp1 + Cost.swap))
              else
                let r := mergeSwapLoopC proj fuel (Bfprt.swapAt l out right) (out + 1) left mid
                  (right + 1) last
                (r.1, r.2 + (Cost.cmp1 + Cost.swap))
            else (l, 0)
          else (l, 0)
      else (l, 0)

/-- Agreement of the counting loop with the model.  The two loops have syntactically
the same branch conditions on the same arguments, so no length hypothesis is needed. -/
theorem mergeSwapLoopC_fst' (proj : α → β) :
    ∀ fuel l out left mid right last,
      (mergeSwapLoopC proj fuel l out left mid right last).1 =
        mergeSwapLoop proj fuel l out left mid right last := by
  intro fuel
  induction fuel with
  | zero => intro l out left mid right last; rfl
  | succ fuel ih =>
      intro l out left mid right last
      rw [mergeSwapLoopC.eq_2, mergeSwapLoop.eq_2]
      by_cases hg : left < mid ∨ right < last
      · rw [dite_eq_left hg, dite_eq_left hg]
        by_cases hre : right = last
        · rw [dite_eq_left hre, dite_eq_left hre]
          by_cases hl : left < l.length
          · rw [dite_eq_left hl, dite_eq_left hl]
            dsimp only
            exact ih _ _ _ _ _ _
          · rw [dite_eq_right hl, dite_eq_right hl]
        · rw [dite_eq_right hre, dite_eq_right hre]
          by_cases hl : left < l.length
          · rw [dite_eq_left hl, dite_eq_left hl]
            by_cases hr : right < l.length
            · rw [dite_eq_left hr, dite_eq_left hr]
              by_cases hb : left < mid ∧ Cmp.ble (proj l[left]) (proj l[right]) = true
              · rw [dite_eq_left hb, dite_eq_left hb]
                dsimp only
                exact ih _ _ _ _ _ _
              · rw [dite_eq_right hb, dite_eq_right hb]
                dsimp only
                exact ih _ _ _ _ _ _
            · rw [dite_eq_right hr, dite_eq_right hr]
          · rw [dite_eq_right hl, dite_eq_right hl]
      · rw [dite_eq_right hg, dite_eq_right hg]

/-- C++'s `merge_with_swap` with its cost. -/
def mergeWithSwapC (proj : α → β) (l : List α) (output first mid last : Nat) :
    List α × Cost :=
  mergeSwapLoopC proj (last - first) l output first mid mid last

theorem mergeWithSwapC_fst (proj : α → β) (l : List α) (output first mid last : Nat) :
    (mergeWithSwapC proj l output first mid last).1 =
      mergeWithSwap proj l output first mid last :=
  mergeSwapLoopC_fst' proj (last - first) l output first mid mid last

/-- At most one key comparison per turn. -/
theorem mergeSwapLoopC_cmp_le (proj : α → β) :
    ∀ fuel l out left mid right last,
      (mergeSwapLoopC proj fuel l out left mid right last).2.cmp ≤ fuel := by
  intro fuel
  induction fuel with
  | zero => intro l out left mid right last; rw [mergeSwapLoopC.eq_1]; simp
  | succ fuel ih =>
      intro l out left mid right last
      rw [mergeSwapLoopC.eq_2]
      by_cases hg : left < mid ∨ right < last
      · rw [dite_eq_left hg]
        by_cases hre : right = last
        · rw [dite_eq_left hre]
          by_cases hl : left < l.length
          · rw [dite_eq_left hl]
            have h := ih (Bfprt.swapAt l out left) (out + 1) (left + 1) mid right last
            simp
            omega
          · rw [dite_eq_right hl]; simp
        · rw [dite_eq_right hre]
          by_cases hl : left < l.length
          · rw [dite_eq_left hl]
            by_cases hr : right < l.length
            · rw [dite_eq_left hr]
              by_cases hb : left < mid ∧ Cmp.ble (proj l[left]) (proj l[right]) = true
              · rw [dite_eq_left hb]
                have h := ih (Bfprt.swapAt l out left) (out + 1) (left + 1) mid right last
                simp
                omega
              · rw [dite_eq_right hb]
                have h := ih (Bfprt.swapAt l out right) (out + 1) left mid (right + 1) last
                simp
                omega
            · rw [dite_eq_right hr]; simp
          · rw [dite_eq_right hl]; simp
      · rw [dite_eq_right hg]; simp

/-- Exactly one swap (3 moves) per turn. -/
theorem mergeSwapLoopC_mv_le (proj : α → β) :
    ∀ fuel l out left mid right last,
      (mergeSwapLoopC proj fuel l out left mid right last).2.mv ≤ 3 * fuel := by
  intro fuel
  induction fuel with
  | zero => intro l out left mid right last; rw [mergeSwapLoopC.eq_1]; simp
  | succ fuel ih =>
      intro l out left mid right last
      rw [mergeSwapLoopC.eq_2]
      by_cases hg : left < mid ∨ right < last
      · rw [dite_eq_left hg]
        by_cases hre : right = last
        · rw [dite_eq_left hre]
          by_cases hl : left < l.length
          · rw [dite_eq_left hl]
            have h := ih (Bfprt.swapAt l out left) (out + 1) (left + 1) mid right last
            simp
            omega
          · rw [dite_eq_right hl]; simp
        · rw [dite_eq_right hre]
          by_cases hl : left < l.length
          · rw [dite_eq_left hl]
            by_cases hr : right < l.length
            · rw [dite_eq_left hr]
              by_cases hb : left < mid ∧ Cmp.ble (proj l[left]) (proj l[right]) = true
              · rw [dite_eq_left hb]
                have h := ih (Bfprt.swapAt l out left) (out + 1) (left + 1) mid right last
                simp
                omega
              · rw [dite_eq_right hb]
                have h := ih (Bfprt.swapAt l out right) (out + 1) left mid (right + 1) last
                simp
                omega
            · rw [dite_eq_right hr]; simp
          · rw [dite_eq_right hl]; simp
      · rw [dite_eq_right hg]; simp

theorem mergeWithSwapC_cmp_le (proj : α → β) (l : List α) (output first mid last : Nat) :
    (mergeWithSwapC proj l output first mid last).2.cmp ≤ last - first :=
  mergeSwapLoopC_cmp_le proj (last - first) l output first mid mid last

theorem mergeWithSwapC_mv_le (proj : α → β) (l : List α) (output first mid last : Nat) :
    (mergeWithSwapC proj l output first mid last).2.mv ≤ 3 * (last - first) :=
  mergeSwapLoopC_mv_le proj (last - first) l output first mid mid last

/-- `min (f + 1) n = 1 + min f (n - 1)` for `n ≥ 1`: one more turn of budget is the
current turn plus the rest. -/
theorem min_succ_pred {f n : Nat} (hn : 1 ≤ n) : min (f + 1) n = 1 + min f (n - 1) := by
  omega

/-- Shifting the consumed element forward: `a + (c - (b + 1))` is one less than
`a + (c - b)` as soon as `b < c`.  Kept as a pure `Nat` lemma so that `omega` never
sees the surrounding list/`Cmp` hypotheses. -/
theorem add_sub_succ {a b c : Nat} (h : b < c) : a + (c - (b + 1)) = (a + (c - b)) - 1 := by
  omega

/-- The loop runs exactly `min fuel remaining` turns, where `remaining` counts the
elements still to be consumed, and swaps on every turn. -/
theorem mergeSwapLoopC_mv (proj : α → β) :
    ∀ fuel l out left mid right last, left ≤ mid → mid ≤ right → right ≤ last →
      last ≤ l.length →
      (mergeSwapLoopC proj fuel l out left mid right last).2.mv =
        3 * min fuel ((mid - left) + (last - right)) := by
  intro fuel
  induction fuel with
  | zero =>
      intro l out left mid right last _ _ _ _
      rw [mergeSwapLoopC.eq_1]
      simp
  | succ fuel ih =>
      intro l out left mid right last hlm hmr hrl hlast
      rw [mergeSwapLoopC.eq_2]
      by_cases hg : left < mid ∨ right < last
      · rw [dite_eq_left hg]
        by_cases hre : right = last
        · rw [dite_eq_left hre]
          have hleft : left < mid := by
            rcases hg with h | h
            · exact h
            · rw [hre] at h
              exact absurd h (Nat.lt_irrefl last)
          have hleftlen : left < l.length := by omega
          rw [dite_eq_left hleftlen]
          have hih := ih (Bfprt.swapAt l out left) (out + 1) (left + 1) mid right last
            (by omega) hmr hrl (by rw [Bfprt.swapAt_length]; exact hlast)
          have hrem : 1 ≤ (mid - left) + (last - right) := by omega
          have hnew : (mid - (left + 1)) + (last - right) =
              ((mid - left) + (last - right)) - 1 := by omega
          simp
          rw [hih, hnew, min_succ_pred hrem]
          omega
        · rw [dite_eq_right hre]
          by_cases hl : left < l.length
          · rw [dite_eq_left hl]
            by_cases hr : right < l.length
            · rw [dite_eq_left hr]
              by_cases hb : left < mid ∧ Cmp.ble (proj l[left]) (proj l[right]) = true
              · rw [dite_eq_left hb]
                have hleft : left < mid := hb.1
                have hih := ih (Bfprt.swapAt l out left) (out + 1) (left + 1) mid right last
                  (by omega) hmr hrl (by rw [Bfprt.swapAt_length]; exact hlast)
                have hrem : 1 ≤ (mid - left) + (last - right) := by omega
                have hnew : (mid - (left + 1)) + (last - right) =
                    ((mid - left) + (last - right)) - 1 := by omega
                simp
                rw [hih, hnew, min_succ_pred hrem]
                omega
              · rw [dite_eq_right hb]
                have hrlt : right < last := Nat.lt_of_le_of_ne hrl hre
                have hih := ih (Bfprt.swapAt l out right) (out + 1) left mid (right + 1) last
                  hlm (Nat.le_succ_of_le hmr) (Nat.succ_le_of_lt hrlt)
                  (by rw [Bfprt.swapAt_length]; exact hlast)
                have hrem : 1 ≤ (mid - left) + (last - right) := by
                  rcases hg with h | h
                  · exact Nat.le_trans (Nat.succ_le_of_lt (Nat.sub_pos_of_lt h))
                      (Nat.le_add_right _ _)
                  · exact Nat.le_trans (Nat.succ_le_of_lt (Nat.sub_pos_of_lt h))
                      (Nat.le_add_left _ _)
                have hnew : (mid - left) + (last - (right + 1)) =
                    ((mid - left) + (last - right)) - 1 := add_sub_succ hrlt
                simp
                rw [hih, hnew, min_succ_pred hrem]
                omega
            · rw [dite_eq_right hr]; omega
          · rw [dite_eq_right hl]; omega
      · rw [dite_eq_right hg]
        have hle : mid ≤ left := Nat.le_of_not_lt (fun h => hg (Or.inl h))
        have hre : last ≤ right := Nat.le_of_not_lt (fun h => hg (Or.inr h))
        have hrem0 : (mid - left) + (last - right) = 0 := by omega
        rw [hrem0, Nat.min_zero, Nat.mul_zero]
        rfl

theorem mergeWithSwapC_mv (proj : α → β) (l : List α) (output first mid last : Nat)
    (hfm : first ≤ mid) (hml : mid ≤ last) (hlast : last ≤ l.length) :
    (mergeWithSwapC proj l output first mid last).2.mv = 3 * (last - first) := by
  have h := mergeSwapLoopC_mv proj (last - first) l output first mid mid last hfm
    (Nat.le_refl mid) hml hlast
  have hmin : min (last - first) ((mid - first) + (last - mid)) = last - first := by
    rw [show (mid - first) + (last - mid) = last - first by omega]
    exact Nat.min_self _
  rw [hmin] at h
  exact h

/-! ## The scans -/

/-- `Tcs.Merge.scanRight` carrying its cost: one comparison per element it examines. -/
def scanRightC (proj : α → β) (x : α) : Nat → List α → Nat → Nat → Nat × Cost
  | 0, _, sp, _ => (sp, 0)
  | fuel + 1, l, sp, last =>
      if _ : sp < last then
        if hl : sp < l.length then
          if Cmp.blt (proj l[sp]) (proj x) then
            ((scanRightC proj x fuel l (sp + 1) last).1,
              (scanRightC proj x fuel l (sp + 1) last).2 + Cost.cmp1)
          else (sp, 0)
        else (sp, 0)
      else (sp, 0)

/-- `Tcs.Merge.scanLeft` carrying its cost: one comparison per element it examines. -/
def scanLeftC (proj : α → β) (y : α) : Nat → List α → Nat → Nat → Nat × Cost
  | 0, _, sp, _ => (sp, 0)
  | fuel + 1, l, sp, first =>
      if _ : first < sp then
        if hl : sp - 1 < l.length then
          if Cmp.blt (proj y) (proj l[sp - 1]) then
            ((scanLeftC proj y fuel l (sp - 1) first).1,
              (scanLeftC proj y fuel l (sp - 1) first).2 + Cost.cmp1)
          else (sp, 0)
        else (sp, 0)
      else (sp, 0)

theorem scanRightC_fst (proj : α → β) (x : α) :
    ∀ fuel l sp last,
      (scanRightC proj x fuel l sp last).1 = scanRight proj x fuel l sp last := by
  intro fuel
  induction fuel with
  | zero => intro l sp last; rw [scanRightC.eq_1, scanRight.eq_1]
  | succ fuel ih =>
      intro l sp last
      rw [scanRightC.eq_2, scanRight.eq_2]
      by_cases h1 : sp < last
      · rw [dite_eq_left h1, dite_eq_left h1]
        by_cases h2 : sp < l.length
        · rw [dite_eq_left h2, dite_eq_left h2]
          by_cases h3 : Cmp.blt (proj l[sp]) (proj x) = true
          · rw [ite_eq_left h3, ite_eq_left h3]
            dsimp only
            exact ih l (sp + 1) last
          · rw [ite_eq_right h3, ite_eq_right h3]
        · rw [dite_eq_right h2, dite_eq_right h2]
      · rw [dite_eq_right h1, dite_eq_right h1]

theorem scanLeftC_fst (proj : α → β) (y : α) :
    ∀ fuel l sp first,
      (scanLeftC proj y fuel l sp first).1 = scanLeft proj y fuel l sp first := by
  intro fuel
  induction fuel with
  | zero => intro l sp first; rw [scanLeftC.eq_1, scanLeft.eq_1]
  | succ fuel ih =>
      intro l sp first
      rw [scanLeftC.eq_2, scanLeft.eq_2]
      by_cases h1 : first < sp
      · rw [dite_eq_left h1, dite_eq_left h1]
        by_cases h2 : sp - 1 < l.length
        · rw [dite_eq_left h2, dite_eq_left h2]
          by_cases h3 : Cmp.blt (proj y) (proj l[sp - 1]) = true
          · rw [ite_eq_left h3, ite_eq_left h3]
            dsimp only
            exact ih l (sp - 1) first
          · rw [ite_eq_right h3, ite_eq_right h3]
        · rw [dite_eq_right h2, dite_eq_right h2]
      · rw [dite_eq_right h1, dite_eq_right h1]

/-- Sharper scan accounting: the forward scan stops inside `[sp, last]` and performs at
most `(result - sp) + 1` comparisons (one per step taken plus the final failing one). -/
theorem scanRightC_bounds (proj : α → β) (x : α) :
    ∀ fuel l sp last, sp + fuel = last →
      sp ≤ (scanRightC proj x fuel l sp last).1 ∧
      (scanRightC proj x fuel l sp last).1 ≤ last ∧
      (scanRightC proj x fuel l sp last).2.cmp ≤
        ((scanRightC proj x fuel l sp last).1 - sp) + 1 ∧
      (scanRightC proj x fuel l sp last).2.mv = 0 := by
  intro fuel
  induction fuel with
  | zero =>
      intro l sp last hsp
      rw [scanRightC.eq_1]
      exact ⟨Nat.le_refl _, by omega, by simp, rfl⟩
  | succ fuel ih =>
      intro l sp last hsp
      rw [scanRightC.eq_2]
      by_cases h1 : sp < last
      · rw [dite_eq_left h1]
        by_cases h2 : sp < l.length
        · rw [dite_eq_left h2]
          by_cases h3 : Cmp.blt (proj l[sp]) (proj x) = true
          · rw [ite_eq_left h3]
            have hsp1 : sp + 1 + fuel = last := by omega
            obtain ⟨ha, hb, hc, hd⟩ := ih l (sp + 1) last hsp1
            refine ⟨by omega, hb, ?_, ?_⟩
            · simp only [Cost.cmp_add, Cost.cmp_cmp1]
              omega
            · simp only [Cost.mv_add, Cost.mv_cmp1]
              omega
          · rw [ite_eq_right h3]
            exact ⟨Nat.le_refl _, by omega, by simp, rfl⟩
        · rw [dite_eq_right h2]
          exact ⟨Nat.le_refl _, by omega, by simp, rfl⟩
      · rw [dite_eq_right h1]
        exact ⟨Nat.le_refl _, by omega, by simp, rfl⟩

/-- Sharper scan accounting: the backward scan stops inside `[first, sp]` and performs
at most `(sp - result) + 1` comparisons. -/
theorem scanLeftC_bounds (proj : α → β) (y : α) :
    ∀ fuel l sp first, sp = first + fuel →
      first ≤ (scanLeftC proj y fuel l sp first).1 ∧
      (scanLeftC proj y fuel l sp first).1 ≤ sp ∧
      (scanLeftC proj y fuel l sp first).2.cmp ≤
        (sp - (scanLeftC proj y fuel l sp first).1) + 1 ∧
      (scanLeftC proj y fuel l sp first).2.mv = 0 := by
  intro fuel
  induction fuel with
  | zero =>
      intro l sp first hsp
      rw [scanLeftC.eq_1]
      exact ⟨by omega, Nat.le_refl _, by simp, rfl⟩
  | succ fuel ih =>
      intro l sp first hsp
      rw [scanLeftC.eq_2]
      by_cases h1 : first < sp
      · rw [dite_eq_left h1]
        by_cases h2 : sp - 1 < l.length
        · rw [dite_eq_left h2]
          by_cases h3 : Cmp.blt (proj y) (proj l[sp - 1]) = true
          · rw [ite_eq_left h3]
            have hsp1 : sp - 1 = first + fuel := by omega
            obtain ⟨ha, hb, hc, hd⟩ := ih l (sp - 1) first hsp1
            refine ⟨ha, by omega, ?_, ?_⟩
            · simp only [Cost.cmp_add, Cost.cmp_cmp1]
              omega
            · simp only [Cost.mv_add, Cost.mv_cmp1]
              omega
          · rw [ite_eq_right h3]
            exact ⟨by omega, Nat.le_refl _, by simp, rfl⟩
        · rw [dite_eq_right h2]
          exact ⟨by omega, Nat.le_refl _, by simp, rfl⟩
      · rw [dite_eq_right h1]
        exact ⟨by omega, Nat.le_refl _, by simp, rfl⟩

/-! ## `inplace_merge_with_rotation` -/

/-- `Tcs.Merge.mergeLoop` carrying its cost: the scan of each turn and the rotation it
performs. -/
def mergeLoopC (proj : α → β) : Nat → List α → Nat → Nat → Nat → List α × Cost
  | 0, l, _, _, _ => (l, 0)
  | fuel + 1, l, first, mid, last =>
      if _ : first < mid ∧ mid < last then
        if _ : mid - first < last - mid then
          if hf : first < l.length then
            let r := scanRightC proj l[first] (last - mid) l mid last
            let sp := r.1
            let s := mergeLoopC proj fuel (rotRange l first mid sp) (first + (sp - mid) + 1) sp last
            (s.1, r.2 + Cost.rot (sp - first) + s.2)
          else (l, 0)
        else
          if hl : last - 1 < l.length then
            let r := scanLeftC proj l[last - 1] (mid - first) l mid first
            let sp := r.1
            let s := mergeLoopC proj fuel (rotRange l sp mid last) first sp (last - (mid - sp) - 1)
            (s.1, r.2 + Cost.rot (last - sp) + s.2)
          else (l, 0)
      else (l, 0)

/-- Agreement of the counting rotation loop with the model. -/
theorem mergeLoopC_fst (proj : α → β) :
    ∀ fuel l first mid last,
      (mergeLoopC proj fuel l first mid last).1 = mergeLoop proj fuel l first mid last := by
  intro fuel
  induction fuel with
  | zero => intro l first mid last; rfl
  | succ fuel ih =>
      intro l first mid last
      rw [mergeLoopC.eq_2, mergeLoop.eq_2]
      by_cases hg : first < mid ∧ mid < last
      · rw [dite_eq_left hg, dite_eq_left hg]
        by_cases hlr : mid - first < last - mid
        · rw [dite_eq_left hlr, dite_eq_left hlr]
          by_cases hf : first < l.length
          · rw [dite_eq_left hf, dite_eq_left hf]
            dsimp only
            rw [scanRightC_fst]
            exact ih _ _ _ _
          · rw [dite_eq_right hf, dite_eq_right hf]
        · rw [dite_eq_right hlr, dite_eq_right hlr]
          by_cases hl : last - 1 < l.length
          · rw [dite_eq_left hl, dite_eq_left hl]
            dsimp only
            rw [scanLeftC_fst]
            exact ih _ _ _ _
          · rw [dite_eq_right hl, dite_eq_right hl]
      · rw [dite_eq_right hg, dite_eq_right hg]

/-- Budget arithmetic of the left-turning branch: one turn consumes one unit of
`min a b` and `c + 1` units of the window, and the rotate costs `a + c`. -/
theorem left_budget {a b c w : Nat} (hc : c ≤ b) (hw : w = a + b) :
    a + c + (tri (min (a - 1) (b - c)) + (w - c - 1)) ≤ tri a + w := by
  have h1 : tri (min (a - 1) (b - c)) ≤ tri (a - 1) := tri_mono (Nat.min_le_left _ _)
  have h2 : tri a = a + tri (a - 1) := tri_eq_add_pred a
  omega

/-- Budget arithmetic of the right-turning branch. -/
theorem right_budget {a b c w : Nat} (hc : c ≤ a) (hw : w = a + b) :
    b + c + (tri (min (a - c) (b - 1)) + (w - c - 1)) ≤ tri b + w := by
  have h1 : tri (min (a - c) (b - 1)) ≤ tri (b - 1) := tri_mono (Nat.min_le_right _ _)
  have h2 : tri b = b + tri (b - 1) := tri_eq_add_pred b
  omega

set_option maxHeartbeats 1000000 in
/-- Per-state cost bound of the rotation loop: the comparisons are bounded by the
current window length and the moves by `2 * (tri (min a b) + window)`, where `a` and
`b` are the two run lengths.  The left branch decreases `min a b` by one and shrinks
the window by `(sp - mid) + 1`; the right branch is symmetric, so the budget
`tri (min a b) + window` is consumed exactly. -/
theorem mergeLoopC_cost_le (proj : α → β) :
    ∀ fuel l first mid last,
      (mergeLoopC proj fuel l first mid last).2.cmp ≤ last - first ∧
      (mergeLoopC proj fuel l first mid last).2.mv ≤
        2 * (tri (min (mid - first) (last - mid)) + (last - first)) := by
  intro fuel
  induction fuel with
  | zero =>
      intro l first mid last
      rw [mergeLoopC.eq_1]
      exact ⟨Nat.zero_le _, Nat.zero_le _⟩
  | succ fuel ih =>
      intro l first mid last
      rw [mergeLoopC.eq_2]
      by_cases hg : first < mid ∧ mid < last
      · rw [dite_eq_left hg]
        have hfm : first < mid := hg.1
        have hml : mid < last := hg.2
        by_cases hlr : mid - first < last - mid
        · rw [dite_eq_left hlr]
          by_cases hf : first < l.length
          · rw [dite_eq_left hf]
            dsimp only
            generalize hr : scanRightC proj l[first] (last - mid) l mid last = r
            have hb := scanRightC_bounds proj l[first] (last - mid) l mid last (by omega)
            rw [hr] at hb
            obtain ⟨hge, hle, hcmp, hmv⟩ := hb
            have hih := ih (rotRange l first mid r.1) (first + (r.1 - mid) + 1) r.1 last
            obtain ⟨hihc, hihm⟩ := hih
            have hrl : r.1 - first = (mid - first) + (r.1 - mid) := by omega
            have hminA : min (mid - first) (last - mid) = mid - first :=
              Nat.min_eq_left (Nat.le_of_lt hlr)
            have htriA : tri (mid - first) = (mid - first) + tri (mid - first - 1) :=
              tri_eq_add_pred _
            have hW' : last - (first + (r.1 - mid) + 1) =
                (last - first) - (r.1 - mid) - 1 := by omega
            have hM' : min (r.1 - (first + (r.1 - mid) + 1)) (last - r.1) =
                min (mid - first - 1) ((last - mid) - (r.1 - mid)) := by omega
            have htriM : tri (min (r.1 - (first + (r.1 - mid) + 1)) (last - r.1)) ≤
                tri (mid - first - 1) := by
              rw [hM']
              exact tri_mono (Nat.min_le_left _ _)
            rw [hW'] at hihc hihm
            rw [hM'] at hihm
            constructor
            · simp only [Cost.cmp_add, Cost.cmp_rot]
              omega
            · simp only [Cost.mv_add, Cost.mv_rot]
              rw [hmv, hrl, hminA, htriA]
              have hbud : (mid - first) + (r.1 - mid) +
                  (tri (min (mid - first - 1) ((last - mid) - (r.1 - mid))) +
                    ((last - first) - (r.1 - mid) - 1)) ≤
                  tri (mid - first) + (last - first) :=
                left_budget (by omega) (by omega)
              omega
          · rw [dite_eq_right hf]
            exact ⟨Nat.zero_le _, Nat.zero_le _⟩
        · rw [dite_eq_right hlr]
          by_cases hl : last - 1 < l.length
          · rw [dite_eq_left hl]
            dsimp only
            generalize hr : scanLeftC proj l[last - 1] (mid - first) l mid first = r
            have hb := scanLeftC_bounds proj l[last - 1] (mid - first) l mid first (by omega)
            rw [hr] at hb
            obtain ⟨hge, hle, hcmp, hmv⟩ := hb
            have hml' : last - mid ≤ mid - first := Nat.le_of_not_lt hlr
            have hih := ih (rotRange l r.1 mid last) first r.1 (last - (mid - r.1) - 1)
            obtain ⟨hihc, hihm⟩ := hih
            have hrl : last - r.1 = (last - mid) + (mid - r.1) := by omega
            have hminB : min (mid - first) (last - mid) = last - mid := Nat.min_eq_right hml'
            have htriB : tri (last - mid) = (last - mid) + tri (last - mid - 1) :=
              tri_eq_add_pred _
            have hW'' : last - (mid - r.1) - 1 - first =
                (last - first) - (mid - r.1) - 1 := by omega
            have hM'' : min (r.1 - first) (last - (mid - r.1) - 1 - r.1) =
                min ((mid - first) - (mid - r.1)) ((last - mid) - 1) := by omega
            have htriM : tri (min (r.1 - first) (last - (mid - r.1) - 1 - r.1)) ≤
                tri (last - mid - 1) := by
              rw [hM'']
              exact tri_mono (Nat.min_le_right _ _)
            rw [hW''] at hihc hihm
            rw [hM''] at hihm
            constructor
            · simp only [Cost.cmp_add, Cost.cmp_rot]
              omega
            · simp only [Cost.mv_add, Cost.mv_rot]
              rw [hmv, hrl, hminB, htriB]
              have hbud : (last - mid) + (mid - r.1) +
                  (tri (min ((mid - first) - (mid - r.1)) ((last - mid) - 1)) +
                    ((last - first) - (mid - r.1) - 1)) ≤
                  tri (last - mid) + (last - first) :=
                right_budget (by omega) (by omega)
              omega
          · rw [dite_eq_right hl]
            exact ⟨Nat.zero_le _, Nat.zero_le _⟩
      · rw [dite_eq_right hg]
        exact ⟨Nat.zero_le _, Nat.zero_le _⟩

/-- C++'s `inplace_merge_with_rotation` with its cost. -/
def mergeByRotationC (proj : α → β) (l : List α) (first mid last : Nat) : List α × Cost :=
  mergeLoopC proj (last - first) l first mid last

theorem mergeByRotationC_fst (proj : α → β) (l : List α) (first mid last : Nat) :
    (mergeByRotationC proj l first mid last).1 = mergeByRotation proj l first mid last :=
  mergeLoopC_fst proj (last - first) l first mid last

theorem mergeByRotationC_cmp_le (proj : α → β) (l : List α) (first mid last : Nat) :
    (mergeByRotationC proj l first mid last).2.cmp ≤
      tri (min (mid - first) (last - mid)) + (last - first) := by
  rw [mergeByRotationC]
  have h := (mergeLoopC_cost_le proj (last - first) l first mid last).1
  omega

theorem mergeByRotationC_mv_le (proj : α → β) (l : List α) (first mid last : Nat) :
    (mergeByRotationC proj l first mid last).2.mv ≤
      2 * (tri (min (mid - first) (last - mid)) + (last - first)) :=
  (mergeLoopC_cost_le proj (last - first) l first mid last).2


/-- With two non-empty runs, `tri (min a b) + (a + b) ≤ (a + b) * (a + b)`: this is
the `O(n^2)` bound of the rotation loop. -/
theorem tri_min_add_le_sq {a b : Nat} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    tri (min a b) + (a + b) ≤ (a + b) * (a + b) := by
  have h1 : tri (min a b) ≤ (min a b) * (min a b) := tri_le_mul_self _
  have h2 : (min a b) * (min a b) ≤ (min a b) * (a + b) :=
    Nat.mul_le_mul_left _ (by omega)
  have h3 : ((min a b) + 1) * (a + b) ≤ (a + b) * (a + b) :=
    Nat.mul_le_mul_right _ (by omega)
  have h4 : (min a b) * (a + b) + (a + b) = ((min a b) + 1) * (a + b) := by
    rw [Nat.add_mul, Nat.one_mul]
  omega

/-- An already-ordered run pair costs nothing: the loop guard is false. -/
theorem mergeLoopC_cost_zero (proj : α → β) :
    ∀ fuel l first mid last, ¬(first < mid ∧ mid < last) →
      (mergeLoopC proj fuel l first mid last).2 = 0 := by
  intro fuel
  induction fuel with
  | zero =>
      intro l first mid last _
      rw [mergeLoopC.eq_1]
  | succ fuel _ih =>
      intro l first mid last hg
      rw [mergeLoopC.eq_2, dite_eq_right hg]

/-- The rotation merge is `O(n^2)` in both units on the whole input family: the window
`n = last - first` bounds both the comparison count and (through `tri (min a b)`) the
move count.  The index is `(l, (first, (mid, last)))` with size `last - first`; when
`first < mid < last` fails the guard stops the loop at cost zero. -/
theorem mergeByRotationC_bigO (proj : α → β) :
    CostBigOWith 2 (fun p : List α × Nat × Nat × Nat => p.2.2.2 - p.2.1)
      (fun p => (mergeByRotationC proj p.1 p.2.1 p.2.2.1 p.2.2.2).2) (fun n => n * n) := by
  intro p
  obtain ⟨l, first, mid, last⟩ := p
  show (mergeByRotationC proj l first mid last).2 ≤
    Cost.const (2 * ((last - first) * (last - first)))
  by_cases hg : first < mid ∧ mid < last
  · have hcmp := mergeByRotationC_cmp_le proj l first mid last
    have hmv := mergeByRotationC_mv_le proj l first mid last
    have htri := tri_min_add_le_sq (a := mid - first) (b := last - mid) (by omega) (by omega)
    have hsum : (mid - first) + (last - mid) = last - first := by omega
    rw [hsum] at htri
    refine Cost.le_const ?_ ?_
    · omega
    · omega
  · have hz : (mergeByRotationC proj l first mid last).2 = 0 :=
      mergeLoopC_cost_zero proj (last - first) l first mid last hg
    rw [hz]
    exact Cost.zero_le _

end Tcs
