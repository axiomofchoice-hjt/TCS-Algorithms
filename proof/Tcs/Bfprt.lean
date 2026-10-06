/-
  BFPRT (median of medians) selection (`include/tcs/bfprt.hpp`), proved correct.

  Modelling. The C++ routine walks the iterator range `[first, last)` and never
  reads outside it, so the model works on that range's element list; `mid` becomes
  the rank `k = mid - first` to select. `bfprtRange` below splices the result back
  into an `Array` for statements phrased over the whole array.

  What is proved (`bfprtAux_selects`): the result is a permutation of the range in
  which the element at index `k` has rank `k` - its key is the `(k+1)`-th smallest
  of the range, counting multiplicity. That is the contract `tests/test_bfprt.cpp`
  checks by sorting a copy and comparing keys at index `k`.

  The median-of-medians *choice* is deliberately not used: a three-way partition
  selects correctly whatever pivot it is given, and the recursion terminates
  because every recursive range is strictly shorter - the pivot occurs in the
  range, so the block it lands in is a proper sub-range. Median of medians is what
  makes that shortening *fast*, a running-time fact not formalized here. The group
  pass is still modelled faithfully and proved to permute, because the C++ does it.
-/
import Tcs.Perm
import Tcs.Select
import Tcs.Sort

namespace Tcs
namespace Bfprt

variable {α : Type u} {β : Type v} [Cmp β]

/-! ## Two strict-order helpers used by the partition analysis -/

/-- If neither `a < b` nor `a = b` then `b < a`: trichotomy in the form the
three-way partition needs. -/
theorem blt_of_not_blt_of_not_beq {a b : β} (h₁ : Cmp.blt a b = false)
    (h₂ : Cmp.beq a b = false) : Cmp.blt b a = true := by
  have h : Cmp.ble a b = false := by
    rw [Cmp.ble_eq_blt_or_beq, h₁, h₂]
    rfl
  have h' : Cmp.ble b a = true := by
    rcases Cmp.ble_total a b with hh | hh
    · rw [hh] at h
      cases h
    · exact hh
  exact Cmp.blt_of_ble_of_not_ble h' h

/-- Elements with equal keys are not strictly below each other. -/
theorem blt_eq_false_of_beq {a b : β} (h : Cmp.beq a b = true) : Cmp.blt a b = false := by
  have h' := Cmp.beq_iff.mp h
  simp [Cmp.blt, h'.1, h'.2]

/-- Rank transfers along a permutation. -/
theorem isKthSmallest_of_perm {proj : α → β} {l₁ l₂ : List α} {k : Nat} {x : α}
    (h : l₁.Perm l₂) (hx : IsKthSmallest proj l₁ k x) : IsKthSmallest proj l₂ k x := by
  unfold IsKthSmallest belowCount uptoCount at hx ⊢
  exact ⟨by rw [← countP_eq_of_perm h]; exact hx.1,
    by rw [← countP_eq_of_perm h]; exact hx.2⟩

/-- Indexing past a prefix: the front part can be a `take`. -/
theorem getElem?_take_append_of_le {l s : List α} {lo k : Nat} (hlen : lo ≤ l.length)
    (hlo : lo ≤ k) : (l.take lo ++ s)[k]? = s[k - lo]? := by
  have h : (l.take lo).length ≤ k := by
    rw [List.length_take, Nat.min_eq_left hlen]
    exact hlo
  rw [List.getElem?_append_right h, List.length_take, Nat.min_eq_left hlen]

/-! ## Splicing a sub-range back in

`bubbleSort` (the sorting primitive behind the C++ `bubble_sort` calls) lives in
`Tcs.Sort`, which this file imports. -/

/-- Sorting a sub-range in place: sort `s` and glue it back between the untouched
prefix and suffix. This is how every range operation below is modelled. -/
theorem splice_perm {l s : List α} {n m : Nat} (hs : s.Perm ((l.drop n).take m)) :
    (l.take n ++ s ++ l.drop (n + m)).Perm l := by
  have h₃ : (l.drop n).take m ++ l.drop (n + m) = l.drop n := by
    rw [← List.drop_drop (i := m) (j := n)]
    exact List.take_append_drop m (l.drop n)
  rw [List.append_assoc]
  have h₂ : (s ++ l.drop (n + m)).Perm (l.drop n) := by
    rw [← h₃]
    exact List.Perm.append_right _ hs
  have h₅ := List.Perm.append_left (l.take n) h₂
  rw [List.take_append_drop n l] at h₅
  exact h₅

/-! ## `std::partition` -/

/-- C++'s `std::partition` on a range, as the front part (elements satisfying `p`)
and the rest. The C++ split iterator's offset is `(partition p l).1.length`. -/
def partition (p : α → Bool) : List α → List α × List α
  | [] => ([], [])
  | x :: t =>
    if p x then (x :: (partition p t).1, (partition p t).2)
    else ((partition p t).1, (partition p t).2 ++ [x])

/-- The two parts together are the input, rearranged. -/
theorem partition_perm (p : α → Bool) (l : List α) :
    ((partition p l).1 ++ (partition p l).2).Perm l := by
  induction l with
  | nil => simp [partition]
  | cons x t ih =>
    unfold partition
    split
    case isTrue _ => simpa using List.Perm.cons x ih
    case isFalse _ =>
      show ((partition p t).1 ++ ((partition p t).2 ++ [x])).Perm (x :: t)
      rw [← List.append_assoc]
      exact (List.Perm.append_right [x] ih).trans
        (List.perm_append_comm (l₁ := t) (l₂ := [x]))

/-- The front part is exactly the satisfying elements. -/
theorem partition_fst_length (p : α → Bool) (l : List α) :
    (partition p l).1.length = l.countP p := by
  induction l with
  | nil => simp [partition]
  | cons x t ih =>
    unfold partition
    split
    case isTrue hx =>
      rw [List.countP_cons_of_pos (p := p) (a := x) hx]
      simp [ih]
    case isFalse hx =>
      rw [List.countP_cons_of_neg (p := p) (a := x) hx]
      simp [ih]

theorem partition_fst_all {p : α → Bool} {l : List α} :
    ∀ x ∈ (partition p l).1, p x = true := by
  induction l with
  | nil => simp [partition]
  | cons y t ih =>
    unfold partition
    split
    case isTrue hp =>
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact hp
      · exact ih x hx'
    case isFalse _ =>
      intro x hx
      exact ih x hx

theorem partition_snd_all {p : α → Bool} {l : List α} :
    ∀ x ∈ (partition p l).2, p x = false := by
  induction l with
  | nil => simp [partition]
  | cons y t ih =>
    unfold partition
    split
    case isTrue _ =>
      intro x hx
      exact ih x hx
    case isFalse hp =>
      intro x hx
      rcases List.mem_append.mp hx with hx' | hx'
      · exact ih x hx'
      · rcases List.mem_singleton.mp hx' with rfl
        cases h : p x <;> simp_all

/-- A member satisfying `p` ends up in the front part of `partition`. -/
theorem partition_mem_fst {p : α → Bool} {l : List α} {x : α} (hx : x ∈ l)
    (hp : p x = true) : x ∈ (partition p l).1 := by
  induction l with
  | nil => simp at hx
  | cons y t ih =>
    unfold partition
    split
    case isTrue _ =>
      rcases List.mem_cons.mp hx with hxy | hx'
      · subst hxy
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih hx')
    case isFalse hy =>
      rcases List.mem_cons.mp hx with hxy | hx'
      · subst hxy
        exact absurd hp hy
      · exact ih hx'

/-- A member failing `p` ends up in the back part of `partition`. -/
theorem partition_mem_snd {p : α → Bool} {l : List α} {x : α} (hx : x ∈ l)
    (hp : p x = false) : x ∈ (partition p l).2 := by
  induction l with
  | nil => simp at hx
  | cons y t ih =>
    unfold partition
    split
    case isTrue hy =>
      rcases List.mem_cons.mp hx with hxy | hx'
      · subst hxy
        rw [hp] at hy
        cases hy
      · exact ih hx'
    case isFalse _ =>
      rcases List.mem_cons.mp hx with hxy | hx'
      · subst hxy
        exact List.mem_append_right _ (List.mem_singleton_self x)
      · exact List.mem_append_left _ (ih hx')

/-- The three blocks of the two nested partitions have the input's total length. -/
theorem partition_lengths_sum (p q : α → Bool) (l : List α) :
    (partition p l).1.length + (partition q (partition p l).2).1.length
        + (partition q (partition p l).2).2.length = l.length := by
  have h₁ : (partition p l).1.length + (partition p l).2.length = l.length := by
    rw [← List.length_append, (partition_perm p l).length_eq]
  have h₂ : (partition q (partition p l).2).1.length
      + (partition q (partition p l).2).2.length = (partition p l).2.length := by
    rw [← List.length_append, (partition_perm q (partition p l).2).length_eq]
  omega

/-- A predicate and its negation split the list: `countP p + countP (!p) = length`. -/
theorem countP_add_countP_not {γ : Type w} (p : γ → Bool) (l : List γ) :
    l.countP p + l.countP (fun x => !p x) = l.length := by
  induction l with
  | nil => simp
  | cons x t ih =>
    rw [List.countP_cons, List.countP_cons, List.length_cons]
    cases hx : p x <;> simp <;> omega

/-! ## The group pass -/

/-- `std::swap` of two positions of a list. Indices out of range leave the list
alone, which keeps the definition total (the C++ only swaps in range). -/
def swapAt (l : List α) (i j : Nat) : List α :=
  if hi : i < l.length ∧ j < l.length then (l.set i l[j]).set j l[i] else l

theorem swapAt_perm (l : List α) (i j : Nat) : (swapAt l i j).Perm l := by
  unfold swapAt
  split
  · rename_i hi
    exact List.perm_set_swap l hi.1 hi.2
  · exact List.Perm.refl l

/-- Sort the `i`-th group of five in place - C++'s
`bubble_sort(first + 5 * i, first + 5 * i + 5)` - and move the group's median from
offset `2` to index `i` - C++'s `std::swap(first[i], first[5 * i + 2])`. -/
def placeMedian (proj : α → β) (i : Nat) (l : List α) : List α :=
  swapAt (l.take (5 * i) ++ bubbleSort proj ((l.drop (5 * i)).take 5) ++ l.drop (5 * i + 5))
    i (5 * i + 2)

/-- C++'s `for (i = 0; i + 5 <= len; i += 5)` loop: every full group of five is
sorted and its median is moved into `[0, len / 5)`.

The *order* of the passes is part of the loop, and this is the one place where it
matters: group `i` is processed in increasing `i`. The destination index `i` is
smaller than every slot of group `i` (and of every later group), so once a median is
written at index `i` no later pass disturbs it, and after the whole pass index `i`
holds the median of group `i` for every `i < len / 5`. Running the groups in the
reverse order instead re-sorts the low groups *after* their medians have been moved
out (the group of index `i` is re-sorted by the passes `j < i` whose slot range
covers `i`), which is not the C++ loop and would invalidate the linear-time argument
below. -/
def groupPass (proj : α → β) : Nat → List α → List α
  | 0, l => l
  | i + 1, l => placeMedian proj i (groupPass proj i l)

theorem placeMedian_perm (proj : α → β) (i : Nat) (l : List α) :
    (placeMedian proj i l).Perm l := by
  unfold placeMedian
  refine (swapAt_perm _ _ _).trans ?_
  exact splice_perm (bubbleSort_perm proj ((l.drop (5 * i)).take 5))

theorem groupPass_perm (proj : α → β) : ∀ i (l : List α), (groupPass proj i l).Perm l
  | 0, l => List.Perm.refl l
  | i + 1, l => (placeMedian_perm proj i (groupPass proj i l)).trans (groupPass_perm proj i l)

theorem groupPass_length (proj : α → β) (i : Nat) (l : List α) :
    (groupPass proj i l).length = l.length :=
  (groupPass_perm proj i l).length_eq

/-! ## The algorithm -/

/-- C++'s `bfprt` on the element list of a range: `k` is the rank to select
(`k = mid - first`), and `fuel` bounds the list length, which makes the recursion
structural - every recursive range is proved strictly shorter below. -/
def bfprtAux (proj : α → β) : Nat → Nat → List α → List α
  | 0, _, l => l
  | fuel + 1, k, l =>
    if l.length < 5 then bubbleSort proj l
    else
      let g := l.length / 5
      let l₁ := groupPass proj g l
      let mm := bfprtAux proj fuel (g / 2) (l₁.take g)
      let l₂ := mm ++ l₁.drop g
      match l₂[g / 2]? with
      | none => l₁
      | some pv =>
        let p₁ := partition (fun x => Cmp.blt (proj x) (proj pv)) l₂
        let p₂ := partition (fun x => Cmp.beq (proj x) (proj pv)) p₁.2
        if k < p₁.1.length then
          bfprtAux proj fuel k p₁.1 ++ (p₂.1 ++ p₂.2)
        else if p₁.1.length + p₂.1.length ≤ k then
          (p₁.1 ++ p₂.1) ++ bfprtAux proj fuel (k - p₁.1.length - p₂.1.length) p₂.2
        else (p₁.1 ++ p₂.1) ++ p₂.2

/-- Strengthening of `bfprtAux_selects` used for the array contract: the result
always permutes the input (even for a rank outside the range), and inside the
range it carries the rank-`k` element. -/
theorem bfprtAux_spec (proj : α → β) (fuel : Nat) :
    ∀ (k : Nat) (l : List α), l.length ≤ fuel →
      (bfprtAux proj fuel k l).Perm l ∧
        (k < l.length →
          ∃ xs ys y, bfprtAux proj fuel k l = xs ++ y :: ys ∧ xs.length = k ∧
            IsKthSmallest proj (bfprtAux proj fuel k l) k y) := by
  induction fuel with
  | zero =>
    intro k l hlen
    refine ⟨List.Perm.refl l, ?_⟩
    intro hk
    exfalso
    omega
  | succ fuel ih =>
    intro k l hlen
    rw [bfprtAux]
    by_cases hsmall : l.length < 5
    · simp only [hsmall, ite_true]
      refine ⟨bubbleSort_perm proj l, ?_⟩
      intro hk
      exact (selects_of_sorted_perm (bubbleSort_perm proj l) (bubbleSort_sorted proj l)
        (by rw [(bubbleSort_perm proj l).length_eq]; exact hk)).2
    · simp only [hsmall, ite_false]
      generalize hg : l.length / 5 = g
      generalize hl₁ : groupPass proj g l = l₁
      generalize hmm : bfprtAux proj fuel (g / 2) (l₁.take g) = mm
      generalize hl₂ : mm ++ l₁.drop g = l₂
      have hl₁perm : l₁.Perm l := by rw [← hl₁]; exact groupPass_perm proj g l
      have hl₁len : l₁.length = l.length := hl₁perm.length_eq
      have hglen : g ≤ l.length := by rw [← hg]; exact Nat.div_le_self _ _
      have htake : (l₁.take g).length = g := by
        rw [List.length_take, hl₁len, Nat.min_eq_left hglen]
      have hgfuel : g ≤ fuel := by rw [← hg]; omega
      have htakefuel : (l₁.take g).length ≤ fuel := by rw [htake]; exact hgfuel
      have hmm_perm : mm.Perm (l₁.take g) := by
        rw [← hmm]
        exact (ih (g / 2) (l₁.take g) htakefuel).1
      have hl₂perm : l₂.Perm l := by
        rw [← hl₂]
        exact ((List.Perm.append_right _ hmm_perm).trans
          (List.Perm.of_eq (List.take_append_drop g l₁))).trans hl₁perm
      have hl₂len : l₂.length = l.length := hl₂perm.length_eq
      cases hsome : l₂[g / 2]? with
      | none =>
        exfalso
        have h₁ : l₂.length ≤ g / 2 := List.getElem?_eq_none_iff.mp hsome
        have h₂ : g / 2 < l₂.length := by
          rw [hl₂len]
          rw [← hg]
          omega
        omega
      | some pv =>
        dsimp only
        generalize hA : (partition (fun x => Cmp.blt (proj x) (proj pv)) l₂).fst = A
        generalize hR : (partition (fun x => Cmp.blt (proj x) (proj pv)) l₂).snd = R
        generalize hB : (partition (fun x => Cmp.beq (proj x) (proj pv)) R).fst = B
        generalize hC : (partition (fun x => Cmp.beq (proj x) (proj pv)) R).snd = C
        have hAperm : (A ++ R).Perm l₂ := by
          rw [← hA, ← hR]
          exact partition_perm _ l₂
        have hRperm : (B ++ C).Perm R := by
          rw [← hB, ← hC]
          exact partition_perm _ R
        have hAall : ∀ x ∈ A, Cmp.blt (proj x) (proj pv) = true := by
          rw [← hA]
          exact partition_fst_all
        have hRall : ∀ x ∈ R, Cmp.blt (proj x) (proj pv) = false := by
          rw [← hR]
          exact partition_snd_all
        have hBall : ∀ x ∈ B, Cmp.beq (proj x) (proj pv) = true := by
          rw [← hB]
          exact partition_fst_all
        have hCall : ∀ x ∈ C, Cmp.beq (proj x) (proj pv) = false := by
          rw [← hC]
          exact partition_snd_all
        have hBblt : ∀ x ∈ B, Cmp.blt (proj x) (proj pv) = false :=
          fun x hx => blt_eq_false_of_beq (hBall x hx)
        have hpvmem : pv ∈ l₂ := List.mem_iff_getElem?.mpr ⟨g / 2, hsome⟩
        have hpvR : pv ∈ R := by
          have h : pv ∈ A ++ R := hAperm.mem_iff.mpr hpvmem
          rcases List.mem_append.mp h with h' | h'
          · have hp := hAall pv h'
            rw [Cmp.blt_irrefl] at hp
            cases hp
          · exact h'
        have hQpv : Cmp.beq (proj pv) (proj pv) = true :=
          Cmp.beq_iff.mpr ⟨Cmp.ble_refl _, Cmp.ble_refl _⟩
        have hpvB : pv ∈ B := by
          have h : pv ∈ B ++ C := hRperm.mem_iff.mpr hpvR
          rcases List.mem_append.mp h with h' | h'
          · exact h'
          · have hp := hCall pv h'
            rw [hQpv] at hp
            cases hp
        have hCR : ∀ x ∈ C, x ∈ R := fun x hx =>
          hRperm.mem_iff.mp (List.mem_append_right B hx)
        have hCblt : ∀ x ∈ C, Cmp.blt (proj pv) (proj x) = true := fun x hx =>
          blt_of_not_blt_of_not_beq (hRall x (hCR x hx)) (hCall x hx)
        have hCble : ∀ x ∈ C, Cmp.ble (proj x) (proj pv) = false := fun x hx =>
          Cmp.not_ble_of_blt (hCblt x hx)
        have hAC : (A ++ (B ++ C)).Perm l₂ :=
          (List.Perm.append_left A hRperm).trans hAperm
        have hsum : A.length + B.length + C.length = l₂.length := by
          have h := partition_lengths_sum (fun x => Cmp.blt (proj x) (proj pv))
            (fun x => Cmp.beq (proj x) (proj pv)) l₂
          rw [hA, hR, hB, hC] at h
          exact h
        have hAlen : A.length = l₂.countP (fun x => Cmp.blt (proj x) (proj pv)) := by
          rw [← hA]
          exact partition_fst_length _ l₂
        have hAlen_lt : A.length < l₂.length := by
          rw [hAlen]
          exact countP_lt_length_of_mem_false hpvmem (Cmp.blt_irrefl _)
        have hClen_lt : C.length < l₂.length := by
          have hBpos : 0 < B.length := List.length_pos_of_mem hpvB
          omega
        have hAfuel : A.length ≤ fuel := by omega
        have hCfuel : C.length ≤ fuel := by omega
        by_cases h1 : k < A.length
        · simp only [h1, ite_true]
          refine ⟨?_, ?_⟩
          · exact ((List.Perm.append_right (B ++ C) (ih k A hAfuel).1).trans hAC).trans hl₂perm
          · intro hk
            obtain ⟨xs, ys, y, hdecomp, hxsk, hrank⟩ := (ih k A hAfuel).2 h1
            have hyA : y ∈ A := (ih k A hAfuel).1.mem_iff.mp (by
              rw [hdecomp]
              exact List.mem_append_right _ List.mem_cons_self)
            have hbelow : belowCount proj (B ++ C) y = 0 := by
              refine countP_eq_zero_of_all (fun z hz => ?_)
              rw [List.mem_append] at hz
              rcases hz with hzB | hzC
              · have hb := Cmp.beq_iff.mp (hBall z hzB)
                have hzy : Cmp.ble (proj y) (proj z) = true :=
                  Cmp.ble_trans (Cmp.ble_of_blt (hAall y hyA)) hb.2
                simp [Cmp.blt, hzy]
              · exact Cmp.not_blt_of_blt (Cmp.blt_trans (hAall y hyA) (hCblt z hzC))
            refine ⟨xs, ys ++ (B ++ C), y, ?_, hxsk, isKthSmallest_append_left hrank hbelow⟩
            calc bfprtAux proj fuel k A ++ (B ++ C)
                = (xs ++ y :: ys) ++ (B ++ C) := by rw [hdecomp]
              _ = xs ++ y :: (ys ++ (B ++ C)) := by rw [List.append_assoc, List.cons_append]
        · simp only [h1, ite_false]
          by_cases h2 : A.length + B.length ≤ k
          · simp only [h2, ite_true]
            have hAle : A.length ≤ k := by omega
            refine ⟨?_, ?_⟩
            · exact ((List.Perm.append_left (A ++ B) (ih (k - A.length - B.length) C hCfuel).1).trans
                ((List.Perm.of_eq (List.append_assoc A B C)).trans hAC)).trans hl₂perm
            · intro hk
              have hkC : k - A.length - B.length < C.length := by omega
              obtain ⟨xs, ys, y, hdecomp, hxsk, hrank⟩ :=
                (ih (k - A.length - B.length) C hCfuel).2 hkC
              have hyC : y ∈ C := (ih (k - A.length - B.length) C hCfuel).1.mem_iff.mp (by
                rw [hdecomp]
                exact List.mem_append_right _ List.mem_cons_self)
              have hbelow : belowCount proj (A ++ B) y = (A ++ B).length := by
                refine countP_eq_length_of_all (fun z hz => ?_)
                rw [List.mem_append] at hz
                rcases hz with hzA | hzB
                · exact Cmp.blt_trans (hAall z hzA) (hCblt y hyC)
                · exact Cmp.blt_of_beq_of_blt (hBall z hzB) (hCblt y hyC)
              have hrank' := isKthSmallest_append_right (l₁ := A ++ B) hrank hbelow
              have hlen : (A ++ B).length + (k - A.length - B.length) = k := by
                rw [List.length_append]
                omega
              refine ⟨(A ++ B) ++ xs, ys, y, ?_, ?_, ?_⟩
              · calc (A ++ B) ++ bfprtAux proj fuel (k - A.length - B.length) C
                    = (A ++ B) ++ (xs ++ y :: ys) := by rw [hdecomp]
                  _ = ((A ++ B) ++ xs) ++ y :: ys := (List.append_assoc (A ++ B) xs (y :: ys)).symm
              · rw [List.length_append, List.length_append, hxsk]
                omega
              · rwa [hlen] at hrank'
          · simp only [h2, ite_false]
            have hAle : A.length ≤ k := by omega
            have hkAB : k < A.length + B.length := by omega
            have hjB : k - A.length < B.length := by omega
            refine ⟨((List.Perm.of_eq (List.append_assoc A B C)).trans hAC).trans hl₂perm, ?_⟩
            intro hk
            have hBdec : B.take (k - A.length) ++ B[k - A.length] :: B.drop (k - A.length + 1) = B := by
              rw [List.getElem_cons_drop hjB]
              exact List.take_append_drop _ B
            have hBC : B ++ C
                = B.take (k - A.length) ++ B[k - A.length] :: (B.drop (k - A.length + 1) ++ C) := by
              calc B ++ C
                  = (B.take (k - A.length) ++ B[k - A.length] :: B.drop (k - A.length + 1)) ++ C := by
                    rw [hBdec]
                _ = B.take (k - A.length) ++ B[k - A.length] :: (B.drop (k - A.length + 1) ++ C) := by
                    rw [List.append_assoc, List.cons_append]
            have hdecomp : (A ++ B) ++ C
                = (A ++ B.take (k - A.length)) ++ B[k - A.length] ::
                    (B.drop (k - A.length + 1) ++ C) := by
              calc (A ++ B) ++ C
                  = A ++ (B ++ C) := List.append_assoc A B C
                _ = A ++ (B.take (k - A.length) ++ B[k - A.length] ::
                      (B.drop (k - A.length + 1) ++ C)) := by rw [hBC]
                _ = (A ++ B.take (k - A.length)) ++ B[k - A.length] ::
                      (B.drop (k - A.length + 1) ++ C) :=
                    (List.append_assoc A (B.take (k - A.length))
                      (B[k - A.length] :: (B.drop (k - A.length + 1) ++ C))).symm
            have hlen : (A ++ B.take (k - A.length)).length = k := by
              rw [List.length_append, List.length_take, Nat.min_eq_left (Nat.le_of_lt hjB)]
              omega
            have hbelow : belowCount proj ((A ++ B) ++ C) pv = A.length := by
              unfold belowCount
              rw [List.countP_append, List.countP_append]
              have h1' : List.countP (fun x => Cmp.blt (proj x) (proj pv)) A = A.length :=
                countP_eq_length_of_all hAall
              have h2' : List.countP (fun x => Cmp.blt (proj x) (proj pv)) B = 0 :=
                countP_eq_zero_of_all hBblt
              have h3' : List.countP (fun x => Cmp.blt (proj x) (proj pv)) C = 0 :=
                countP_eq_zero_of_all (fun z hz => Cmp.not_blt_of_blt (hCblt z hz))
              rw [h1', h2', h3']
              omega
            have hupto : uptoCount proj ((A ++ B) ++ C) pv = A.length + B.length := by
              unfold uptoCount
              rw [List.countP_append, List.countP_append]
              have h1' : List.countP (fun x => Cmp.ble (proj x) (proj pv)) A = A.length :=
                countP_eq_length_of_all (fun z hz => Cmp.ble_of_blt (hAall z hz))
              have h2' : List.countP (fun x => Cmp.ble (proj x) (proj pv)) B = B.length :=
                countP_eq_length_of_all (fun z hz => (Cmp.beq_iff.mp (hBall z hz)).1)
              have h3' : List.countP (fun x => Cmp.ble (proj x) (proj pv)) C = 0 :=
                countP_eq_zero_of_all hCble
              rw [h1', h2', h3']
              omega
            have hrankPv : IsKthSmallest proj ((A ++ B) ++ C) k pv :=
              ⟨by rw [hbelow]; exact hAle, by rw [hupto]; exact hkAB⟩
            have hbeq : Cmp.beq (proj pv) (proj (B[k - A.length])) = true := by
              rw [Cmp.beq_comm]
              exact hBall _ (List.getElem_mem hjB)
            exact ⟨A ++ B.take (k - A.length), B.drop (k - A.length + 1) ++ C,
              B[k - A.length], hdecomp, hlen, isKthSmallest_of_beq hrankPv hbeq⟩

/-- The result of `bfprtAux` is always a permutation of its input. -/
theorem bfprtAux_perm (proj : α → β) (fuel k : Nat) (l : List α) (hlen : l.length ≤ fuel) :
    (bfprtAux proj fuel k l).Perm l :=
  (bfprtAux_spec proj fuel k l hlen).1

/-- **BFPRT selects the rank-`k` element.** -/
theorem bfprtAux_selects (proj : α → β) (fuel : Nat) :
    ∀ (k : Nat) (l : List α), l.length ≤ fuel → k < l.length →
      Selects proj k l (bfprtAux proj fuel k l) := by
  intro k l hlen hk
  exact ⟨(bfprtAux_spec proj fuel k l hlen).1, (bfprtAux_spec proj fuel k l hlen).2 hk⟩

/-! ## The array-level contract -/

/-- `bfprt` at the array level: select on the element list of `[lo, hi)` and splice
the result back, leaving the rest of the array untouched. -/
def bfprtRange (proj : α → β) (a : Array α) (lo mid hi : Nat) : Array α :=
  (a.toList.take lo ++ bfprtAux proj (hi - lo) (mid - lo) ((a.toList.drop lo).take (hi - lo))
    ++ a.toList.drop hi).toArray

theorem bfprtRange_perm (proj : α → β) (a : Array α) {lo mid hi : Nat} (hlo : lo ≤ hi)
    (hhi : hi ≤ a.size) :
    (bfprtRange proj a lo mid hi).toList.Perm a.toList := by
  have hlen : ((a.toList.drop lo).take (hi - lo)).length ≤ hi - lo := by
    rw [List.length_take, List.length_drop, Array.length_toList, Nat.min_eq_left (by omega)]
    omega
  have hs : (bfprtAux proj (hi - lo) (mid - lo) ((a.toList.drop lo).take (hi - lo))).Perm
      ((a.toList.drop lo).take (hi - lo)) :=
    bfprtAux_perm proj (hi - lo) (mid - lo) _ hlen
  have h := splice_perm (l := a.toList)
    (s := bfprtAux proj (hi - lo) (mid - lo) ((a.toList.drop lo).take (hi - lo)))
    (n := lo) (m := hi - lo) hs
  have hlohi : lo + (hi - lo) = hi := by omega
  rw [bfprtRange, List.toList_toArray]
  rw [hlohi] at h
  exact h

/-- **The C++ contract.** Position `mid` holds an element whose rank within the
range is `mid - lo`. -/
theorem bfprtRange_selects (proj : α → β) (a : Array α) {lo mid hi : Nat} (hlo : lo ≤ mid)
    (hmid : mid < hi) (hhi : hi ≤ a.size) :
    ∃ y, (bfprtRange proj a lo mid hi)[mid]? = some y ∧
      IsKthSmallest proj ((a.toList.drop lo).take (hi - lo)) (mid - lo) y := by
  have hlo' : lo ≤ a.toList.length := by rw [Array.length_toList]; omega
  have hlen_eq : ((a.toList.drop lo).take (hi - lo)).length = hi - lo := by
    rw [List.length_take, List.length_drop, Array.length_toList]
    exact Nat.min_eq_left (by omega)
  have hlen : ((a.toList.drop lo).take (hi - lo)).length ≤ hi - lo := by rw [hlen_eq]; omega
  have hk : mid - lo < ((a.toList.drop lo).take (hi - lo)).length := by
    rw [hlen_eq]
    omega
  have hsel := bfprtAux_selects proj (hi - lo) (mid - lo) ((a.toList.drop lo).take (hi - lo))
    hlen hk
  obtain ⟨xs, ys, y, hXdec, hxsk, hrank⟩ := hsel.2
  have hXlen : (bfprtAux proj (hi - lo) (mid - lo) ((a.toList.drop lo).take (hi - lo))).length
      = hi - lo := by
    rw [hsel.1.length_eq, hlen_eq]
  have htake_len : (a.toList.take lo).length = lo := by
    rw [List.length_take, Nat.min_eq_left hlo']
  have hmidAB : mid < (a.toList.take lo ++ bfprtAux proj (hi - lo) (mid - lo)
      ((a.toList.drop lo).take (hi - lo))).length := by
    rw [List.length_append, htake_len, hXlen]
    omega
  refine ⟨y, ?_, isKthSmallest_of_perm hsel.1 hrank⟩
  rw [bfprtRange, ← Array.getElem?_toList, List.toList_toArray]
  rw [List.getElem?_append_left hmidAB]
  rw [getElem?_take_append_of_le hlo' hlo]
  rw [hXdec]
  rw [← hxsk]
  rw [List.getElem?_append_right (Nat.le_refl _)]
  simp

/-- What `tests/test_bfprt.cpp` asserts: the key at `mid` equals the key a sorted
copy of the range carries there. -/
theorem bfprtRange_key_eq_sorted (proj : α → β) (a : Array α) {lo mid hi : Nat}
    (hlo : lo ≤ mid) (hmid : mid < hi) (hhi : hi ≤ a.size) :
    ∃ y z, (bfprtRange proj a lo mid hi)[mid]? = some y ∧
      (bubbleSort proj ((a.toList.drop lo).take (hi - lo)))[mid - lo]? = some z ∧
      Cmp.beq (proj y) (proj z) = true := by
  have hlen_eq : ((a.toList.drop lo).take (hi - lo)).length = hi - lo := by
    rw [List.length_take, List.length_drop, Array.length_toList]
    exact Nat.min_eq_left (by omega)
  have hk : mid - lo < ((a.toList.drop lo).take (hi - lo)).length := by
    rw [hlen_eq]
    omega
  obtain ⟨y, hy, hranky⟩ := bfprtRange_selects proj a hlo hmid hhi
  have hk' : mid - lo < (bubbleSort proj ((a.toList.drop lo).take (hi - lo))).length := by
    rw [(bubbleSort_perm proj _).length_eq]
    exact hk
  refine ⟨y, (bubbleSort proj ((a.toList.drop lo).take (hi - lo)))[mid - lo]'hk', hy, ?_, ?_⟩
  · exact List.getElem?_eq_getElem hk'
  · exact isKthSmallest_unique hranky (isKthSmallest_of_perm (bubbleSort_perm proj _)
      (sorted_isKthSmallest (bubbleSort_sorted proj _) hk'))

/-! Concrete values, so a mis-stated definition cannot pass unnoticed. -/

example : (bubbleSort (proj := fun n : Nat => n) [3, 1, 2]).Perm [3, 1, 2] :=
  bubbleSort_perm _ _

example : Sorted (KeyLe (fun n : Nat => n)) (bubbleSort (fun n : Nat => n) [3, 1, 2]) :=
  bubbleSort_sorted _ _

example : (partition (fun n : Nat => n < 2) [1, 5, 0, 7]).1 = [1, 0] := rfl

example : (partition (fun n : Nat => n < 2) [1, 5, 0, 7]).2 = [7, 5] := rfl

example : (swapAt [1, 2, 3, 4] 0 2) = [3, 2, 1, 4] := rfl

example : (swapAt [1, 2, 3] 0 9) = [1, 2, 3] := rfl

end Bfprt
end Tcs
