/-
  In-place stable merge: the specification layer, and the short-range branch of
  C++'s `inplace_stable_merge` (`include/tcs/inplace/stable_merge.hpp`).

  A stable merge is specified *without* ever mentioning positions. For a key `k`,
  `keyFilter proj k l` is the subsequence of `l` made of the elements whose key
  equals `k`; asking that subsequence to be unchanged for every `k` says both that
  equal keys keep their input order *and* that no element was lost or invented.
  `StableSort proj l l'` bundles that with sortedness, so it is exactly the
  contract the pipeline `stable_unique_limit -> align_blocks_limit -> block phases
  -> bubble_sort -> rotation merges` has to maintain end to end, and no uniqueness
  argument about sorted permutations is needed anywhere.

  This module holds that specification, the reference stable merge `mergeTwo`, and
  the first branch of the C++ routine: below 25 elements the C++ calls
  `bubble_sort` over the whole range, whose stability is proved here.
-/
import Tcs.Merge

namespace Tcs

variable {α : Type u} {β : Type v} [Cmp β]

/-! ## Stability as a subsequence invariant -/

/-- The elements of `l` whose key equals `k`, in order. -/
def keyFilter (proj : α → β) (k : β) (l : List α) : List α :=
  l.filter fun x => Cmp.beq (proj x) k

/-- **The stable-sort contract**: `l'` is `l` sorted, and every equal-key
subsequence of `l` survives in `l'` unchanged - which is "equal keys keep their
input order" together with "`l'` uses exactly the elements of `l`". -/
def StableSort (proj : α → β) (l l' : List α) : Prop :=
  Sorted (KeyLe proj) l' ∧ l'.Perm l ∧ ∀ k : β, keyFilter proj k l' = keyFilter proj k l

theorem stableSort_sorted {proj : α → β} {l l' : List α} (h : StableSort proj l l') :
    Sorted (KeyLe proj) l' :=
  h.1

theorem stableSort_perm {proj : α → β} {l l' : List α} (h : StableSort proj l l') :
    l'.Perm l :=
  h.2.1

theorem stableSort_keyFilter {proj : α → β} {l l' : List α} (h : StableSort proj l l')
    (k : β) : keyFilter proj k l' = keyFilter proj k l :=
  h.2.2 k

theorem stableSort_length {proj : α → β} {l l' : List α} (h : StableSort proj l l') :
    l'.length = l.length :=
  h.2.1.length_eq

/-! ## The key subsequence

`List.filter` is compiled through `List.brecOn`, so it never unfolds
definitionally: every equation below is derived from the core `List.filter`
lemmas rather than by `rfl`. -/

theorem keyFilter_nil (proj : α → β) (k : β) : keyFilter proj k [] = [] :=
  rfl

theorem keyFilter_cons (proj : α → β) (k : β) (x : α) (xs : List α) :
    keyFilter proj k (x :: xs) =
      if Cmp.beq (proj x) k then x :: keyFilter proj k xs else keyFilter proj k xs := by
  by_cases h : Cmp.beq (proj x) k = true
  · rw [ite_eq_left h]
    exact List.filter_cons_of_pos (p := fun y => Cmp.beq (proj y) k) h
  · rw [ite_eq_right h]
    exact List.filter_cons_of_neg (p := fun y => Cmp.beq (proj y) k) h

theorem keyFilter_cons_of_beq {proj : α → β} {k : β} {x : α} {xs : List α}
    (h : Cmp.beq (proj x) k = true) :
    keyFilter proj k (x :: xs) = x :: keyFilter proj k xs := by
  rw [keyFilter_cons, ite_eq_left h]

theorem keyFilter_cons_of_not_beq {proj : α → β} {k : β} {x : α} {xs : List α}
    (h : ¬(Cmp.beq (proj x) k = true)) :
    keyFilter proj k (x :: xs) = keyFilter proj k xs := by
  rw [keyFilter_cons, ite_eq_right h]

theorem keyFilter_append (proj : α → β) (k : β) (l₁ l₂ : List α) :
    keyFilter proj k (l₁ ++ l₂) = keyFilter proj k l₁ ++ keyFilter proj k l₂ := by
  show List.filter (fun y => Cmp.beq (proj y) k) (l₁ ++ l₂) =
    List.filter (fun y => Cmp.beq (proj y) k) l₁ ++ List.filter (fun y => Cmp.beq (proj y) k) l₂
  rw [List.filter_append]

/-- A list none of whose elements carries the key `k` has an empty `k`-subsequence. -/
theorem keyFilter_eq_nil_of_all {proj : α → β} {k : β} (l : List α)
    (h : ∀ x ∈ l, Cmp.beq (proj x) k = false) : keyFilter proj k l = [] := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      have hx := h x List.mem_cons_self
      rw [keyFilter_cons, ite_eq_right (by rw [hx]; exact Bool.false_ne_true),
        ih (fun y hy => h y (List.mem_cons_of_mem x hy))]

/-- The totality of the order, in the form the merge needs: a failed `<=` holds
the other way round. -/
theorem Cmp.ble_of_not_ble {a b : β} (h : Cmp.ble a b = false) : Cmp.ble b a = true := by
  rcases Cmp.ble_total a b with h' | h'
  · rw [h] at h'; exact absurd h' Bool.false_ne_true
  · exact h'

/-- If `b`'s key is strictly below `a`'s then no single key equals both. -/
theorem not_both_beq_of_blt {proj : α → β} {a b : α} {k : β}
    (h : Cmp.blt (proj b) (proj a) = true) :
    ¬(Cmp.beq (proj a) k = true ∧ Cmp.beq (proj b) k = true) := by
  rintro ⟨h₁, h₂⟩
  rw [Cmp.beq_eq h₁, Cmp.beq_eq h₂] at h
  exact absurd h (by simp [Cmp.blt_irrefl])

/-! ## `bubbleUpR` and the outer loop keep every equal-key subsequence -/

theorem bubbleUpR_nil (proj : α → β) (a : α) : bubbleUpR proj a [] = ([], a) :=
  rfl

/-- One bubble pass only swaps an element with one of a *strictly* smaller key, so
no equal-key subsequence is disturbed: the peeled maximum simply moves to the end. -/
theorem bubbleUpR_keyFilter (proj : α → β) (a : α) (k : β) :
    ∀ l : List α,
      keyFilter proj k ((bubbleUpR proj a l).1 ++ [(bubbleUpR proj a l).2]) =
        keyFilter proj k (a :: l)
  | [] => by rw [bubbleUpR_nil]; rfl
  | b :: bs => by
      have ih₁ := bubbleUpR_keyFilter proj a k bs
      have ih₂ := bubbleUpR_keyFilter proj b k bs
      by_cases h : Cmp.blt (proj b) (proj a) = true
      · rw [bubbleUpR_cons_of_blt h]
        dsimp only
        rw [List.cons_append]
        have hpq := not_both_beq_of_blt (proj := proj) (k := k) h
        simp only [keyFilter_cons, ih₁]
        by_cases hp : Cmp.beq (proj a) k = true <;>
          by_cases hq : Cmp.beq (proj b) k = true <;> simp_all
      · rw [bubbleUpR_cons_of_not_blt (by simpa using h)]
        dsimp only
        rw [List.cons_append]
        simp only [keyFilter_cons, ih₂]

/-- The outer loop reappends the peeled maxima one by one, which is exactly the
order a stable sort needs, so it keeps the equal-key subsequences too. -/
theorem bubbleSortAux_keyFilter (proj : α → β) (fuel : Nat) :
    ∀ l : List α, l.length ≤ fuel → ∀ k : β,
      keyFilter proj k (bubbleSortAux proj fuel l) = keyFilter proj k l := by
  induction fuel with
  | zero =>
      intro l hl k
      match l with
      | [] => rfl
      | _ :: _ => exact absurd hl (Nat.not_succ_le_zero _)
  | succ n ih =>
      intro l hl k
      match l with
      | [] => rfl
      | x :: xs =>
        rw [bubbleSortAux_succ_cons]
        dsimp only
        have hlen : (bubbleUpR proj x xs).1.length ≤ n := by
          rw [bubbleUpR_length]
          simp only [List.length_cons] at hl
          omega
        rw [keyFilter_append, ih _ hlen k, ← keyFilter_append, bubbleUpR_keyFilter proj x k xs]

/-- **`bubble_sort` is stable**: it never swaps two equal keys, so every equal-key
subsequence of its input reappears verbatim. -/
theorem bubbleSort_keyFilter (proj : α → β) (l : List α) (k : β) :
    keyFilter proj k (bubbleSort proj l) = keyFilter proj k l :=
  bubbleSortAux_keyFilter proj l.length l (Nat.le_refl _) k

/-- **The `block_size <= 4` branch of C++'s `inplace_stable_merge`**: there the
routine falls back to `bubble_sort` over the whole range, and `bubble_sort` is a
stable sort. -/
theorem bubbleSort_stableSort (proj : α → β) (l : List α) :
    StableSort proj l (bubbleSort proj l) :=
  ⟨bubbleSort_sorted proj l, bubbleSort_perm proj l, bubbleSort_keyFilter proj l⟩

/-! ## The reference stable merge -/

/-- In a *sorted* run no element repeats the key of an element the run already
compares strictly above: everything from the head on is at least the head. -/
theorem keyFilter_head_eq_nil {proj : α → β} {x y : α} {xs : List α}
    (hA : Sorted (KeyLe proj) (x :: xs)) (h : Cmp.ble (proj x) (proj y) = false) :
    keyFilter proj (proj y) (x :: xs) = [] := by
  have hyx : Cmp.blt (proj y) (proj x) = true := Cmp.blt_of_ble_of_not_ble (Cmp.ble_of_not_ble h) h
  refine keyFilter_eq_nil_of_all _ (fun z hz => ?_)
  rcases List.mem_cons.mp hz with h' | h'
  · rw [h', Cmp.beq_comm (proj x) (proj y), Cmp.not_beq_of_blt hyx]
  · have hxle : Cmp.ble (proj x) (proj z) = true :=
      ((sorted_cons_iff (KeyLe proj) x xs).mp hA).1 z h'
    rw [Cmp.beq_comm (proj z) (proj y), Cmp.not_beq_of_blt (Cmp.blt_of_blt_of_ble hyx hxle)]

/-- **`mergeTwo` is the stable merge**: on two sorted runs it keeps every equal-key
subsequence, which is exactly "take from the left run on ties". -/
theorem mergeTwo_keyFilter (proj : α → β) (k : β) (A : List α) :
    ∀ B : List α, Sorted (KeyLe proj) A → Sorted (KeyLe proj) B →
      keyFilter proj k (mergeTwo proj A B) = keyFilter proj k A ++ keyFilter proj k B := by
  induction A with
  | nil => intro B _ _; rw [mergeTwo_nil_left, keyFilter_nil, List.nil_append]
  | cons x xs ih =>
      intro B hA hB
      have hxs : Sorted (KeyLe proj) xs := ((sorted_cons_iff (KeyLe proj) x xs).mp hA).2
      have main : ∀ B : List α, Sorted (KeyLe proj) B →
          keyFilter proj k (mergeTwo proj (x :: xs) B) =
            keyFilter proj k (x :: xs) ++ keyFilter proj k B := by
        intro B
        induction B with
        | nil => intro _; rw [mergeTwo_nil_right, keyFilter_nil, List.append_nil]
        | cons y ys ihB =>
            intro hB
            have hys : Sorted (KeyLe proj) ys := ((sorted_cons_iff (KeyLe proj) y ys).mp hB).2
            by_cases h : Cmp.ble (proj x) (proj y) = true
            · rw [mergeTwo_cons_cons_of_ble h]
              simp only [keyFilter_cons, ih (y :: ys) hxs hB]
              by_cases hk : Cmp.beq (proj x) k = true <;> simp_all
            · have h' : Cmp.ble (proj x) (proj y) = false := by simpa using h
              rw [mergeTwo_cons_cons_of_not_ble h']
              by_cases hk : Cmp.beq (proj y) k = true
              · have hnil : keyFilter proj k (x :: xs) = [] := by
                  rw [← Cmp.beq_eq hk]
                  exact keyFilter_head_eq_nil hA h'
                rw [keyFilter_cons, ite_eq_left hk, ihB hys, hnil, keyFilter_cons, ite_eq_left hk]
                simp
              · simp only [keyFilter_cons, ihB hys, ite_eq_right hk]
      exact main B hB

/-- The reference stable merge, packaged as a `StableSort` contract. -/
theorem mergeTwo_stableSort (proj : α → β) {A B : List α}
    (hA : Sorted (KeyLe proj) A) (hB : Sorted (KeyLe proj) B) :
    StableSort proj (A ++ B) (mergeTwo proj A B) :=
  ⟨mergeTwo_sorted proj A B hA hB, mergeTwo_perm proj A B, fun k => by
    rw [mergeTwo_keyFilter proj k A B hA hB, keyFilter_append]⟩

end Tcs
