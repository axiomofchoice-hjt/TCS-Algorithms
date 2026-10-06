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

/-! ## `stable_unique_limit`

The C++ routine has two overloads. The three-argument one reorders a *sorted* range so
that the first occurrence of each distinct key comes first, up to a limit; the
four-argument one does the same for two adjacent sorted runs at once, using
`inplace_merge_with_rotation` in the middle.

The model is the loop itself. `picked` is the buffer of kept elements, which the C++
holds contiguously immediately before the position it scans (so `*(right - 1)` is the
last kept element), and the closing `rotate(first, left, right)` brings that buffer to
the front - which is why the model returns it first, followed by the skipped elements
in their relative order. -/

/-- The pick test of C++'s `stable_unique_limit` loop: keep `x` while fewer than `max`
elements have been kept and `x`'s key differs from the key of the last kept element -
the C++ test `len < max && (left == right || proj(*(right - 1)) != proj(*iter))`, with
`left == right` (an empty buffer) read off `getLast?`. -/
def keepUnique (proj : α → β) (max : Nat) (picked : List α) (x : α) : Bool :=
  (picked.length < max) && (match picked.getLast? with
    | none => true
    | some y => !Cmp.beq (proj y) (proj x))

/-- C++'s `stable_unique_limit(first, last, max)` loop. -/
def uniqueLimitAux (proj : α → β) (max : Nat) : List α → List α → List α × List α
  | picked, [] => (picked, [])
  | picked, x :: xs =>
      if keepUnique proj max picked x then
        uniqueLimitAux proj max (picked ++ [x]) xs
      else
        let r := uniqueLimitAux proj max picked xs
        (r.1, x :: r.2)

theorem uniqueLimitAux_nil (proj : α → β) (max : Nat) (picked : List α) :
    uniqueLimitAux proj max picked [] = (picked, []) := rfl

theorem uniqueLimitAux_cons (proj : α → β) (max : Nat) (picked : List α) (x : α)
    (xs : List α) :
    uniqueLimitAux proj max picked (x :: xs) =
      if keepUnique proj max picked x then uniqueLimitAux proj max (picked ++ [x]) xs
      else (let r := uniqueLimitAux proj max picked xs; (r.1, x :: r.2)) := rfl

/-- C++'s `stable_unique_limit(first, last, max)` on a sorted range: the kept elements
followed by the skipped ones. -/
def uniqueLimit (proj : α → β) (max : Nat) (l : List α) : List α × List α :=
  uniqueLimitAux proj max [] l

/-- The keys of a list are pairwise different. -/
def KeysNodup (proj : α → β) (l : List α) : Prop :=
  l.Pairwise fun x y => Cmp.beq (proj x) (proj y) = false

/-- In a sorted list nothing exceeds the last element. -/
theorem keyLe_getLast {proj : α → β} {l : List α} {z : α}
    (hs : Sorted (KeyLe proj) l) (hz : l.getLast? = some z) : ∀ y ∈ l, KeyLe proj y z := by
  obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.mp hz
  intro y hy
  have hs' : (ys ++ [z]).Pairwise (KeyLe proj) := hs
  rw [List.pairwise_append] at hs'
  rcases List.mem_append.mp hy with hy' | hy'
  · exact hs'.2.2 y hy' z (by simp)
  · rw [List.mem_singleton] at hy'
    subst hy'
    exact Cmp.ble_refl _

/-- A successful pick test keeps the buffer's keys pairwise different. Under
sortedness the last kept element already compares *strictly* below `x`, so testing
`beq` against the last element is not only necessary but sufficient - which is exactly
why the C++ loop may compare against `*(right - 1)` alone. -/
theorem keepUnique_keysNodup {proj : α → β} {max : Nat} {picked : List α} {x : α}
    (hs : Sorted (KeyLe proj) picked) (hn : KeysNodup proj picked)
    (hle : ∀ y ∈ picked, KeyLe proj y x) (hk : keepUnique proj max picked x = true) :
    KeysNodup proj (picked ++ [x]) := by
  have hnot : ∀ y, picked.getLast? = some y → Cmp.beq (proj y) (proj x) = false := by
    intro y hy
    cases hb : Cmp.beq (proj y) (proj x) with
    | false => rfl
    | true =>
        rw [keepUnique] at hk
        simp only [hy] at hk
        rw [hb] at hk
        simp at hk
  rw [KeysNodup, List.pairwise_append]
  refine ⟨hn, List.pairwise_singleton _ _, ?_⟩
  intro a ha b hb
  rw [List.mem_singleton] at hb
  rw [hb]
  cases hl : picked.getLast? with
  | none =>
      rw [List.getLast?_eq_none_iff] at hl
      subst hl
      simp at ha
  | some y =>
      have hy : y ∈ picked := by
        obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp hl
        rw [hys]
        exact List.mem_append_right _ (by simp)
      have hay : Cmp.ble (proj a) (proj y) = true := keyLe_getLast hs hl a ha
      have hyx : Cmp.ble (proj y) (proj x) = true := hle y hy
      have hxy : Cmp.ble (proj x) (proj y) = false := by
        cases h : Cmp.ble (proj x) (proj y) with
        | false => rfl
        | true =>
            have hb : Cmp.beq (proj y) (proj x) = true := by simp [Cmp.beq, hyx, h]
            rw [hnot y hl] at hb
            exact absurd hb (by simp)
      have hxa : Cmp.ble (proj x) (proj a) = false := by
        cases h : Cmp.ble (proj x) (proj a) with
        | false => rfl
        | true =>
            have hxy' : Cmp.ble (proj x) (proj y) = true := Cmp.ble_trans h hay
            rw [hxy] at hxy'
            exact absurd hxy' (by simp)
      simp [Cmp.beq, hxa]

/-- The accumulator invariant of the loop: the buffer is sorted and has pairwise
different keys, the part still to be scanned is sorted, and no kept key exceeds a key
still to be scanned. The last component is what makes `*(right - 1)` sufficient. -/
def UniqueInv (proj : α → β) (picked l : List α) : Prop :=
  Sorted (KeyLe proj) picked ∧ KeysNodup proj picked ∧ Sorted (KeyLe proj) l ∧
    ∀ y ∈ picked, ∀ z ∈ l, KeyLe proj y z

/-- **The buffer `stable_unique_limit` builds is sorted and its keys are pairwise
different** - which is what lets the rest of the pipeline use it as lane labels. -/
theorem uniqueLimitAux_sorted_keysNodup (proj : α → β) (max : Nat) :
    ∀ picked l : List α, UniqueInv proj picked l →
      Sorted (KeyLe proj) (uniqueLimitAux proj max picked l).1 ∧
        KeysNodup proj (uniqueLimitAux proj max picked l).1 := by
  intro picked l
  induction l generalizing picked with
  | nil => intro h; rw [uniqueLimitAux_nil]; exact ⟨h.1, h.2.1⟩
  | cons x xs ih =>
      intro h
      obtain ⟨hps, hpn, hls, hle⟩ := h
      obtain ⟨hxle, hxs⟩ := (sorted_cons_iff (KeyLe proj) x xs).mp hls
      rw [uniqueLimitAux_cons]
      by_cases hk : keepUnique proj max picked x = true
      · rw [ite_eq_left hk]
        refine ih (picked ++ [x]) ⟨?_, ?_, hxs, ?_⟩
        · exact sorted_append hps (sorted_singleton _ _)
            (fun a ha b hb => by
              rw [List.mem_singleton] at hb; rw [hb]; exact hle a ha x (by simp))
        · exact keepUnique_keysNodup hps hpn (fun y hy => hle y hy x (by simp)) hk
        · intro y hy z hz
          rcases List.mem_append.mp hy with hy' | hy'
          · exact hle y hy' z (List.mem_cons_of_mem x hz)
          · rw [List.mem_singleton] at hy'
            subst hy'
            exact hxle z hz
      · rw [ite_eq_right (by simpa using hk)]
        dsimp only
        exact ih picked ⟨hps, hpn, hxs, fun y hy z hz => hle y hy z (List.mem_cons_of_mem x hz)⟩

/-- The loop neither loses nor invents elements. -/
theorem uniqueLimitAux_perm (proj : α → β) (max : Nat) :
    ∀ picked l : List α,
      ((uniqueLimitAux proj max picked l).1 ++ (uniqueLimitAux proj max picked l).2).Perm
        (picked ++ l) := by
  intro picked l
  induction l generalizing picked with
  | nil => rw [uniqueLimitAux_nil]
  | cons x xs ih =>
      rw [uniqueLimitAux_cons]
      by_cases hk : keepUnique proj max picked x = true
      · rw [ite_eq_left hk]
        have h := ih (picked ++ [x])
        rwa [List.append_assoc, List.singleton_append] at h
      · rw [ite_eq_right (by simpa using hk)]
        dsimp only
        exact (List.perm_middle (l₁ := (uniqueLimitAux proj max picked xs).1)
            (l₂ := (uniqueLimitAux proj max picked xs).2)).trans
          ((List.Perm.cons x (ih picked)).trans
            (List.perm_middle (l₁ := picked) (a := x) (l₂ := xs)).symm)

theorem uniqueLimit_perm (proj : α → β) (max : Nat) (l : List α) :
    ((uniqueLimit proj max l).1 ++ (uniqueLimit proj max l).2).Perm l :=
  (uniqueLimitAux_perm proj max [] l).trans (by rw [List.nil_append])

theorem uniqueLimit_sorted_keysNodup (proj : α → β) (max : Nat) {l : List α}
    (hl : Sorted (KeyLe proj) l) :
    Sorted (KeyLe proj) (uniqueLimit proj max l).1 ∧ KeysNodup proj (uniqueLimit proj max l).1 :=
  uniqueLimitAux_sorted_keysNodup proj max [] l ⟨sorted_nil _, List.Pairwise.nil, hl, by simp⟩

/-! ## The scans of the stable rotation merge

`inplace_merge_with_rotation` merges two adjacent sorted runs by repeatedly rotating a
block of one run that has to cross the current element of the other, and then skipping
straight past the elements that block has just made final. The two scans below are the
inner loops that find those blocks; modelling them as recursions rather than with
`takeWhile` keeps the "everything below `a`" and "everything equal to `a`" facts
available as plain inductions. -/

/-- The B-side scan of `inplace_merge_with_rotation_scroll_right`: the elements of `B`
whose key is strictly below `a`. That is exactly the C++ `while (split_right < last &&
proj(*split_right) < proj(*first)) split_right++;`, returning the scanned block and the
rest. -/
def splitRight (proj : α → β) (a : β) : List α → List α × List α
  | [] => ([], [])
  | y :: ys =>
      if Cmp.blt (proj y) a then
        let r := splitRight proj a ys
        (y :: r.1, r.2)
      else ([], y :: ys)

theorem splitRight_nil (proj : α → β) (a : β) : splitRight proj a [] = ([], []) := rfl

theorem splitRight_cons (proj : α → β) (a : β) (y : α) (ys : List α) :
    splitRight proj a (y :: ys) =
      if Cmp.blt (proj y) a then (let r := splitRight proj a ys; (y :: r.1, r.2))
      else ([], y :: ys) := rfl

/-- The scan consumes exactly the front of the list. -/
theorem splitRight_append (proj : α → β) (a : β) (B : List α) :
    (splitRight proj a B).1 ++ (splitRight proj a B).2 = B := by
  induction B with
  | nil => simp [splitRight_nil]
  | cons y ys ih =>
      rw [splitRight_cons]
      by_cases h : Cmp.blt (proj y) a = true
      · rw [ite_eq_left h]; dsimp only; rw [List.cons_append, ih]
      · rw [ite_eq_right (by simpa using h)]; simp

/-- Everything the scan takes is strictly below `a`. -/
theorem splitRight_blt (proj : α → β) (a : β) (B : List α) :
    ∀ y ∈ (splitRight proj a B).1, Cmp.blt (proj y) a = true := by
  induction B with
  | nil => intro y hy; rw [splitRight_nil] at hy; simp at hy
  | cons z zs ih =>
      intro y hy
      rw [splitRight_cons] at hy
      by_cases h : Cmp.blt (proj z) a = true
      · rw [ite_eq_left h] at hy
        dsimp only at hy
        rcases List.mem_cons.mp hy with hy' | hy'
        · rw [hy']; exact h
        · exact ih y hy'
      · rw [ite_eq_right (by simpa using h)] at hy
        simp at hy

/-- What the scan leaves behind starts at a key that is *not* below `a`, so by
sortedness every key left behind is at least `a`. -/
theorem splitRight_snd_head_ble {proj : α → β} {a : β} :
    ∀ {B : List α} {y : α} {ys : List α}, (splitRight proj a B).2 = y :: ys →
      Cmp.ble a (proj y) = true := by
  intro B
  induction B with
  | nil => intro y ys h; rw [splitRight_nil] at h; simp at h
  | cons z zs ih =>
      intro y ys h
      rw [splitRight_cons] at h
      by_cases hz : Cmp.blt (proj z) a = true
      · rw [ite_eq_left hz] at h
        dsimp only at h
        exact ih h
      · rw [ite_eq_right (by simpa using hz)] at h
        injection h with h1 _
        rw [← h1]
        exact Cmp.blt_eq_false_iff.mp (by simpa using hz)

/-- The A-side scan of the same turn: the leading run of `A` whose key equals `a`. That
is the C++ `first++; while (first < mid && proj(*first) == proj(*(first - 1))) first++;`
- under sortedness "equal to the previous element" and "equal to the head" agree, and
the C++ has just advanced past the head. -/
def splitEq (proj : α → β) (a : β) : List α → List α × List α
  | [] => ([], [])
  | y :: ys =>
      if Cmp.beq (proj y) a then
        let r := splitEq proj a ys
        (y :: r.1, r.2)
      else ([], y :: ys)

theorem splitEq_nil (proj : α → β) (a : β) : splitEq proj a [] = ([], []) := rfl

theorem splitEq_cons (proj : α → β) (a : β) (y : α) (ys : List α) :
    splitEq proj a (y :: ys) =
      if Cmp.beq (proj y) a then (let r := splitEq proj a ys; (y :: r.1, r.2))
      else ([], y :: ys) := rfl

theorem splitEq_append (proj : α → β) (a : β) (A : List α) :
    (splitEq proj a A).1 ++ (splitEq proj a A).2 = A := by
  induction A with
  | nil => simp [splitEq_nil]
  | cons y ys ih =>
      rw [splitEq_cons]
      by_cases h : Cmp.beq (proj y) a = true
      · rw [ite_eq_left h]; dsimp only; rw [List.cons_append, ih]
      · rw [ite_eq_right (by simpa using h)]; simp

/-- Everything the equal-run scan takes has key exactly `a`. -/
theorem splitEq_beq (proj : α → β) (a : β) (A : List α) :
    ∀ y ∈ (splitEq proj a A).1, Cmp.beq (proj y) a = true := by
  induction A with
  | nil => intro y hy; rw [splitEq_nil] at hy; simp at hy
  | cons z zs ih =>
      intro y hy
      rw [splitEq_cons] at hy
      by_cases h : Cmp.beq (proj z) a = true
      · rw [ite_eq_left h] at hy
        dsimp only at hy
        rcases List.mem_cons.mp hy with hy' | hy'
        · rw [hy']; exact h
        · exact ih y hy'
      · rw [ite_eq_right (by simpa using h)] at hy
        simp at hy

/-- The equal-run scan takes at least the head when the head's key is `a`, which is what
makes every turn of the loop advance. -/
theorem splitEq_cons_of_beq {proj : α → β} {a : β} {y : α} {ys : List α}
    (h : Cmp.beq (proj y) a = true) :
    ∃ r : List α × List α, splitEq proj a (y :: ys) = (y :: r.1, r.2) := by
  rw [splitEq_cons, ite_eq_left h]
  exact ⟨_, rfl⟩

/-! ## Two block facts about `mergeTwo`

A merge that has a whole block of the right run strictly below the left run's head
emits that block first; and a merge whose left run starts at a key that is at most the
right run's keys emits the left run first. Those two facts are exactly what one turn of
the rotation merge needs. -/

theorem mergeTwo_append_right_eq {proj : α → β} {a : α} {A' : List α} (B1 : List α) :
    ∀ B2 : List α, (∀ y ∈ B1, Cmp.blt (proj y) (proj a) = true) →
      mergeTwo proj (a :: A') (B1 ++ B2) = B1 ++ mergeTwo proj (a :: A') B2 := by
  induction B1 with
  | nil => intro B2 _; rw [List.nil_append, List.nil_append]
  | cons y ys ih =>
      intro B2 h
      have hy : Cmp.blt (proj y) (proj a) = true := h y (by simp)
      have hys : ∀ z ∈ ys, Cmp.blt (proj z) (proj a) = true := fun z hz => h z (by simp [hz])
      rw [List.cons_append, mergeTwo_cons_cons_of_not_ble (Cmp.not_ble_of_blt hy), ih B2 hys,
        List.cons_append]

theorem mergeTwo_append_left_eq {proj : α → β} (A1 : List α) :
    ∀ A2 B2 : List α, (∀ x ∈ A1, ∀ y ∈ B2, Cmp.ble (proj x) (proj y) = true) →
      mergeTwo proj (A1 ++ A2) B2 = A1 ++ mergeTwo proj A2 B2 := by
  induction A1 with
  | nil => intro A2 B2 _; rw [List.nil_append, List.nil_append]
  | cons x xs ih =>
      intro A2 B2 h
      rw [List.cons_append]
      cases B2 with
      | nil => rw [mergeTwo_nil_right, mergeTwo_nil_right, List.cons_append]
      | cons y ys =>
          rw [mergeTwo_cons_cons_of_ble (h x (by simp) y (by simp)),
            ih A2 (y :: ys) (fun z hz w hw => h z (by simp [hz]) w hw), List.cons_append]

theorem Cmp.beq_self (a : β) : Cmp.beq a a = true := by
  simp [Cmp.beq, Cmp.ble_refl]

/-- In a sorted list nothing is below the head. -/
theorem keyLe_head {proj : α → β} {x : α} {xs : List α}
    (hs : Sorted (KeyLe proj) (x :: xs)) : ∀ y ∈ x :: xs, KeyLe proj x y := by
  intro y hy
  obtain ⟨h1, _⟩ := (sorted_cons_iff (KeyLe proj) x xs).mp hs
  rcases List.mem_cons.mp hy with h | h
  · rw [h]; exact Cmp.ble_refl _
  · exact h1 y h

/-- A merge of a right run that is *entirely* below the left head emits the right run
first, and then the left run. -/
theorem mergeTwo_eq_of_all_blt {proj : α → β} {a : α} {A' : List α} (B : List α) :
    ∀ (_ : ∀ y ∈ B, Cmp.blt (proj y) (proj a) = true),
      mergeTwo proj (a :: A') B = B ++ (a :: A') := by
  induction B with
  | nil => intro _; rw [List.nil_append, mergeTwo_nil_right]
  | cons y ys ih =>
      intro h
      have hy : Cmp.blt (proj y) (proj a) = true := h y (by simp)
      have hys : ∀ z ∈ ys, Cmp.blt (proj z) (proj a) = true := fun z hz => h z (by simp [hz])
      rw [mergeTwo_cons_cons_of_not_ble (Cmp.not_ble_of_blt hy), ih hys, List.cons_append]

/-! ## `inplace_merge_with_rotation_scroll_right`

The C++ turns the loop inside out: everything before `first` is already final, `A` and
`B` are the two runs that remain, and one turn rotates `B`'s block below `A`'s head to
the front and then finalizes `A`'s leading run of equal keys. Modelling the state as
`P ++ A ++ B` keeps that invariant a plain list equation, and `fuel` bounds
`A.length + B.length` as in the other loop models. -/

/-- C++'s `inplace_merge_with_rotation_scroll_right` loop. -/
def scrollRight (proj : α → β) : Nat → List α → List α → List α → List α
  | 0, P, A, B => P ++ A ++ B
  | _ + 1, P, [], B => P ++ B
  | _ + 1, P, a :: A', [] => P ++ (a :: A')
  | n + 1, P, a :: A', b :: B' =>
      match splitRight proj (proj a) (b :: B') with
      | (B1, []) => P ++ B1 ++ (a :: A')
      | (B1, B2) =>
          match splitEq proj (proj a) (a :: A') with
          | (A1, A2) => scrollRight proj n (P ++ B1 ++ A1) A2 B2

theorem scrollRight_zero (proj : α → β) (P A B : List α) :
    scrollRight proj 0 P A B = P ++ A ++ B := rfl

theorem scrollRight_succ_nil_left (proj : α → β) (n : Nat) (P B : List α) :
    scrollRight proj (n + 1) P [] B = P ++ B := rfl

theorem scrollRight_succ_nil_right (proj : α → β) (n : Nat) (P : List α) (a : α)
    (A' : List α) : scrollRight proj (n + 1) P (a :: A') [] = P ++ (a :: A') := rfl

theorem scrollRight_succ_cons (proj : α → β) (n : Nat) (P : List α) (a : α) (A' : List α)
    (b : α) (B' : List α) :
    scrollRight proj (n + 1) P (a :: A') (b :: B') =
      (match splitRight proj (proj a) (b :: B') with
       | (B1, []) => P ++ B1 ++ (a :: A')
       | (B1, B2) =>
          match splitEq proj (proj a) (a :: A') with
          | (A1, A2) => scrollRight proj n (P ++ B1 ++ A1) A2 B2) := rfl

/-- **`inplace_merge_with_rotation_scroll_right` is the stable merge**: run from the
state `P ++ A ++ B` with both runs sorted, it leaves `P` alone and appends
`mergeTwo A B`. -/
theorem scrollRight_spec (proj : α → β) (fuel : Nat) :
    ∀ (P A B : List α), A.length + B.length ≤ fuel →
      Sorted (KeyLe proj) A → Sorted (KeyLe proj) B →
      scrollRight proj fuel P A B = P ++ mergeTwo proj A B := by
  induction fuel with
  | zero =>
      intro P A B hlen _ _
      have hA : A = [] := List.eq_nil_of_length_eq_zero (by omega)
      have hB : B = [] := List.eq_nil_of_length_eq_zero (by omega)
      rw [hA, hB, scrollRight_zero, mergeTwo_nil_left, List.append_nil]
  | succ n ih =>
      intro P A B hlen hAs hBs
      match A, B with
      | [], B => rw [scrollRight_succ_nil_left, mergeTwo_nil_left]
      | a :: A', [] => rw [scrollRight_succ_nil_right, mergeTwo_nil_right]
      | a :: A', b :: B' =>
        rw [scrollRight_succ_cons]
        cases hsp : splitRight proj (proj a) (b :: B') with
        | mk B1 B2 =>
          cases B2 with
          | nil =>
              dsimp only
              have hB1 : B1 = b :: B' := by
                have h := splitRight_append proj (proj a) (b :: B')
                rw [hsp] at h
                simpa using h
              have hblt : ∀ y ∈ B1, Cmp.blt (proj y) (proj a) = true := by
                have h := splitRight_blt proj (proj a) (b :: B')
                rw [hsp] at h
                exact h
              rw [hB1] at hblt
              rw [hB1, mergeTwo_eq_of_all_blt (b :: B') hblt, List.append_assoc]
          | cons c B2' =>
              have hB : B1 ++ (c :: B2') = b :: B' := by
                have h := splitRight_append proj (proj a) (b :: B')
                rw [hsp] at h
                exact h
              have hblt : ∀ y ∈ B1, Cmp.blt (proj y) (proj a) = true := by
                have h := splitRight_blt proj (proj a) (b :: B')
                rw [hsp] at h
                exact h
              have hc : Cmp.ble (proj a) (proj c) = true := by
                refine splitRight_snd_head_ble (B := b :: B') (y := c) (ys := B2') ?_
                rw [hsp]
              have hBs2 : Sorted (KeyLe proj) (c :: B2') := by
                have h1 : c :: B2' = (b :: B').drop B1.length := by
                  rw [← List.drop_left (l₁ := B1) (l₂ := c :: B2'), ← hB]
                rw [h1]
                exact sorted_drop hBs
              cases hse : splitEq proj (proj a) (a :: A') with
              | mk A1 A2 =>
                dsimp only
                have hA : A1 ++ A2 = a :: A' := by
                  have h := splitEq_append proj (proj a) (a :: A')
                  rw [hse] at h
                  exact h
                have hA1 : ∀ y ∈ A1, Cmp.beq (proj y) (proj a) = true := by
                  have h := splitEq_beq proj (proj a) (a :: A')
                  rw [hse] at h
                  exact h
                have hA1ne : A1 ≠ [] := by
                  obtain ⟨r, hr⟩ := splitEq_cons_of_beq (proj := proj) (a := proj a) (y := a)
                    (ys := A') (Cmp.beq_self (proj a))
                  rw [hr] at hse
                  injection hse with h1 _
                  rw [← h1]
                  simp
                have hAs2 : Sorted (KeyLe proj) A2 := by
                  have h1 : A2 = (a :: A').drop A1.length := by
                    rw [← List.drop_left (l₁ := A1) (l₂ := A2), ← hA]
                  rw [h1]
                  exact sorted_drop hAs
                have hlen2 : A2.length + (c :: B2').length ≤ n := by
                  have h1 : 0 < A1.length := List.length_pos_iff.mpr hA1ne
                  have h2 : A1.length + A2.length = A'.length + 1 := by
                    rw [← List.length_append, hA]
                    simp
                  have h3 : B1.length + (c :: B2').length = B'.length + 1 := by
                    rw [← List.length_append, hB]
                    simp
                  have h4 : A'.length + 1 + (B'.length + 1) ≤ n + 1 := by
                    simpa using hlen
                  omega
                have hble : ∀ x ∈ A1, ∀ y ∈ c :: B2', Cmp.ble (proj x) (proj y) = true := by
                  intro x hx y hy
                  rw [Cmp.beq_eq (hA1 x hx)]
                  exact Cmp.ble_trans hc (keyLe_head hBs2 y hy)
                rw [ih (P ++ B1 ++ A1) A2 (c :: B2') hlen2 hAs2 hBs2,
                  ← hB, mergeTwo_append_right_eq (a := a) (A' := A') B1 (c :: B2') hblt,
                  ← hA, mergeTwo_append_left_eq A1 A2 (c :: B2') hble]
                simp only [List.append_assoc]

/-- Run to completion from an empty final prefix, the scroll-right loop *is* the stable
merge of the two runs. -/
theorem scrollRight_eq_mergeTwo (proj : α → β) {A B : List α}
    (hA : Sorted (KeyLe proj) A) (hB : Sorted (KeyLe proj) B) :
    scrollRight proj (A.length + B.length) [] A B = mergeTwo proj A B := by
  have h := scrollRight_spec proj (A.length + B.length) [] A B (Nat.le_refl _) hA hB
  simpa using h

/-! ## The scans of `inplace_merge_with_rotation_scroll_left`

The left-scrolling pass walks both runs from the right, so its two scans are written on
the *reversed* runs, where they are once again ordinary recursions. Reversing back at
the end keeps the statements in terms of the C++'s own runs. -/

/-- The A-side scan of `inplace_merge_with_rotation_scroll_left`, on the reversed `A`:
the prefix of keys strictly above `b`. The C++ walks `split_left` back while
`proj(*(split_left - 1)) > proj(*(last - 1))`. -/
def splitAboveRev (proj : α → β) (b : β) : List α → List α × List α
  | [] => ([], [])
  | y :: ys =>
      if Cmp.blt b (proj y) then
        let r := splitAboveRev proj b ys
        (y :: r.1, r.2)
      else ([], y :: ys)

/-- The B-side scan of the same pass, on the reversed `B`: the prefix of keys equal to
`b`. The C++ walks `last` back while `proj(*last) == proj(*(last - 1))`. -/
def splitEqualRev (proj : α → β) (b : β) : List α → List α × List α
  | [] => ([], [])
  | y :: ys =>
      if Cmp.beq (proj y) b then
        let r := splitEqualRev proj b ys
        (y :: r.1, r.2)
      else ([], y :: ys)

theorem splitAboveRev_nil (proj : α → β) (b : β) : splitAboveRev proj b [] = ([], []) := rfl
theorem splitEqualRev_nil (proj : α → β) (b : β) : splitEqualRev proj b [] = ([], []) := rfl

theorem splitAboveRev_cons (proj : α → β) (b : β) (y : α) (ys : List α) :
    splitAboveRev proj b (y :: ys) =
      if Cmp.blt b (proj y) then (let r := splitAboveRev proj b ys; (y :: r.1, r.2))
      else ([], y :: ys) := rfl

theorem splitEqualRev_cons (proj : α → β) (b : β) (y : α) (ys : List α) :
    splitEqualRev proj b (y :: ys) =
      if Cmp.beq (proj y) b then (let r := splitEqualRev proj b ys; (y :: r.1, r.2))
      else ([], y :: ys) := rfl

theorem splitAboveRev_append (proj : α → β) (b : β) (Ar : List α) :
    (splitAboveRev proj b Ar).1 ++ (splitAboveRev proj b Ar).2 = Ar := by
  induction Ar with
  | nil => simp [splitAboveRev_nil]
  | cons y ys ih =>
      rw [splitAboveRev_cons]
      by_cases h : Cmp.blt b (proj y) = true
      · rw [ite_eq_left h]; dsimp only; rw [List.cons_append, ih]
      · rw [ite_eq_right (by simpa using h)]; simp

theorem splitEqualRev_append (proj : α → β) (b : β) (Br : List α) :
    (splitEqualRev proj b Br).1 ++ (splitEqualRev proj b Br).2 = Br := by
  induction Br with
  | nil => simp [splitEqualRev_nil]
  | cons y ys ih =>
      rw [splitEqualRev_cons]
      by_cases h : Cmp.beq (proj y) b = true
      · rw [ite_eq_left h]; dsimp only; rw [List.cons_append, ih]
      · rw [ite_eq_right (by simpa using h)]; simp

/-- Everything the left scan takes is strictly above `b`. -/
theorem splitAboveRev_fst_blt (proj : α → β) (b : β) (Ar : List α) :
    ∀ y ∈ (splitAboveRev proj b Ar).1, Cmp.blt b (proj y) = true := by
  induction Ar with
  | nil => intro y hy; rw [splitAboveRev_nil] at hy; simp at hy
  | cons z zs ih =>
      intro y hy
      rw [splitAboveRev_cons] at hy
      by_cases h : Cmp.blt b (proj z) = true
      · rw [ite_eq_left h] at hy
        dsimp only at hy
        rcases List.mem_cons.mp hy with hy' | hy'
        · rw [hy']; exact h
        · exact ih y hy'
      · rw [ite_eq_right (by simpa using h)] at hy
        simp at hy

/-- Everything the equal scan takes has key exactly `b`. -/
theorem splitEqualRev_fst_beq (proj : α → β) (b : β) (Br : List α) :
    ∀ y ∈ (splitEqualRev proj b Br).1, Cmp.beq (proj y) b = true := by
  induction Br with
  | nil => intro y hy; rw [splitEqualRev_nil] at hy; simp at hy
  | cons z zs ih =>
      intro y hy
      rw [splitEqualRev_cons] at hy
      by_cases h : Cmp.beq (proj z) b = true
      · rw [ite_eq_left h] at hy
        dsimp only at hy
        rcases List.mem_cons.mp hy with hy' | hy'
        · rw [hy']; exact h
        · exact ih y hy'
      · rw [ite_eq_right (by simpa using h)] at hy
        simp at hy

/-- Where the left scan stops, the key is no longer strictly above `b`, so it is at most
`b`. -/
theorem splitAboveRev_snd_head_ble {proj : α → β} {b : β} :
    ∀ {Ar : List α} {y : α} {ys : List α}, (splitAboveRev proj b Ar).2 = y :: ys →
      Cmp.ble (proj y) b = true := by
  intro Ar
  induction Ar with
  | nil => intro y ys h; rw [splitAboveRev_nil] at h; simp at h
  | cons z zs ih =>
      intro y ys h
      rw [splitAboveRev_cons] at h
      by_cases hz : Cmp.blt b (proj z) = true
      · rw [ite_eq_left hz] at h
        dsimp only at h
        exact ih h
      · rw [ite_eq_right (by simpa using hz)] at h
        injection h with h1 _
        rw [← h1]
        exact Cmp.blt_eq_false_iff.mp (by simpa using hz)

/-- The equal scan takes at least the head when the head's key is `b`, which is what
makes every left turn advance. -/
theorem splitEqualRev_fst_ne_nil {proj : α → β} {b : β} {y : α} {ys : List α}
    (h : Cmp.beq (proj y) b = true) : (splitEqualRev proj b (y :: ys)).1 ≠ [] := by
  rw [splitEqualRev_cons, ite_eq_left h]
  simp

/-- `A`'s maximal suffix of keys strictly above `b`, and what stays in front of it. -/
def splitAbove (proj : α → β) (b : β) (A : List α) : List α × List α :=
  let r := splitAboveRev proj b A.reverse
  (r.2.reverse, r.1.reverse)

/-- `B`'s maximal suffix of keys equal to `b`, and what stays in front of it. -/
def splitEqual (proj : α → β) (b : β) (B : List α) : List α × List α :=
  let r := splitEqualRev proj b B.reverse
  (r.2.reverse, r.1.reverse)

theorem splitAbove_append (proj : α → β) (b : β) (A : List α) :
    (splitAbove proj b A).1 ++ (splitAbove proj b A).2 = A := by
  show (splitAboveRev proj b A.reverse).2.reverse ++
      (splitAboveRev proj b A.reverse).1.reverse = A
  rw [← List.reverse_append, splitAboveRev_append, List.reverse_reverse]

theorem splitEqual_append (proj : α → β) (b : β) (B : List α) :
    (splitEqual proj b B).1 ++ (splitEqual proj b B).2 = B := by
  show (splitEqualRev proj b B.reverse).2.reverse ++
      (splitEqualRev proj b B.reverse).1.reverse = B
  rw [← List.reverse_append, splitEqualRev_append, List.reverse_reverse]

/-- The suffix the left scan peels off is strictly above `b`. -/
theorem splitAbove_snd_blt (proj : α → β) (b : β) (A : List α) :
    ∀ y ∈ (splitAbove proj b A).2, Cmp.blt b (proj y) = true := by
  intro y hy
  have hy' : y ∈ (splitAboveRev proj b A.reverse).1 := by
    have := List.mem_reverse.mp hy
    simpa [splitAbove] using this
  exact splitAboveRev_fst_blt proj b A.reverse y hy'

/-- The suffix the equal scan peels off has key exactly `b`. -/
theorem splitEqual_snd_beq (proj : α → β) (b : β) (B : List α) :
    ∀ y ∈ (splitEqual proj b B).2, Cmp.beq (proj y) b = true := by
  intro y hy
  have hy' : y ∈ (splitEqualRev proj b B.reverse).1 := by
    have := List.mem_reverse.mp hy
    simpa [splitEqual] using this
  exact splitEqualRev_fst_beq proj b B.reverse y hy'

/-- Decomposing the front of `A` at the left scan's stopping point gives the last key it
kept, which is at most `b`. -/
theorem splitAbove_fst_le_last {proj : α → β} {b : β} {A ys : List α} {z : α}
    (h : (splitAbove proj b A).1 = ys ++ [z]) : Cmp.ble (proj z) b = true := by
  have h2 : (splitAboveRev proj b A.reverse).2 = z :: ys.reverse := by
    have hcongr := congrArg List.reverse h
    simpa [splitAbove, List.reverse_append] using hcongr
  exact splitAboveRev_snd_head_ble h2

/-- The last key the left scan keeps, when the scan keeps anything. -/
theorem splitAbove_fst_le_of_getLast {proj : α → β} {b : β} {A : List α} {z : α}
    (hz : (splitAbove proj b A).1.getLast? = some z) : Cmp.ble (proj z) b = true := by
  obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp hz
  exact splitAbove_fst_le_last hys

/-- The equal scan of `B0 ++ [z]` peels off something as soon as `z`'s key is `b`. -/
theorem splitEqual_snd_ne_nil {proj : α → β} {b : β} {B0 : List α} {z : α}
    (h : Cmp.beq (proj z) b = true) : (splitEqual proj b (B0 ++ [z])).2 ≠ [] := by
  have hrev : (splitEqualRev proj b (B0 ++ [z]).reverse).1 ≠ [] := by
    have hr : (B0 ++ [z]).reverse = z :: B0.reverse := by
      rw [List.reverse_append, List.reverse_singleton, List.singleton_append]
    rw [hr]
    exact splitEqualRev_fst_ne_nil h
  intro hnil
  have hz0 : (splitEqualRev proj b (B0 ++ [z]).reverse).1 = [] := by
    have h1 : (splitEqualRev proj b (B0 ++ [z]).reverse).1.reverse = [] := by
      simpa [splitEqual] using hnil
    rw [← List.reverse_reverse (splitEqualRev proj b (B0 ++ [z]).reverse).1, h1,
      List.reverse_nil]
  exact hrev hz0

/-! ## Suffix block facts about `mergeTwo`

The left-scrolling pass peels its finished tail off the *back* of the merge, so it needs
the mirror block facts: a left run that is entirely above the right run goes last, and a
left run whose keys are at most a right-run suffix goes in front of it. -/

theorem mergeTwo_eq_of_all_gt {proj : α → β} {A : List α} (B : List α) :
    ∀ (_ : ∀ y ∈ A, ∀ x ∈ B, Cmp.blt (proj x) (proj y) = true),
      mergeTwo proj A B = B ++ A := by
  induction B with
  | nil => intro _; rw [mergeTwo_nil_right, List.nil_append]
  | cons b Bs ih =>
      intro h
      match A with
      | [] => rw [mergeTwo_nil_left, List.append_nil]
      | a :: As =>
          have hba : Cmp.blt (proj b) (proj a) = true := h a (by simp) b (by simp)
          have hBs : ∀ y ∈ a :: As, ∀ x ∈ Bs, Cmp.blt (proj x) (proj y) = true :=
            fun y hy x hx => h y hy x (by simp [hx])
          rw [mergeTwo_cons_cons_of_not_ble (Cmp.not_ble_of_blt hba), ih hBs, List.cons_append]

theorem mergeTwo_append_left_suffix {proj : α → β} {A2 : List α} (A1 : List α) :
    ∀ B : List α, (∀ y ∈ A2, ∀ x ∈ B, Cmp.blt (proj x) (proj y) = true) →
      mergeTwo proj (A1 ++ A2) B = mergeTwo proj A1 B ++ A2 := by
  induction A1 with
  | nil => intro B h; rw [mergeTwo_nil_left]; exact mergeTwo_eq_of_all_gt (A := A2) B h
  | cons x xs ih =>
      have main : ∀ B : List α, (∀ y ∈ A2, ∀ x ∈ B, Cmp.blt (proj x) (proj y) = true) →
          mergeTwo proj (x :: (xs ++ A2)) B = mergeTwo proj (x :: xs) B ++ A2 := by
        intro B
        induction B with
        | nil => intro _; rw [mergeTwo_nil_right, mergeTwo_nil_right, List.cons_append]
        | cons y ys ihB =>
            intro h
            by_cases hxy : Cmp.ble (proj x) (proj y) = true
            · rw [mergeTwo_cons_cons_of_ble hxy, mergeTwo_cons_cons_of_ble hxy,
                ih (y :: ys) h, List.cons_append]
            · have hxy' : Cmp.ble (proj x) (proj y) = false := by simpa using hxy
              rw [mergeTwo_cons_cons_of_not_ble hxy', mergeTwo_cons_cons_of_not_ble hxy',
                ihB (fun z hz w hw => h z hz w (by simp [hw])), List.cons_append]
      intro B h
      rw [List.cons_append]
      exact main B h

theorem mergeTwo_append_right_suffix {proj : α → β} {B2 : List α} (B1 : List α) :
    ∀ A : List α, (∀ x ∈ A, ∀ y ∈ B2, Cmp.ble (proj x) (proj y) = true) →
      mergeTwo proj A (B1 ++ B2) = mergeTwo proj A B1 ++ B2 := by
  induction B1 with
  | nil =>
      intro A h
      have h2 := mergeTwo_append_left_eq A [] B2 (fun x hx y hy => h x hx y hy)
      rw [List.append_nil, mergeTwo_nil_left] at h2
      rw [List.nil_append, mergeTwo_nil_right]
      exact h2
  | cons b Bs ih =>
      have main : ∀ A : List α, (∀ x ∈ A, ∀ y ∈ B2, Cmp.ble (proj x) (proj y) = true) →
          mergeTwo proj A (b :: (Bs ++ B2)) = mergeTwo proj A (b :: Bs) ++ B2 := by
        intro A
        induction A with
        | nil => intro _; rw [mergeTwo_nil_left, mergeTwo_nil_left, List.cons_append]
        | cons a As ihA =>
            intro h
            by_cases hab : Cmp.ble (proj a) (proj b) = true
            · rw [mergeTwo_cons_cons_of_ble hab, mergeTwo_cons_cons_of_ble hab,
                ihA (fun x hx y hy => h x (by simp [hx]) y hy), List.cons_append]
            · have hab' : Cmp.ble (proj a) (proj b) = false := by simpa using hab
              rw [mergeTwo_cons_cons_of_not_ble hab', mergeTwo_cons_cons_of_not_ble hab',
                ih (a :: As) (fun x hx y hy => h x hx y (by simp [hy])), List.cons_append]
      intro A h
      rw [List.cons_append]
      exact main A h

/-- Split `R` at the maximal prefix whose keys equal the key of `R`'s head - the C++'s
`last--; while (mid < last && proj(*last) == proj(*(last - 1))) last--;` seen from the
reversed side. The C++ compares with the *previous* element, which under sortedness is
the same as comparing with the head. -/
def splitEqualHead (proj : α → β) : List α → List α × List α
  | [] => ([], [])
  | y :: ys => splitEqualRev proj (proj y) (y :: ys)

theorem splitEqualHead_nil (proj : α → β) : splitEqualHead proj [] = ([], []) := rfl

theorem splitEqualHead_cons (proj : α → β) (y : α) (ys : List α) :
    splitEqualHead proj (y :: ys) = splitEqualRev proj (proj y) (y :: ys) := rfl

theorem splitEqualHead_append (proj : α → β) (R : List α) :
    (splitEqualHead proj R).1 ++ (splitEqualHead proj R).2 = R := by
  match R with
  | [] => simp [splitEqualHead_nil]
  | y :: ys => rw [splitEqualHead_cons, splitEqualRev_append]

theorem splitEqualHead_fst_beq (proj : α → β) (y : α) (ys : List α) :
    ∀ x ∈ (splitEqualHead proj (y :: ys)).1, Cmp.beq (proj x) (proj y) = true := by
  intro x hx
  rw [splitEqualHead_cons] at hx
  exact splitEqualRev_fst_beq proj (proj y) (y :: ys) x hx

theorem splitEqualHead_fst_ne_nil (proj : α → β) (y : α) (ys : List α) :
    (splitEqualHead proj (y :: ys)).1 ≠ [] := by
  rw [splitEqualHead_cons]
  exact splitEqualRev_fst_ne_nil (Cmp.beq_self (proj y))

/-- One turn of C++'s `inplace_merge_with_rotation_scroll_left`, as a state update: the
new left run, the new right run and the finished tail. `b` is the right region's last
element, `leftSplit`'s second component the part of the left run strictly above its key,
and the reversed region is split at its maximal head-keyed prefix. -/
def scrollLeftTurn (proj : α → β) (A B Q : List α) : List α × List α × List α :=
  match A, B.reverse with
  | [], _ => (A, B, Q)
  | _, [] => (A, B, Q)
  | _, b :: Br =>
      let sa := splitAbove proj (proj b) A
      let se := splitEqualHead proj (b :: Br)
      (sa.1, se.2.reverse, se.1.reverse ++ sa.2 ++ Q)

/-- C++'s `inplace_merge_with_rotation_scroll_left`, run for `fuel` turns. A turn that
has nothing to move leaves the state alone, so `fuel` only has to be large enough. -/
def scrollLeft (proj : α → β) : Nat → List α → List α → List α → List α
  | 0, A, B, Q => A ++ B ++ Q
  | n + 1, A, B, Q =>
      let t := scrollLeftTurn proj A B Q
      scrollLeft proj n t.1 t.2.1 t.2.2

theorem scrollLeft_zero (proj : α → β) (A B Q : List α) :
    scrollLeft proj 0 A B Q = A ++ B ++ Q := rfl

theorem scrollLeft_succ (proj : α → β) (n : Nat) (A B Q : List α) :
    scrollLeft proj (n + 1) A B Q =
      (let t := scrollLeftTurn proj A B Q; scrollLeft proj n t.1 t.2.1 t.2.2) := rfl

theorem scrollLeftTurn_nil_left (proj : α → β) (B Q : List α) :
    scrollLeftTurn proj [] B Q = ([], B, Q) := rfl

theorem scrollLeftTurn_cons (proj : α → β) (a : α) (As : List α) (Br : List α) (b : α)
    (Q : List α) :
    scrollLeftTurn proj (a :: As) (Br ++ [b]) Q =
      (match splitAbove proj (proj b) (a :: As) with
       | (A1, A2) =>
         match splitEqualHead proj (b :: Br.reverse) with
         | (B2r, B1r) => (A1, B1r.reverse, B2r.reverse ++ A2 ++ Q)) := by
  unfold scrollLeftTurn
  rw [show (Br ++ [b]).reverse = b :: Br.reverse from by
    rw [List.reverse_append, List.reverse_singleton, List.singleton_append]]

/-- **A left turn is a `mergeTwo` split.** If the left run ends in a part `A2` that is
strictly above the right run, and the right run splits as `B1 ++ B2` where `B2` carries a
key no key of `A1` exceeds, then merging `A1 ++ A2` with `B1 ++ B2` is `mergeTwo A1 B1`,
then `B2`, then `A2`. -/
theorem mergeTwo_split_tail {proj : α → β} {A1 A2 B1 B2 : List α}
    (hA2 : ∀ y ∈ A2, ∀ x ∈ B1 ++ B2, Cmp.blt (proj x) (proj y) = true)
    (hA1B2 : ∀ x ∈ A1, ∀ y ∈ B2, Cmp.ble (proj x) (proj y) = true) :
    mergeTwo proj (A1 ++ A2) (B1 ++ B2) = mergeTwo proj A1 B1 ++ (B2 ++ A2) := by
  rw [mergeTwo_append_left_suffix A1 (B1 ++ B2) hA2,
    mergeTwo_append_right_suffix B1 A1 hA1B2, List.append_assoc]

/-- A turn with an empty left or right run has nothing to move, so the loop returns the
state unchanged however much fuel it is given. -/
theorem scrollLeft_eq_of_nil {proj : α → β} (fuel : Nat) :
    ∀ (A B Q : List α), (A = [] ∨ B = []) → scrollLeft proj fuel A B Q = A ++ B ++ Q := by
  induction fuel with
  | zero => intro A B Q _; rw [scrollLeft_zero]
  | succ n ih =>
      intro A B Q h
      rw [scrollLeft_succ]
      match A, B with
      | [], B =>
          rw [scrollLeftTurn_nil_left]
          dsimp only
          exact ih [] B Q (Or.inl rfl)
      | a :: As, [] =>
          dsimp only [scrollLeftTurn]
          exact ih (a :: As) [] Q (Or.inr rfl)

/-- **`inplace_merge_with_rotation_scroll_left` is the stable merge**: run from the state
`A ++ B ++ Q` with both runs sorted and `fuel` large enough, it leaves the finished tail
`Q` alone and prepends `mergeTwo A B`. -/
theorem scrollLeft_spec (proj : α → β) (fuel : Nat) :
    ∀ (A B Q : List α), A.length + B.length ≤ fuel →
      Sorted (KeyLe proj) A → Sorted (KeyLe proj) B →
      scrollLeft proj fuel A B Q = mergeTwo proj A B ++ Q := by
  induction fuel with
  | zero =>
      intro A B Q hlen _ _
      have hA : A = [] := List.eq_nil_of_length_eq_zero (by omega)
      have hB : B = [] := List.eq_nil_of_length_eq_zero (by omega)
      rw [hA, hB, scrollLeft_zero, mergeTwo_nil_left]
      simp
  | succ n ih =>
      intro A B Q hlen hAs hBs
      cases hBr : B.reverse with
      | nil =>
          have hBnil : B = [] := by
            have h := congrArg List.reverse hBr
            rw [List.reverse_reverse, List.reverse_nil] at h
            exact h
          subst hBnil
          match A with
          | [] =>
              rw [scrollLeft_eq_of_nil (n + 1) [] [] Q (Or.inl rfl), mergeTwo_nil_left]
              simp
          | a :: As =>
              rw [scrollLeft_eq_of_nil (n + 1) (a :: As) [] Q (Or.inr rfl), mergeTwo_nil_right]
              simp
      | cons b Br =>
          have hB : B = Br.reverse ++ [b] := by
            have h := congrArg List.reverse hBr
            rw [List.reverse_reverse] at h
            rw [h, List.reverse_cons]
          rw [hB] at hlen hBs ⊢
          match A with
          | [] =>
              rw [scrollLeft_eq_of_nil (n + 1) [] (Br.reverse ++ [b]) Q (Or.inl rfl),
                mergeTwo_nil_left]
              simp
          | a :: As =>
              rw [scrollLeft_succ]
              dsimp only [scrollLeftTurn]
              rw [show (Br.reverse ++ [b]).reverse = b :: Br from by
                rw [List.reverse_append, List.reverse_singleton, List.singleton_append,
                  List.reverse_reverse]]
              dsimp only
              cases hsa : splitAbove proj (proj b) (a :: As) with
              | mk A1 A2 =>
                cases hse : splitEqualHead proj (b :: Br) with
                | mk B2r B1r =>
                  dsimp only
                  have hsplitA : A1 ++ A2 = a :: As := by
                    have h := splitAbove_append proj (proj b) (a :: As)
                    rw [hsa] at h
                    exact h
                  have hsA : Sorted (KeyLe proj) (A1 ++ A2) := by rw [hsplitA]; exact hAs
                  have hA1 : Sorted (KeyLe proj) A1 := (List.pairwise_append.mp hsA).1
                  have hbA2 : ∀ y ∈ A2, Cmp.blt (proj b) (proj y) = true := by
                    intro y hy
                    exact splitAbove_snd_blt proj (proj b) (a :: As) y (by rw [hsa]; exact hy)
                  have hBleb : ∀ x ∈ Br.reverse ++ [b], Cmp.ble (proj x) (proj b) = true :=
                    keyLe_getLast (proj := proj) (l := Br.reverse ++ [b]) (z := b) hBs
                      List.getLast?_concat
                  have hA2gtB : ∀ y ∈ A2, ∀ x ∈ Br.reverse ++ [b],
                      Cmp.blt (proj x) (proj y) = true :=
                    fun y hy x hx => Cmp.blt_of_ble_of_blt (hBleb x hx) (hbA2 y hy)
                  have hBsplit : Br.reverse ++ [b] = B1r.reverse ++ B2r.reverse := by
                    have h := splitEqualHead_append proj (b :: Br)
                    rw [hse] at h
                    have h2 := congrArg List.reverse h
                    simpa [List.reverse_append, List.reverse_cons, List.reverse_reverse] using h2.symm
                  have hB1 : Sorted (KeyLe proj) B1r.reverse :=
                    (List.pairwise_append.mp (by rw [← hBsplit]; exact hBs)).1
                  have hA1leb : ∀ x ∈ A1, Cmp.ble (proj x) (proj b) = true := by
                    rcases List.eq_nil_or_concat A1 with hA1nil | ⟨A1', z, hA1z⟩
                    · intro x hx; rw [hA1nil] at hx; simp at hx
                    · have hA1z' : A1 = A1' ++ [z] := by rw [hA1z, List.concat_eq_append]
                      have hzle : Cmp.ble (proj z) (proj b) = true := by
                        refine splitAbove_fst_le_last (A := a :: As) (ys := A1') (z := z) ?_
                        rw [hsa]
                        exact hA1z'
                      have hget : A1.getLast? = some z := by
                        rw [hA1z']
                        exact List.getLast?_concat
                      have hall := keyLe_getLast hA1 hget
                      intro x hx
                      exact Cmp.ble_trans (hall x hx) hzle
                  have hB2r_eq : B2r = (splitEqualHead proj (b :: Br)).1 := by simp [hse]
                  have hkeyge : ∀ y ∈ B2r, Cmp.ble (proj b) (proj y) = true := by
                    intro y hy
                    rw [hB2r_eq] at hy
                    rw [Cmp.beq_eq (splitEqualHead_fst_beq proj b Br y hy)]
                    exact Cmp.ble_refl _
                  have hA1B2 : ∀ x ∈ A1, ∀ y ∈ B2r.reverse, Cmp.ble (proj x) (proj y) = true :=
                    fun x hx y hy => Cmp.ble_trans (hA1leb x hx) (hkeyge y (List.mem_reverse.mp hy))
                  have hB2r_ne : B2r ≠ [] := by
                    rw [hB2r_eq]
                    exact splitEqualHead_fst_ne_nil proj b Br
                  have hA2gtB' : ∀ y ∈ A2, ∀ x ∈ B1r.reverse ++ B2r.reverse,
                      Cmp.blt (proj x) (proj y) = true := by
                    rw [← hBsplit]
                    exact hA2gtB
                  have hlen' : A1.length + B1r.reverse.length ≤ n := by
                    have h1 : A1.length + A2.length = As.length + 1 := by
                      have h := congrArg List.length hsplitA
                      simpa using h
                    have h2 : B2r.length + B1r.length = Br.length + 1 := by
                      have h := splitEqualHead_append proj (b :: Br)
                      rw [hse] at h
                      have hlen2 := congrArg List.length h
                      simp [List.length_append] at hlen2
                      omega
                    have h3 : 1 ≤ B2r.length := List.length_pos_iff.mpr hB2r_ne
                    have h4 : (a :: As).length + (Br.reverse ++ [b]).length ≤ n + 1 := hlen
                    simp only [List.length_cons, List.length_append, List.length_nil,
                      List.length_reverse] at h4
                    simp only [List.length_reverse]
                    omega
                  rw [ih A1 B1r.reverse (B2r.reverse ++ A2 ++ Q) hlen' hA1 hB1,
                    ← hsplitA, hBsplit,
                    mergeTwo_split_tail (A1 := A1) (A2 := A2) (B1 := B1r.reverse)
                      (B2 := B2r.reverse) hA2gtB' hA1B2]
                  simp only [List.append_assoc]

/-! ## `inplace_merge_with_rotation` -/

/-- C++'s `inplace_merge_with_rotation`: merge the adjacent runs `[first, mid)` and
`[mid, last)` of `l`, choosing the scrolling direction by which run is shorter - the
left one scrolls right when it is shorter, otherwise the right one scrolls left. -/
def mergeByRotationStable (proj : α → β) (l : List α) (first mid last : Nat) : List α :=
  let A := (l.drop first).take (mid - first)
  let B := (l.drop mid).take (last - mid)
  let P := l.take first
  let Q := l.drop last
  if mid - first < last - mid then scrollRight proj (A.length + B.length) P A B ++ Q
  else P ++ scrollLeft proj (A.length + B.length) A B Q

/-- **`inplace_merge_with_rotation` is the stable merge of its two runs**: the range
`[first, last)` comes out as `mergeTwo` of the two runs, and everything outside it is
untouched. Whichever direction the C++ picks, the result is the same. -/
theorem mergeByRotationStable_spec (proj : α → β) {l : List α} {first mid last : Nat}
    (hA : Sorted (KeyLe proj) ((l.drop first).take (mid - first)))
    (hB : Sorted (KeyLe proj) ((l.drop mid).take (last - mid))) :
    mergeByRotationStable proj l first mid last
      = l.take first ++ mergeTwo proj ((l.drop first).take (mid - first))
          ((l.drop mid).take (last - mid)) ++ l.drop last := by
  unfold mergeByRotationStable
  by_cases h : mid - first < last - mid
  · rw [ite_eq_left h]
    have hs := scrollRight_spec proj
      (((l.drop first).take (mid - first)).length +
        ((l.drop mid).take (last - mid)).length)
      (l.take first) ((l.drop first).take (mid - first))
      ((l.drop mid).take (last - mid)) (Nat.le_refl _) hA hB
    rw [hs]
  · rw [ite_eq_right (by simpa using h)]
    have hs := scrollLeft_spec proj
      (((l.drop first).take (mid - first)).length +
        ((l.drop mid).take (last - mid)).length)
      ((l.drop first).take (mid - first)) ((l.drop mid).take (last - mid))
      (l.drop last) (Nat.le_refl _) hA hB
    rw [hs]
    simp only [List.append_assoc]

/-- A successful pick puts `x`'s key strictly above every key already kept. -/
theorem keepUnique_blt {proj : α → β} {max : Nat} {picked : List α} {x : α}
    (hs : Sorted (KeyLe proj) picked) (hle : ∀ z ∈ picked, KeyLe proj z x)
    (hk : keepUnique proj max picked x = true) :
    ∀ z ∈ picked, Cmp.blt (proj z) (proj x) = true := by
  intro z hz
  cases hl : picked.getLast? with
  | none =>
      rw [List.getLast?_eq_none_iff] at hl
      subst hl
      simp at hz
  | some y =>
      have hbeq : Cmp.beq (proj y) (proj x) = false := by
        cases hb : Cmp.beq (proj y) (proj x) with
        | false => rfl
        | true =>
            simp only [keepUnique, hl] at hk
            rw [hb] at hk
            simp at hk
      have hy_le : Cmp.ble (proj y) (proj x) = true :=
        hle y (by
          obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp hl
          rw [hys]
          exact List.mem_append_right _ (by simp))
      have hxy : Cmp.ble (proj x) (proj y) = false := by
        cases hb : Cmp.ble (proj x) (proj y) with
        | false => rfl
        | true =>
            simp [Cmp.beq, hy_le, hb] at hbeq
      have hyx : Cmp.blt (proj y) (proj x) = true := by
        simp [Cmp.blt, hy_le, hxy]
      exact Cmp.blt_of_ble_of_blt (keyLe_getLast hs hl z hz) hyx

/-- A failed pick test either hits the `max` limit or finds `x`'s key already kept. -/
theorem keepUnique_eq_false {proj : α → β} {max : Nat} {picked : List α} {x : α}
    (hk : keepUnique proj max picked x = false) :
    max ≤ picked.length ∨ ∃ y, picked.getLast? = some y ∧ Cmp.beq (proj y) (proj x) = true := by
  by_cases hlen : picked.length < max
  · right
    cases hl : picked.getLast? with
    | none =>
        rw [List.getLast?_eq_none_iff] at hl
        subst hl
        have h : keepUnique proj max [] x = true := by
          rw [keepUnique, List.getLast?_nil, Bool.and_true]
          exact decide_eq_true hlen
        rw [h] at hk
        exact absurd hk (by simp)
    | some y =>
        refine ⟨y, rfl, ?_⟩
        cases hb : Cmp.beq (proj y) (proj x) with
        | true => rfl
        | false =>
            exfalso
            have hk' := hk
            rw [keepUnique] at hk'
            simp only [hl] at hk'
            rw [hb] at hk'
            simp [hlen] at hk'
  · left; omega

/-- A sublist of a sorted list is sorted. -/
theorem sorted_of_sublist {R : α → α → Prop} :
    ∀ {l₁ l₂ : List α}, List.Sublist l₁ l₂ → Sorted R l₂ → Sorted R l₁ := by
  intro l₁ l₂ h
  induction h with
  | slnil => intro _; exact sorted_nil _
  | cons b _ ih => intro hs; exact ih (List.pairwise_cons.mp hs).2
  | cons_cons b h ih =>
      intro hs
      obtain ⟨h1, h2⟩ := List.pairwise_cons.mp hs
      exact List.Pairwise.cons (fun y hy => h1 y (List.Sublist.subset h hy)) (ih h2)

/-- A successful pick test implies the buffer has not reached `max`. -/
theorem keepUnique_lt {proj : α → β} {max : Nat} {picked : List α} {x : α}
    (hk : keepUnique proj max picked x = true) : picked.length < max := by
  by_cases h : picked.length < max
  · exact h
  · have hc : keepUnique proj max picked x = false := by
      rw [keepUnique]
      simp [h]
    rw [hc] at hk
    exact absurd hk (by simp)

/-- The `k`-subsequence of a cons, as an append - the form the per-key argument wants. -/
theorem keyFilter_cons' (proj : α → β) (k : β) (x : α) (xs : List α) :
    keyFilter proj k (x :: xs) = keyFilter proj k [x] ++ keyFilter proj k xs := by
  cases hx : Cmp.beq (proj x) k with
  | false =>
      rw [keyFilter_cons_of_not_beq (by rw [hx]; exact Bool.false_ne_true),
        keyFilter_cons_of_not_beq (by rw [hx]; exact Bool.false_ne_true), keyFilter_nil,
        List.nil_append]
  | true =>
      rw [keyFilter_cons_of_beq hx, keyFilter_cons_of_beq hx, keyFilter_nil,
        List.singleton_append]

/-- The elements the loop skips are a sublist of what it was given, so they keep their
order. This needs no accumulator invariant: the loop only ever appends to the buffer or
appends to the skipped part. -/
theorem uniqueLimitAux_sublist (proj : α → β) (max : Nat) :
    ∀ picked l : List α, List.Sublist (uniqueLimitAux proj max picked l).2 l := by
  intro picked l
  induction l generalizing picked with
  | nil => rw [uniqueLimitAux_nil]; exact List.Sublist.slnil
  | cons x xs ih =>
      rw [uniqueLimitAux_cons]
      by_cases hk : keepUnique proj max picked x = true
      · rw [ite_eq_left hk]
        exact List.Sublist.cons x (ih (picked ++ [x]))
      · rw [ite_eq_right (by simpa using hk)]
        dsimp only
        exact List.Sublist.cons_cons x (ih picked)

/-- Once the buffer has reached `max`, the loop moves nothing at all. -/
theorem uniqueLimitAux_stop (proj : α → β) (max : Nat) :
    ∀ picked l : List α, max ≤ picked.length →
      (uniqueLimitAux proj max picked l).1 = picked ∧ (uniqueLimitAux proj max picked l).2 = l := by
  intro picked l
  induction l generalizing picked with
  | nil => intro _; rw [uniqueLimitAux_nil]; exact ⟨rfl, rfl⟩
  | cons x xs ih =>
      intro hmax
      have hk : keepUnique proj max picked x = false := by
        rw [keepUnique]
        simp [Nat.not_lt.mpr hmax]
      rw [uniqueLimitAux_cons, ite_eq_right (by simpa using hk)]
      dsimp only
      obtain ⟨hb, hr⟩ := ih picked hmax
      exact ⟨hb, by rw [hr]⟩

/-- Keeping `x` maintains the accumulator invariant. -/
theorem uniqueInv_keep {proj : α → β} (max : Nat) {picked l : List α} {x : α}
    (h : UniqueInv proj picked (x :: l)) (hk : keepUnique proj max picked x = true) :
    UniqueInv proj (picked ++ [x]) l := by
  obtain ⟨hps, hpn, hls, hle⟩ := h
  obtain ⟨hxle, hxs⟩ := (sorted_cons_iff (KeyLe proj) x l).mp hls
  exact ⟨sorted_append hps (sorted_singleton _ _) (fun a ha b hb => by
      rw [List.mem_singleton] at hb
      rw [hb]
      exact hle a ha x (by simp)),
    keepUnique_keysNodup hps hpn (fun y hy => hle y hy x (by simp)) hk,
    hxs,
    fun y hy z hz => by
      rcases List.mem_append.mp hy with hy' | hy'
      · exact hle y hy' z (List.mem_cons_of_mem x hz)
      · rw [List.mem_singleton] at hy'
        rw [hy']
        exact hxle z hz⟩

/-- Skipping maintains the accumulator invariant. -/
theorem uniqueInv_skip {proj : α → β} {picked l : List α} {x : α}
    (h : UniqueInv proj picked (x :: l)) : UniqueInv proj picked l :=
  ⟨h.1, h.2.1, ((sorted_cons_iff (KeyLe proj) x l).mp h.2.2.1).2,
    fun y hy z hz => h.2.2.2 y hy z (List.mem_cons_of_mem x hz)⟩

/-- **What the loop keeps.** The buffer is the accumulator followed by the elements it
newly kept, and those new elements' keys are *strictly* above every key of the
accumulator - which is what tells the two apart. -/
theorem uniqueLimitAux_buffer_split (proj : α → β) (max : Nat) :
    ∀ picked l : List α, UniqueInv proj picked l →
      ∃ extra : List α, (uniqueLimitAux proj max picked l).1 = picked ++ extra ∧
        ∀ y ∈ extra, ∀ z ∈ picked, Cmp.blt (proj z) (proj y) = true := by
  intro picked l
  induction l generalizing picked with
  | nil =>
      intro _
      rw [uniqueLimitAux_nil]
      refine ⟨[], ?_, by simp⟩
      show picked = picked ++ []
      exact (List.append_nil picked).symm
  | cons x xs ih =>
      intro h
      rw [uniqueLimitAux_cons]
      by_cases hk : keepUnique proj max picked x = true
      · rw [ite_eq_left hk]
        have hnew : ∀ z ∈ picked, Cmp.blt (proj z) (proj x) = true :=
          keepUnique_blt h.1 (fun w hw => h.2.2.2 w hw x (by simp)) hk
        obtain ⟨extra, hbuf, habove⟩ := ih (picked ++ [x]) (uniqueInv_keep max h hk)
        refine ⟨x :: extra, ?_, ?_⟩
        · rw [hbuf, List.append_assoc, List.singleton_append]
        · intro y hy z hz
          rcases List.mem_cons.mp hy with hyx | hy'
          · rw [hyx]
            exact hnew z hz
          · exact habove y hy' z (List.mem_append_left [x] hz)
      · rw [ite_eq_right (by simpa using hk)]
        dsimp only
        obtain ⟨extra, hbuf, habove⟩ := ih picked (uniqueInv_skip h)
        exact ⟨extra, hbuf, habove⟩

/-- **The loop keeps every equal-key subsequence**, in the sense that the buffer followed
by the skipped elements has the same `k`-subsequence as the accumulator followed by the
input. This is the property that makes the buffer usable as lane labels later on: it
says that a key's first occurrence really does come first. -/
theorem uniqueLimitAux_keyFilter (proj : α → β) (max : Nat) :
    ∀ picked l : List α, UniqueInv proj picked l →
      ∀ k : β, keyFilter proj k (uniqueLimitAux proj max picked l).1 ++
          keyFilter proj k (uniqueLimitAux proj max picked l).2 =
        keyFilter proj k (picked ++ l) := by
  intro picked l
  induction l generalizing picked with
  | nil =>
      intro _ k
      rw [uniqueLimitAux_nil]
      show keyFilter proj k picked ++ keyFilter proj k [] = keyFilter proj k (picked ++ [])
      rw [keyFilter_nil, List.append_nil, List.append_nil]
  | cons x xs ih =>
      intro h k
      rw [uniqueLimitAux_cons]
      by_cases hk : keepUnique proj max picked x = true
      · rw [ite_eq_left hk]
        rw [ih (picked ++ [x]) (uniqueInv_keep max h hk) k, List.append_assoc,
          List.singleton_append]
      · rw [ite_eq_right (by simpa using hk)]
        dsimp only
        have hinv : UniqueInv proj picked xs := uniqueInv_skip h
        obtain ⟨extra, hbuf, habove⟩ := uniqueLimitAux_buffer_split proj max picked xs hinv
        have hkf := ih picked hinv k
        rw [keyFilter_append (proj := proj) k picked (x :: xs)]
        by_cases hx : Cmp.beq (proj x) k = true
        · rcases keepUnique_eq_false (by simpa using hk) with hmax | ⟨y, hy, hbeq⟩
          · obtain ⟨hb, hr⟩ := uniqueLimitAux_stop proj max picked xs hmax
            rw [hb, hr]
          · have hy_picked : y ∈ picked := by
              obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp hy
              rw [hys]
              exact List.mem_append_right _ (by simp)
            have hyk : Cmp.beq (proj y) k = true := by
              rw [Cmp.beq_eq hbeq, Cmp.beq_eq hx]
              exact Cmp.beq_self k
            have hExtra : keyFilter proj k extra = [] := by
              refine keyFilter_eq_nil_of_all extra (fun w hw => ?_)
              have hb' : Cmp.blt (proj y) (proj w) = true := habove w hw y hy_picked
              rw [Cmp.beq_eq hyk] at hb'
              rw [Cmp.beq_comm (proj w) k]
              exact Cmp.not_beq_of_blt hb'
            have hA : keyFilter proj k (uniqueLimitAux proj max picked xs).1 =
                keyFilter proj k picked := by
              rw [hbuf, keyFilter_append (proj := proj) k picked extra, hExtra, List.append_nil]
            have hCan : keyFilter proj k (uniqueLimitAux proj max picked xs).2 =
                keyFilter proj k xs := by
              have hh := hkf
              rw [keyFilter_append (proj := proj) k picked xs, hA] at hh
              exact List.append_cancel_left hh
            simp only [hA, hCan, keyFilter_cons_of_beq hx]
        · simp only [keyFilter_cons_of_not_beq hx]
          rw [hkf, keyFilter_append (proj := proj) k picked xs]

theorem uniqueLimit_rest_sorted (proj : α → β) (max : Nat) {l : List α}
    (hl : Sorted (KeyLe proj) l) : Sorted (KeyLe proj) (uniqueLimit proj max l).2 :=
  sorted_of_sublist (uniqueLimitAux_sublist proj max [] l) hl

theorem uniqueLimit_keyFilter (proj : α → β) (max : Nat) {l : List α}
    (hl : Sorted (KeyLe proj) l) (k : β) :
    keyFilter proj k (uniqueLimit proj max l).1 ++ keyFilter proj k (uniqueLimit proj max l).2 =
      keyFilter proj k l := by
  have h := uniqueLimitAux_keyFilter proj max [] l ⟨sorted_nil _, List.Pairwise.nil, hl, by simp⟩ k
  show keyFilter proj k (uniqueLimitAux proj max [] l).1 ++
      keyFilter proj k (uniqueLimitAux proj max [] l).2 = keyFilter proj k l
  simpa using h

/-- **The full contract of the three-argument `stable_unique_limit`** on a sorted range:
the buffer is sorted with pairwise different keys, the skipped elements stay sorted and
in order, the whole range is only permuted, and - the point of the routine - the buffer
followed by the skipped elements has the same `k`-subsequence as the input, for every
key. -/
theorem uniqueLimit_spec (proj : α → β) (max : Nat) {l : List α} (hl : Sorted (KeyLe proj) l) :
    Sorted (KeyLe proj) (uniqueLimit proj max l).1 ∧
    KeysNodup proj (uniqueLimit proj max l).1 ∧
    Sorted (KeyLe proj) (uniqueLimit proj max l).2 ∧
    List.Sublist (uniqueLimit proj max l).2 l ∧
    ((uniqueLimit proj max l).1 ++ (uniqueLimit proj max l).2).Perm l ∧
    ∀ k : β, keyFilter proj k (uniqueLimit proj max l).1 ++
        keyFilter proj k (uniqueLimit proj max l).2 = keyFilter proj k l :=
  ⟨(uniqueLimit_sorted_keysNodup proj max hl).1,
    (uniqueLimit_sorted_keysNodup proj max hl).2,
    uniqueLimit_rest_sorted proj max hl,
    uniqueLimitAux_sublist proj max [] l,
    uniqueLimit_perm proj max l,
    uniqueLimit_keyFilter proj max hl⟩

/-! ## The four-argument `stable_unique_limit`

The C++ overload does the same job for two adjacent sorted runs at once: it takes the
buffer of the right run, merges the left run with it (`inplace_merge_with_rotation`,
which `mergeByRotationStable` mirrors, so the merged range is `mergeTwo L R.buf`), and
then takes the buffer of that merged part. The result is the buffer, what is left of the
merged part, and what is left of the right run - the whole range in three pieces. -/

/-- C++'s four-argument `stable_unique_limit` on the adjacent sorted runs `L` and `R`. -/
def uniqueLimitRange (proj : α → β) (max : Nat) (L R : List α) : List α × List α × List α :=
  let rR := uniqueLimit proj max R
  let rL := uniqueLimit proj max (mergeTwo proj L rR.1)
  (rL.1, rL.2, rR.2)

/-- **The four-argument `stable_unique_limit`**: the buffer is sorted with pairwise
different keys, both remainders are sorted, the whole range is only permuted, and every
`k`-subsequence survives - so the buffer's element for a key is that key's first
occurrence in the *whole* range, which is what the later stages need. -/
theorem uniqueLimitRange_spec (proj : α → β) (max : Nat) {L R : List α}
    (hL : Sorted (KeyLe proj) L) (hR : Sorted (KeyLe proj) R) :
    Sorted (KeyLe proj) (uniqueLimitRange proj max L R).1 ∧
    KeysNodup proj (uniqueLimitRange proj max L R).1 ∧
    Sorted (KeyLe proj) (uniqueLimitRange proj max L R).2.1 ∧
    Sorted (KeyLe proj) (uniqueLimitRange proj max L R).2.2 ∧
    ((uniqueLimitRange proj max L R).1 ++ (uniqueLimitRange proj max L R).2.1 ++
        (uniqueLimitRange proj max L R).2.2).Perm (L ++ R) ∧
    (∀ k : β, keyFilter proj k ((uniqueLimitRange proj max L R).1 ++
        (uniqueLimitRange proj max L R).2.1 ++ (uniqueLimitRange proj max L R).2.2) =
      keyFilter proj k (L ++ R)) := by
  dsimp only [uniqueLimitRange]
  have hRspec : Sorted (KeyLe proj) (uniqueLimit proj max R).1 ∧
      KeysNodup proj (uniqueLimit proj max R).1 ∧
      Sorted (KeyLe proj) (uniqueLimit proj max R).2 ∧
      List.Sublist (uniqueLimit proj max R).2 R ∧
      ((uniqueLimit proj max R).1 ++ (uniqueLimit proj max R).2).Perm R ∧
      (∀ k : β, keyFilter proj k (uniqueLimit proj max R).1 ++
          keyFilter proj k (uniqueLimit proj max R).2 = keyFilter proj k R) :=
    uniqueLimit_spec proj max hR
  have hm : Sorted (KeyLe proj) (mergeTwo proj L (uniqueLimit proj max R).1) :=
    mergeTwo_sorted proj L _ hL hRspec.1
  have hmspec := uniqueLimit_spec proj max hm
  refine ⟨hmspec.1, hmspec.2.1, hmspec.2.2.1, hRspec.2.2.1, ?_, ?_⟩
  · have h1 := List.Perm.append_right (uniqueLimit proj max R).2
      (uniqueLimit_perm proj max (mergeTwo proj L (uniqueLimit proj max R).1))
    have h2 := List.Perm.append_right (uniqueLimit proj max R).2
      (mergeTwo_perm proj L (uniqueLimit proj max R).1)
    have h3 : ((L ++ (uniqueLimit proj max R).1) ++ (uniqueLimit proj max R).2).Perm (L ++ R) := by
      rw [List.append_assoc]
      exact List.Perm.append_left L hRspec.2.2.2.2.1
    exact (h1.trans h2).trans h3
  · intro k
    have hmerge : keyFilter proj k (mergeTwo proj L (uniqueLimit proj max R).1) =
        keyFilter proj k L ++ keyFilter proj k (uniqueLimit proj max R).1 :=
      mergeTwo_keyFilter proj k L _ hL hRspec.1
    have hbuf := hmspec.2.2.2.2.2 k
    have hrest := hRspec.2.2.2.2.2 k
    calc keyFilter proj k
          (((uniqueLimit proj max (mergeTwo proj L (uniqueLimit proj max R).1)).1 ++
            (uniqueLimit proj max (mergeTwo proj L (uniqueLimit proj max R).1)).2) ++
            (uniqueLimit proj max R).2)
        = keyFilter proj k (uniqueLimit proj max (mergeTwo proj L (uniqueLimit proj max R).1)).1 ++
          keyFilter proj k (uniqueLimit proj max (mergeTwo proj L (uniqueLimit proj max R).1)).2 ++
          keyFilter proj k (uniqueLimit proj max R).2 := by
            rw [keyFilter_append (proj := proj) k
                ((uniqueLimit proj max (mergeTwo proj L (uniqueLimit proj max R).1)).1 ++
                  (uniqueLimit proj max (mergeTwo proj L (uniqueLimit proj max R).1)).2)
                (uniqueLimit proj max R).2,
              keyFilter_append (proj := proj) k
                (uniqueLimit proj max (mergeTwo proj L (uniqueLimit proj max R).1)).1
                (uniqueLimit proj max (mergeTwo proj L (uniqueLimit proj max R).1)).2]
      _ = keyFilter proj k (mergeTwo proj L (uniqueLimit proj max R).1) ++
          keyFilter proj k (uniqueLimit proj max R).2 := by rw [hbuf]
      _ = (keyFilter proj k L ++ keyFilter proj k (uniqueLimit proj max R).1) ++
          keyFilter proj k (uniqueLimit proj max R).2 := by rw [hmerge]
      _ = keyFilter proj k L ++ (keyFilter proj k (uniqueLimit proj max R).1 ++
          keyFilter proj k (uniqueLimit proj max R).2) := by rw [List.append_assoc]
      _ = keyFilter proj k L ++ keyFilter proj k R := by rw [hrest]
      _ = keyFilter proj k (L ++ R) := by rw [keyFilter_append]

/-- In a list whose keys are pairwise different, the subsequence of a key that one of its
elements carries is that single element. -/
theorem keyFilter_eq_singleton_of_keysNodup {proj : α → β} {l : List α} (h : KeysNodup proj l)
    {x : α} (hx : x ∈ l) {k : β} (hk : Cmp.beq (proj x) k = true) : keyFilter proj k l = [x] := by
  induction l with
  | nil => simp at hx
  | cons y ys ih =>
      rw [KeysNodup, List.pairwise_cons] at h
      obtain ⟨h1, h2⟩ := h
      rcases List.mem_cons.mp hx with hxy | hx'
      · have hyk : Cmp.beq (proj y) k = true := by rw [← hxy]; exact hk
        rw [← hxy, keyFilter_cons_of_beq hk,
          keyFilter_eq_nil_of_all ys (fun w hw => by
            have hw' := h1 w hw
            rw [Cmp.beq_eq hyk] at hw'
            rw [Cmp.beq_comm (proj w) k]
            exact hw')]
      · have hyx : Cmp.beq (proj y) (proj x) = false := h1 x hx'
        rw [Cmp.beq_eq hk] at hyx
        rw [keyFilter_cons_of_not_beq (by rw [hyx]; exact Bool.false_ne_true)]
        exact ih h2 hx'

/-- **The buffer's element for a key is that key's first occurrence**: the key's
subsequence of the whole input starts with it. This is what makes merging the buffer back
in front of the remainders put the equal keys in the right order. -/
theorem uniqueLimit_buf_first (proj : α → β) (max : Nat) {l : List α} (hl : Sorted (KeyLe proj) l)
    {x : α} (hx : x ∈ (uniqueLimit proj max l).1) {k : β} (hk : Cmp.beq (proj x) k = true) :
    keyFilter proj k l = [x] ++ keyFilter proj k (uniqueLimit proj max l).2 := by
  have hsingle := keyFilter_eq_singleton_of_keysNodup (uniqueLimit_spec proj max hl).2.1 hx hk
  have hkf := uniqueLimit_keyFilter proj max hl k
  rw [hsingle] at hkf
  exact hkf.symm

/-- The same for the four-argument overload. -/
theorem uniqueLimitRange_buf_first (proj : α → β) (max : Nat) {L R : List α}
    (hL : Sorted (KeyLe proj) L) (hR : Sorted (KeyLe proj) R) {x : α}
    (hx : x ∈ (uniqueLimitRange proj max L R).1) {k : β} (hk : Cmp.beq (proj x) k = true) :
    keyFilter proj k (L ++ R) = [x] ++ keyFilter proj k (uniqueLimitRange proj max L R).2.1 ++
      keyFilter proj k (uniqueLimitRange proj max L R).2.2 := by
  have hspec := uniqueLimitRange_spec proj max hL hR
  have hsingle := keyFilter_eq_singleton_of_keysNodup hspec.2.1 hx hk
  have hkf := hspec.2.2.2.2.2 k
  rw [keyFilter_append (proj := proj) k
      ((uniqueLimitRange proj max L R).1 ++ (uniqueLimitRange proj max L R).2.1)
      (uniqueLimitRange proj max L R).2.2,
    keyFilter_append (proj := proj) k (uniqueLimitRange proj max L R).1
      (uniqueLimitRange proj max L R).2.1,
    hsingle] at hkf
  exact hkf.symm

/-! ## `align_blocks_limit` -/

/-- C++'s `align_blocks_limit`: round the split between the two runs down to a multiple of
`block_size` counted from `first`, then cut the block region off after
`block_size * n_blocks` elements, merging with `inplace_merge_with_rotation`
(`mergeByRotationStable`) so that both runs stay sorted. Returns the rearranged list, the
new split and the new end of the block region; `first` and the original end are unchanged,
which is why the C++ returns them untouched. -/
def alignBlocksLimit (proj : α → β) (bs nb : Nat) (l : List α) (first mid last : Nat) :
    List α × Nat × Nat :=
  let m := first + ((mid - first) / bs * bs)
  let l1 := mergeByRotationStable proj l m mid last
  let l2 := first + bs * nb
  if m > l2 then (mergeByRotationStable proj l1 l2 m last, l2, last) else (l1, m, l2)

/-- `l.drop i` splits at `j` when `i ≤ j`. -/
theorem drop_take_splice' {l : List α} : ∀ {i j : Nat}, i ≤ j →
    l.drop i = (l.drop i).take (j - i) ++ l.drop j := by
  induction l with
  | nil => intro i j _; simp
  | cons a as ih =>
      intro i j h
      cases i with
      | zero => exact (List.take_append_drop j (a :: as)).symm
      | succ i' =>
          cases j with
          | zero => exact absurd h (Nat.not_succ_le_zero i')
          | succ j' =>
              simp only [List.drop_succ_cons, Nat.succ_sub_succ_eq_sub]
              exact ih (Nat.succ_le_succ_iff.mp h)

/-- Splitting a list at three consecutive indices. -/
theorem take_drop_splice3 {l : List α} {first mid last : Nat} (h1 : first ≤ mid)
    (h2 : mid ≤ last) :
    l = l.take first ++ (l.drop first).take (mid - first) ++
      (l.drop mid).take (last - mid) ++ l.drop last := by
  have htake : l.take first ++ (l.drop first).take (mid - first) = l.take mid := by
    rw [← take_add' l first (mid - first), Nat.add_sub_of_le h1]
  have hdrop : (l.drop mid).take (last - mid) ++ l.drop last = l.drop mid :=
    (drop_take_splice' (l := l) (i := mid) (j := last) h2).symm
  rw [htake]
  simp only [List.append_assoc]
  rw [hdrop, List.take_append_drop]

/-- Merging the two halves of a range in place keeps every `k`-subsequence: the range's
four-part decomposition is unchanged, only its two middle pieces are replaced by their
stable merge. -/
theorem keyFilter_mergeByRotationStable {proj : α → β} {l : List α} {first mid last : Nat}
    (h1 : first ≤ mid) (h2 : mid ≤ last)
    (hA : Sorted (KeyLe proj) ((l.drop first).take (mid - first)))
    (hB : Sorted (KeyLe proj) ((l.drop mid).take (last - mid))) (k : β) :
    keyFilter proj k (mergeByRotationStable proj l first mid last) = keyFilter proj k l := by
  have hspec := mergeByRotationStable_spec (proj := proj) (l := l) (first := first)
    (mid := mid) (last := last) hA hB
  have hf : keyFilter proj k (l.take first ++ mergeTwo proj ((l.drop first).take (mid - first))
        ((l.drop mid).take (last - mid)) ++ l.drop last) =
      keyFilter proj k (l.take first ++ (l.drop first).take (mid - first) ++
        (l.drop mid).take (last - mid) ++ l.drop last) := by
    simp only [keyFilter_append]
    rw [mergeTwo_keyFilter proj k _ _ hA hB]
    simp only [List.append_assoc]
  rw [hspec, hf, ← take_drop_splice3 (l := l) h1 h2]

/-- A sub-run of a sorted run is sorted. This is what lets `align_blocks_limit` re-merge
the pieces its block rounding cuts out: each piece is still one of the caller's sorted
runs, just a shorter one. -/
theorem sorted_subrun {proj : α → β} {l : List α} {first mid lo hi : Nat}
    (h1 : first ≤ lo) (h2 : lo ≤ hi) (h3 : hi ≤ mid)
    (hs : Sorted (KeyLe proj) ((l.drop first).take (mid - first))) :
    Sorted (KeyLe proj) ((l.drop lo).take (hi - lo)) := by
  have h3' : lo ≤ mid := Nat.le_trans h2 h3
  have hsplit : (mid - lo) + (lo - first) = mid - first := by
    rw [← Nat.add_sub_assoc h1, Nat.sub_add_cancel h3']
  have hA : hi - lo ≤ (mid - first) - (lo - first) := by
    rw [← hsplit, Nat.add_sub_cancel (mid - lo) (lo - first)]
    exact Nat.sub_le_sub_right h3 lo
  have hM : ((l.drop first).take (mid - first)).drop (lo - first) =
      (l.drop lo).take ((mid - first) - (lo - first)) := by
    rw [drop_take']
    rw [show List.drop (lo - first) (l.drop first) = l.drop lo from by
      simp only [List.drop_drop]
      exact congrArg (fun n => List.drop n l) (Nat.add_sub_of_le h1)]
  have hstep : Sorted (KeyLe proj) ((l.drop lo).take ((mid - first) - (lo - first))) := by
    rw [← hM]
    exact sorted_drop (n := lo - first) hs
  have hfin := sorted_take (n := hi - lo) hstep
  rwa [List.take_take, Nat.min_eq_left hA] at hfin

/-- The first `m` elements of `X ++ Y` are `X`, when `X` has exactly `m` elements. -/
theorem take_prefix_of_length {X Y : List α} {m : Nat} (h : X.length = m) :
    (X ++ Y).take m = X := by
  rw [← h]
  exact List.take_left

/-- If `l₁` agrees with `l` on its first `m` elements, then so does the piece `[l₂, m)`.
This is what keeps the second merge of `align_blocks_limit` fed with a piece of the
caller's original sorted run: the first merge only rewrites the range from `m` on. -/
theorem drop_take_of_take_eq {l l₁ : List α} {l₂ m : Nat} (hm : l₁.take m = l.take m) :
    (l₁.drop l₂).take (m - l₂) = (l.drop l₂).take (m - l₂) := by
  calc (l₁.drop l₂).take (m - l₂)
      = (l₁.take m).drop l₂ := (drop_take' l₁ l₂ m).symm
    _ = (l.take m).drop l₂ := by rw [hm]
    _ = (l.drop l₂).take (m - l₂) := drop_take' l l₂ m

/-- `mergeTwo` is as long as its two inputs together. -/
theorem mergeTwo_length (proj : α → β) (A B : List α) :
    (mergeTwo proj A B).length = A.length + B.length := by
  rw [← List.length_append, ← (mergeTwo_perm proj A B).length_eq]

end Tcs
