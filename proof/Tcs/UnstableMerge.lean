/-
  The block phase of `inplace_unstable_merge` (`include/tcs/inplace/unstable_merge.hpp`),
  proved correct: `block_selection_sort`, `block_merge_pairwise` and the assembly
  `inplace_unstable_merge`.

  Modelling. The C++ routines walk random-access ranges and only ever compare keys,
  so the model works on a list with `Nat` indices, as in `Tcs.Merge`. The two block
  phases are modelled one level up, on the *list of blocks* of the aligned prefix:

  * `block_selection_sort` reorders the whole `bs`-blocks of the aligned prefix
    `A1 ++ B1` by the pair `(first key, last key)`, which is exactly the order the
    C++ selection sort computes. The model performs the reordering by *merging* the
    two runs' block sequences in that order (`blkMerge`), which keeps each run's
    blocks in run order; that extra information is what the counting argument for
    `block_merge_pairwise` needs, and it is true of the C++ output as well.
  * `block_merge_pairwise` is the block-index loop of the C++, with `merge_with_swap`
    on a window of three blocks expressed by `mergeTwo` (the buffer contents that
    `Tcs.mergeWithSwap_final` characterises exactly) plus the optional block swap.

  One deliberate abstraction: the C++ `merge_with_swap` deposits the displaced
  block's elements at the *end* of its buffer in an order determined by its
  swap sequence, whereas the block model carries that displaced block unchanged.
  The block is never read again (it is always the next `output` slot), so only its
  multiset matters; final key sequences agree, element order inside equal-key
  groups may differ. This is documented on `blockMergeStd` below. Likewise
  `bubble_sort` is modelled by `Tcs.bubbleSort` and the block selection sort by the
  two runs' pair-ordered block merge, as in `Tcs/Sort.lean`.

  What is proved:
  * `blockSelectionSort_*`: the block sort permutes the aligned prefix, keeps every
    block internally sorted, and orders the blocks by `(first key, last key)`.
  * `blockMergePairwise_sorted`: after the pairwise block merges, everything but the
    last block of the aligned prefix is sorted. The invariant is the one recorded in
    `.merge-dev/BLOCK-PHASE-BRIEF.md`, including the counting lemma
    (`countP_blkMerge_take_le`) that bounds how many elements of the processed
    blocks can exceed the next block's first key.
  * `unstableMerge_sorted_and_perm` and its `Array` wrapper: `inplace_unstable_merge`
    sorts the whole range and only permutes it.

  `blockSize = Nat.sqrt len` is modelled by `Nat.sqrt`; the tail index `al - bs` is
  `Nat` subtraction, which clamps at `0` where the C++ would be out of bounds (for
  `len ≥ 2` one of the two halves has length `≥ len/2 ≥ bs`, so the C++ never gets
  there; the proof does not need `bs ≤ al`).
-/
import Tcs.Merge
import Tcs.Sort

namespace Tcs

variable {α : Type u} {β : Type v}

/-- `Bool` conjunction elimination, as an `Iff`-style helper (core states it as an
equation on `Bool`). -/
theorem bool_and_mp {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  simpa only [Bool.and_eq_true] using h

/-- `Bool` disjunction elimination, as an `Iff`-style helper. -/
theorem bool_or_mp {a b : Bool} (h : (a || b) = true) : a = true ∨ b = true := by
  simpa only [Bool.or_eq_true] using h

/-! ## Lexicographic order on `(first key, last key)` pairs -/

/-- `≤` on optional keys, with `none` (the key of an empty block) as bottom. -/
def occLe (a b : Option β) [Cmp β] : Bool :=
  match a, b with
  | none, _ => true
  | some _, none => false
  | some x, some y => Cmp.ble x y

/-- `<` on optional keys, with `none` as bottom. -/
def occLt (a b : Option β) [Cmp β] : Bool :=
  match a, b with
  | none, some _ => true
  | some x, some y => Cmp.blt x y
  | _, _ => false

/-- Equality on optional keys, decided by the order (exact by antisymmetry). -/
def occEq (a b : Option β) [Cmp β] : Bool := occLe a b && occLe b a

theorem occLe_refl [Cmp β] (a : Option β) : occLe a a = true := by
  cases a with
  | none => rfl
  | some x => exact Cmp.ble_refl x

theorem occLe_total [Cmp β] (a b : Option β) : occLe a b = true ∨ occLe b a = true := by
  cases a with
  | none => exact Or.inl rfl
  | some x =>
    cases b with
    | none => exact Or.inr rfl
    | some y => exact Cmp.ble_total x y

theorem occLe_trans [Cmp β] {a b c : Option β} (h₁ : occLe a b = true)
    (h₂ : occLe b c = true) : occLe a c = true := by
  cases a with
  | none => rfl
  | some x =>
    cases b with
    | none => simp [occLe] at h₁
    | some y =>
      cases c with
      | none => simp [occLe] at h₂
      | some z => exact Cmp.ble_trans h₁ h₂

theorem occLe_antisymm [Cmp β] {a b : Option β} (h₁ : occLe a b = true)
    (h₂ : occLe b a = true) : a = b := by
  cases a with
  | none => cases b with
    | none => rfl
    | some y => simp [occLe] at h₂
  | some x => cases b with
    | none => simp [occLe] at h₁
    | some y => rw [Cmp.ble_antisymm h₁ h₂]

theorem occLe_eq_lt_or_eq [Cmp β] (a b : Option β) :
    occLe a b = (occLt a b || occEq a b) := by
  unfold occLt occEq
  cases a with
  | none => cases b <;> rfl
  | some x => cases b with
    | none => rfl
    | some y => exact Cmp.ble_eq_blt_or_beq x y

theorem occLt_iff [Cmp β] {a b : Option β} :
    occLt a b = true ↔ occLe a b = true ∧ occLe b a = false := by
  cases a with
  | none => cases b with
    | none => simp [occLt, occLe]
    | some y => simp [occLt, occLe]
  | some x => cases b with
    | none => simp [occLt, occLe]
    | some y => exact Cmp.blt_iff

theorem occLt_of_le_of_not_le [Cmp β] {a b : Option β} (h₁ : occLe a b = true)
    (h₂ : occLe b a = false) : occLt a b = true :=
  occLt_iff.mpr ⟨h₁, h₂⟩

theorem occLe_of_lt [Cmp β] {a b : Option β} (h : occLt a b = true) : occLe a b = true :=
  (occLt_iff.mp h).1

theorem occLt_trans [Cmp β] {a b c : Option β} (h₁ : occLt a b = true)
    (h₂ : occLt b c = true) : occLt a c = true := by
  have h1 := occLt_iff.mp h₁
  have h2 := occLt_iff.mp h₂
  refine occLt_iff.mpr ⟨occLe_trans h1.1 h2.1, ?_⟩
  cases h : occLe c a with
  | false => rfl
  | true => exact absurd (occLe_trans h h1.1) (by rw [h2.2]; exact Bool.false_ne_true)

theorem occEq_iff [Cmp β] {a b : Option β} :
    occEq a b = true ↔ occLe a b = true ∧ occLe b a = true := by
  simp [occEq, Bool.and_eq_true]

theorem occEq_refl [Cmp β] (a : Option β) : occEq a a = true :=
  occEq_iff.mpr ⟨occLe_refl a, occLe_refl a⟩

theorem occEq_comm [Cmp β] (a b : Option β) : occEq a b = occEq b a := by
  simp [occEq, Bool.and_comm]

theorem occEq_eq_of_antisymm [Cmp β] {a b : Option β} (h : occEq a b = true) : a = b :=
  occLe_antisymm (occEq_iff.mp h).1 (occEq_iff.mp h).2

theorem occLt_irrefl [Cmp β] (a : Option β) : occLt a a = false := by
  cases a with
  | none => rfl
  | some x => exact Cmp.blt_irrefl x

theorem occLt_not [Cmp β] {a b : Option β} (h : occLt a b = true) : occLt b a = false := by
  have h' := (occLt_iff.mp h).2
  cases hb : occLt b a with
  | false => rfl
  | true => exact absurd ((occLt_iff.mp hb).1) (by rw [h']; exact Bool.false_ne_true)

theorem occEq_false_of_occLt [Cmp β] {a b : Option β} (h : occLt a b = true) : occEq a b = false := by
  have h' := (occLt_iff.mp h).2
  cases hb : occEq a b with
  | false => rfl
  | true => exact absurd ((occEq_iff.mp hb).2) (by rw [h']; exact Bool.false_ne_true)

theorem occLt_false_of_occEq [Cmp β] {a b : Option β} (h : occEq a b = true) : occLt a b = false := by
  have h' : occLe b a = true := (occEq_iff.mp h).2
  cases hb : occLt a b with
  | false => rfl
  | true => exact absurd ((occLt_iff.mp hb).2) (by rw [h']; simp)

/-- Trichotomy for the option order: below, equal, or above. -/
theorem occLt_or_occEq_or_occLt [Cmp β] (a b : Option β) :
    occLt a b = true ∨ occEq a b = true ∨ occLt b a = true := by
  cases a with
  | none => cases b with
    | none => exact Or.inr (Or.inl rfl)
    | some y => exact Or.inl rfl
  | some x => cases b with
    | none => exact Or.inr (Or.inr rfl)
    | some y =>
      by_cases hxy : Cmp.ble x y = true
      · by_cases hyx : Cmp.ble y x = true
        · exact Or.inr (Or.inl (by simp [occEq, occLe, hxy, hyx]))
        · have hyx' : Cmp.ble y x = false := by cases h : Cmp.ble y x <;> simp_all
          exact Or.inl (by simp [occLt, Cmp.blt, hxy, hyx'])
      · have hxy' : Cmp.ble x y = false := by cases h : Cmp.ble x y <;> simp_all
        have hyx : Cmp.ble y x = true := by
          rcases Cmp.ble_total x y with h | h
          · exact absurd h hxy
          · exact h
        exact Or.inr (Or.inr (by simp [occLt, Cmp.blt, hyx, hxy']))

variable {α : Type u} {β : Type v} [Cmp β]

/-- First key of a block (the key of its first element; `none` when empty). -/
def keyFst (proj : α → β) (b : List α) : Option β := b.head?.map proj

/-- Last key of a block (the key of its last element; `none` when empty). -/
def keyLst (proj : α → β) (b : List α) : Option β := b.getLast?.map proj

/-- Lexicographic `≤` on key pairs, first key then last key, with `none` bottom. -/
def pairLex (f₁ f₂ l₁ l₂ : Option β) : Bool :=
  occLt f₁ f₂ || (occEq f₁ f₂ && occLe l₁ l₂)

/-- The block comparison of `block_selection_sort`:
`(first key, last key)` lexicographically. -/
def PairLe (proj : α → β) (x y : List α) : Bool :=
  pairLex (keyFst proj x) (keyFst proj y) (keyLst proj x) (keyLst proj y)

/-- Key-pair equality of two blocks, i.e. both keys equal. -/
def PairEq (proj : α → β) (x y : List α) : Bool :=
  occEq (keyFst proj x) (keyFst proj y) && occEq (keyLst proj x) (keyLst proj y)

theorem pairLex_of_occLt {f₁ f₂ l₁ l₂ : Option β} (h : occLt f₁ f₂ = true) :
    pairLex f₁ f₂ l₁ l₂ = true := by
  unfold pairLex
  rw [h]
  rfl

theorem pairLex_of_occEq {f₁ f₂ l₁ l₂ : Option β} (h : occEq f₁ f₂ = true) :
    pairLex f₁ f₂ l₁ l₂ = occLe l₁ l₂ := by
  unfold pairLex
  rw [occLt_false_of_occEq h, h]
  rfl

/-- When the *other* first key is strictly below, the comparison fails. -/
theorem pairLex_false_of_occLt_rev {f₁ f₂ l₁ l₂ : Option β} (h : occLt f₂ f₁ = true) :
    pairLex f₁ f₂ l₁ l₂ = false := by
  have hle : occLe f₂ f₁ = true := occLe_of_lt h
  have hnot : occLe f₁ f₂ = false := (occLt_iff.mp h).2
  unfold pairLex
  rw [show occLt f₁ f₂ = false from by
        cases hl : occLt f₁ f₂ with
        | false => rfl
        | true => exact absurd ((occLt_iff.mp hl).2) (by rw [hle]; simp),
      show occEq f₁ f₂ = false from by simp [occEq, hnot]]
  rfl

theorem pairLex_total (f₁ f₂ l₁ l₂ : Option β) :
    pairLex f₁ f₂ l₁ l₂ = true ∨ pairLex f₂ f₁ l₂ l₁ = true := by
  rcases occLt_or_occEq_or_occLt f₁ f₂ with h | h | h
  · exact Or.inl (pairLex_of_occLt h)
  · rw [occEq_eq_of_antisymm h]
    rw [pairLex_of_occEq (occEq_refl f₂), pairLex_of_occEq (occEq_refl f₂)]
    exact occLe_total l₁ l₂
  · exact Or.inr (pairLex_of_occLt h)

theorem pairLex_trans {f₁ f₂ f₃ l₁ l₂ l₃ : Option β}
    (h₁ : pairLex f₁ f₂ l₁ l₂ = true) (h₂ : pairLex f₂ f₃ l₂ l₃ = true) :
    pairLex f₁ f₃ l₁ l₃ = true := by
  rcases occLt_or_occEq_or_occLt f₁ f₂ with h | h | h
  · rcases occLt_or_occEq_or_occLt f₂ f₃ with h' | h' | h'
    · exact pairLex_of_occLt (occLt_trans h h')
    · rw [← occEq_eq_of_antisymm h']
      exact pairLex_of_occLt h
    · rw [pairLex_false_of_occLt_rev h'] at h₂
      exact absurd h₂ (by simp)
  · rw [occEq_eq_of_antisymm h] at h₁ ⊢
    rcases occLt_or_occEq_or_occLt f₂ f₃ with h' | h' | h'
    · exact pairLex_of_occLt h'
    · rw [pairLex_of_occEq (occEq_refl f₂)] at h₁
      rw [← occEq_eq_of_antisymm h'] at h₂ ⊢
      rw [pairLex_of_occEq (occEq_refl f₂)] at h₂
      rw [pairLex_of_occEq (occEq_refl f₂)]
      exact occLe_trans h₁ h₂
    · rw [pairLex_false_of_occLt_rev h'] at h₂
      exact absurd h₂ (by simp)
  · rw [pairLex_false_of_occLt_rev h] at h₁
    exact absurd h₁ (by simp)

theorem PairLe_total (proj : α → β) (x y : List α) :
    PairLe proj x y = true ∨ PairLe proj y x = true :=
  pairLex_total (keyFst proj x) (keyFst proj y) (keyLst proj x) (keyLst proj y)

theorem PairLe_trans {proj : α → β} {x y z : List α} (h₁ : PairLe proj x y = true)
    (h₂ : PairLe proj y z = true) : PairLe proj x z = true :=
  pairLex_trans h₁ h₂

theorem pairLex_ble_fst {f₁ f₂ l₁ l₂ : Option β} (h : pairLex f₁ f₂ l₁ l₂ = true) :
    occLe f₁ f₂ = true := by
  unfold pairLex at h
  rcases bool_or_mp h with h | h
  · exact occLe_of_lt h
  · exact (occEq_iff.mp (bool_and_mp h).1).1

theorem pairLex_le_snd {f₁ f₂ l₁ l₂ : Option β} (h : pairLex f₁ f₂ l₁ l₂ = true)
    (hrev : occLe f₂ f₁ = true) : occLe l₁ l₂ = true := by
  unfold pairLex at h
  rcases bool_or_mp h with h | h
  · have hlt := occLt_iff.mp h
    rw [hrev] at hlt
    exact absurd hlt.2 (by simp)
  · exact (bool_and_mp h).2

theorem pairLex_antisymm {f₁ f₂ l₁ l₂ : Option β} (h₁ : pairLex f₁ f₂ l₁ l₂ = true)
    (h₂ : pairLex f₂ f₁ l₂ l₁ = true) :
    occEq f₁ f₂ = true ∧ occEq l₁ l₂ = true := by
  have hf₁ := pairLex_ble_fst h₁
  have hf₂ := pairLex_ble_fst h₂
  have hl₁ := pairLex_le_snd h₁ hf₂
  have hl₂ := pairLex_le_snd h₂ hf₁
  exact ⟨occEq_iff.mpr ⟨hf₁, hf₂⟩, occEq_iff.mpr ⟨hl₁, hl₂⟩⟩

/-- A `PairLe` comparison only looks at the first keys unless they are equal. -/
theorem PairLe_ble_fst {proj : α → β} {x y : List α} (h : PairLe proj x y = true) :
    occLe (keyFst proj x) (keyFst proj y) = true :=
  pairLex_ble_fst h

/-- Equal first keys force the last keys to be comparable in the same direction. -/
theorem PairLe_ble_lst {proj : α → β} {x y : List α} (h : PairLe proj x y = true)
    (hrev : occLe (keyFst proj y) (keyFst proj x) = true) :
    occLe (keyLst proj x) (keyLst proj y) = true :=
  pairLex_le_snd h hrev

theorem PairLe_antisymm {proj : α → β} {x y : List α} (h₁ : PairLe proj x y = true)
    (h₂ : PairLe proj y x = true) : PairEq proj x y = true := by
  obtain ⟨hf, hl⟩ := pairLex_antisymm h₁ h₂
  simp [PairEq, hf, hl]

/-! ## The `bs`-blocks of one run -/

/-- The first `fuel` successive `bs`-element blocks of `l`. The trailing block may
be shorter than `bs`; all blocks have length `bs` when `fuel * bs ≤ l.length`. -/
def chunksAux (bs : Nat) : Nat → List α → List (List α)
  | 0, _ => []
  | _ + 1, [] => []
  | fuel + 1, l@(_ :: _) => l.take bs :: chunksAux bs fuel (l.drop bs)

/-- The `m` successive `bs`-blocks of `l`. -/
def chunks (bs m : Nat) (l : List α) : List (List α) := chunksAux bs m l

theorem chunksAux_flatten (bs : Nat) : ∀ (fuel : Nat) (l : List α),
    (chunksAux bs fuel l).flatten = l.take (fuel * bs)
  | 0, l => by simp [chunksAux]
  | fuel + 1, [] => by simp [chunksAux]
  | fuel + 1, a :: t => by
      rw [chunksAux, List.flatten_cons, chunksAux_flatten bs fuel ((a :: t).drop bs)]
      rw [Nat.succ_mul, Nat.add_comm (fuel * bs) bs, take_add']

theorem chunks_flatten (bs m : Nat) (l : List α) :
    (chunks bs m l).flatten = l.take (m * bs) :=
  chunksAux_flatten bs m l

/-- When the list is long enough, its `m` blocks are exactly `m` blocks. -/
theorem chunksAux_length {bs : Nat} (hbs : 0 < bs) : ∀ (fuel : Nat) (l : List α),
    fuel * bs ≤ l.length → (chunksAux bs fuel l).length = fuel
  | 0, l, _ => rfl
  | fuel + 1, l, h => by
      cases l with
      | nil =>
        exfalso
        have hpos : 0 < (fuel + 1) * bs := Nat.mul_pos (Nat.succ_pos fuel) hbs
        simp only [List.length_nil] at h
        omega
      | cons a t =>
        have hdrop : fuel * bs ≤ ((a :: t).drop bs).length := by
          rw [List.length_drop]
          rw [Nat.succ_mul] at h
          omega
        rw [chunksAux.eq_3, List.length_cons,
          chunksAux_length hbs fuel ((a :: t).drop bs) hdrop]

/-- Every block produced from a long-enough list has length exactly `bs`. -/
theorem chunksAux_all_length {bs : Nat} (hbs : 0 < bs) : ∀ (fuel : Nat) (l : List α),
    fuel * bs ≤ l.length → ∀ b ∈ chunksAux bs fuel l, b.length = bs
  | 0, l, _, b, hb => by simp [chunksAux.eq_1] at hb
  | fuel + 1, l, h, b, hb => by
      cases l with
      | nil => simp [chunksAux.eq_2] at hb
      | cons a t =>
        have hbsle : bs ≤ (a :: t).length := by
          have : bs ≤ (fuel + 1) * bs := by rw [Nat.succ_mul]; omega
          omega
        have hdrop : fuel * bs ≤ ((a :: t).drop bs).length := by
          rw [List.length_drop]
          rw [Nat.succ_mul] at h
          omega
        rw [chunksAux.eq_3, List.mem_cons] at hb
        rcases hb with rfl | hb
        · rw [List.length_take, Nat.min_eq_left hbsle]
        · exact chunksAux_all_length hbs fuel ((a :: t).drop bs) hdrop b hb

/-- Every block of a sorted run is internally sorted. -/
theorem chunksAux_all_sorted {proj : α → β} {bs : Nat} :
    ∀ (fuel : Nat) (l : List α), Sorted (KeyLe proj) l →
      ∀ b ∈ chunksAux bs fuel l, Sorted (KeyLe proj) b
  | 0, l, _, b, hb => by simp [chunksAux.eq_1] at hb
  | fuel + 1, l, hs, b, hb => by
      cases l with
      | nil => simp [chunksAux.eq_2] at hb
      | cons a t =>
        rw [chunksAux.eq_3, List.mem_cons] at hb
        rcases hb with rfl | hb
        · exact sorted_take hs
        · exact chunksAux_all_sorted fuel ((a :: t).drop bs) (sorted_drop hs) b hb

/-- The blocks of one sorted run, in run order: every block is elementwise below
the blocks that follow it. -/
def RunOrdered (proj : α → β) : List (List α) → Prop
  | [] => True
  | b :: rest => AllLe (KeyLe proj) b rest.flatten ∧ RunOrdered proj rest

/-- Blocks cut from a sorted run are run-ordered. -/
theorem chunksAux_runOrdered {proj : α → β} {bs : Nat} :
    ∀ (fuel : Nat) (l : List α), Sorted (KeyLe proj) l →
      RunOrdered proj (chunksAux bs fuel l)
  | 0, l, _ => trivial
  | fuel + 1, l, hs => by
      cases l with
      | nil => rw [chunksAux.eq_2]; trivial
      | cons a t =>
        refine ⟨?_, ?_⟩
        · rw [chunksAux_flatten]
          exact allLe_take_right (allLe_take_drop_of_sorted hs)
        · exact chunksAux_runOrdered fuel ((a :: t).drop bs) (sorted_drop hs)

/-- The run order, as an indexed statement. -/
theorem RunOrdered.allLe_getElem {proj : α → β} {blks : List (List α)}
    (h : RunOrdered proj blks) :
    ∀ (i j : Nat) (hi : i < blks.length) (hj : j < blks.length), i < j →
      AllLe (KeyLe proj) blks[i] blks[j] := by
  induction blks with
  | nil => intro i j hi; simp at hi
  | cons b rest ih =>
    intro i j hi hj hij
    cases i with
    | zero =>
      cases j with
      | zero => exfalso; omega
      | succ k =>
        rw [List.getElem_cons_zero, List.getElem_cons_succ]
        exact allLe_of_subset_right h.1
          (fun y hy => List.mem_flatten.mpr ⟨rest[k]'(by simp at hj; omega),
            List.mem_iff_getElem.mpr ⟨k, by simp at hj; omega, rfl⟩, hy⟩)
    | succ i' =>
      cases j with
      | zero => exfalso; omega
      | succ k =>
        rw [List.getElem_cons_succ, List.getElem_cons_succ]
        exact ih h.2 i' k (by simpa using hi) (by simpa using hj) (by omega)

/-- The last element of a nonempty list (or the default) is a member. -/
theorem getLastD_mem (l : List α) (d : α) : l.getLast?.getD d ∈ d :: l := by
  induction l generalizing d with
  | nil => simp
  | cons a t ih => rw [List.getLast?_cons]; exact List.mem_cons_of_mem d (ih a)

/-- Every elementwise comparison of blocks is a `PairLe`. -/
theorem PairLe_of_allLe {proj : α → β} {b c : List α} (hc : c ≠ [])
    (h : AllLe (KeyLe proj) b c) : PairLe proj b c = true := by
  obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_ne_nil hc
  cases b with
  | nil => simp [PairLe, pairLex, keyFst, occLt]
  | cons x xs =>
    have hble : Cmp.ble (proj x) (proj y) = true := h x (by simp) y (by simp)
    have hlastble : Cmp.ble (proj (xs.getLast?.getD x)) (proj (ys.getLast?.getD y)) = true :=
      h _ (getLastD_mem xs x) _ (getLastD_mem ys y)
    have hf1 : keyFst proj (x :: xs) = some (proj x) := rfl
    have hf2 : keyFst proj (y :: ys) = some (proj y) := rfl
    have hl1 : keyLst proj (x :: xs) = some (proj (xs.getLast?.getD x)) := by
      simp [keyLst, List.getLast?_cons]
    have hl2 : keyLst proj (y :: ys) = some (proj (ys.getLast?.getD y)) := by
      simp [keyLst, List.getLast?_cons]
    rw [PairLe, pairLex, hf1, hf2, hl1, hl2]
    by_cases hle : Cmp.ble (proj y) (proj x) = true
    · rw [show occLt (some (proj x)) (some (proj y)) = false from by
            simp [occLt, Cmp.blt, hble, hle],
          show occEq (some (proj x)) (some (proj y)) = true from by
            simp [occEq, occLe, hble, hle],
          show occLe (some (proj (xs.getLast?.getD x)))
              (some (proj (ys.getLast?.getD y))) = true from by
            simp [occLe, hlastble]]
      rfl
    · rw [show occLt (some (proj x)) (some (proj y)) = true from by
            simp [occLt, Cmp.blt, hble, hle]]
      rfl

/-- A run-ordered list of nonempty blocks is sorted by the block pair. -/
theorem RunOrdered.pairSorted {proj : α → β} {blks : List (List α)}
    (hne : ∀ c ∈ blks, c ≠ []) (h : RunOrdered proj blks) :
    Sorted (fun x y => PairLe proj x y = true) blks := by
  induction blks with
  | nil => exact sorted_nil _
  | cons b rest ih =>
    refine (sorted_cons_iff _ b rest).mpr ⟨?_, ?_⟩
    · intro c hc
      exact PairLe_of_allLe (hne c (List.mem_cons_of_mem _ hc))
        (allLe_of_subset_right h.1 (fun y hy => List.mem_flatten.mpr ⟨c, hc, hy⟩))
    · exact ih (fun c hc => hne c (List.mem_cons_of_mem _ hc)) h.2

/-! ## Merging the two runs' blocks by key pair -/

/-- Merge two block sequences by the `(first key, last key)` pair, taking the left
run on ties. This is the order `block_selection_sort` puts the blocks in. -/
def blkMerge (proj : α → β) : List (List α) → List (List α) → List (List α)
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys =>
      if PairLe proj x y then x :: blkMerge proj xs (y :: ys)
      else y :: blkMerge proj (x :: xs) ys

theorem blkMerge_nil_left (proj : α → β) (ys : List (List α)) : blkMerge proj [] ys = ys := by
  simp [blkMerge]

theorem blkMerge_nil_right (proj : α → β) (xs : List (List α)) : blkMerge proj xs [] = xs := by
  cases xs <;> simp [blkMerge]

theorem blkMerge_cons_cons_of_le {proj : α → β} {x y : List α} {xs ys : List (List α)}
    (h : PairLe proj x y = true) :
    blkMerge proj (x :: xs) (y :: ys) = x :: blkMerge proj xs (y :: ys) := by
  rw [blkMerge.eq_3, ite_eq_left h]

theorem blkMerge_cons_cons_of_not_le {proj : α → β} {x y : List α} {xs ys : List (List α)}
    (h : PairLe proj x y = false) :
    blkMerge proj (x :: xs) (y :: ys) = y :: blkMerge proj (x :: xs) ys := by
  rw [blkMerge.eq_3, ite_eq_right (by rw [h]; exact Bool.false_ne_true)]

theorem blkMerge_perm (proj : α → β) (xs ys : List (List α)) :
    (blkMerge proj xs ys).Perm (xs ++ ys) := by
  induction xs, ys using blkMerge.induct proj with
  | case1 ys => rw [blkMerge_nil_left, List.nil_append]
  | case2 xs h => rw [blkMerge_nil_right, List.append_nil]
  | case3 x xs y ys h ih =>
    rw [blkMerge_cons_cons_of_le h]
    exact List.Perm.cons x ih
  | case4 x xs y ys h ih =>
    rw [blkMerge_cons_cons_of_not_le (by simpa using h)]
    exact (List.Perm.cons y ih).trans (perm_cons_cons_append y x xs ys)

theorem blkMerge_length (proj : α → β) (xs ys : List (List α)) :
    (blkMerge proj xs ys).length = xs.length + ys.length :=
  (blkMerge_perm proj xs ys).length_eq.trans (by simp)

theorem blkMerge_flatten_perm (proj : α → β) (xs ys : List (List α)) :
    (blkMerge proj xs ys).flatten.Perm (xs.flatten ++ ys.flatten) := by
  have h : (blkMerge proj xs ys).flatten.Perm ((xs ++ ys).flatten) :=
    List.Perm.flatten (blkMerge_perm proj xs ys)
  rwa [List.flatten_append] at h

theorem blkMerge_mem {proj : α → β} {b : List α} {xs ys : List (List α)}
    (h : b ∈ blkMerge proj xs ys) : b ∈ xs ∨ b ∈ ys :=
  (blkMerge_perm proj xs ys).subset h |> List.mem_append.mp

/-- Conversely, every block of either input occurs in the merge. -/
theorem mem_blkMerge {proj : α → β} {b : List α} {xs ys : List (List α)}
    (h : b ∈ xs ∨ b ∈ ys) : b ∈ blkMerge proj xs ys := by
  induction xs, ys using blkMerge.induct proj with
  | case1 ys =>
    rcases h with h | h
    · simp at h
    · rwa [blkMerge_nil_left]
  | case2 xs hne =>
    rcases h with h | h
    · rwa [blkMerge_nil_right]
    · simp at h
  | case3 x xs y ys hle ih =>
    rw [blkMerge_cons_cons_of_le hle]
    rcases h with h | h
    · rcases List.mem_cons.mp h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem x (ih (Or.inl h))
    · exact List.mem_cons_of_mem x (ih (Or.inr h))
  | case4 x xs y ys hnot ih =>
    have hfalse : PairLe proj x y = false := Bool.eq_false_iff.mpr hnot
    rw [blkMerge_cons_cons_of_not_le hfalse]
    rcases h with h | h
    · exact List.mem_cons_of_mem y (ih (Or.inl h))
    · rcases List.mem_cons.mp h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem y (ih (Or.inr h))

theorem blkMerge_all {proj : α → β} {P : List α → Prop} (xs ys : List (List α))
    (hx : ∀ b ∈ xs, P b) (hy : ∀ b ∈ ys, P b) : ∀ b ∈ blkMerge proj xs ys, P b := by
  intro b hb
  rcases blkMerge_mem hb with h | h
  · exact hx b h
  · exact hy b h

theorem blkMerge_sorted (proj : α → β) :
    ∀ xs ys : List (List α),
      Sorted (fun x y => PairLe proj x y = true) xs →
      Sorted (fun x y => PairLe proj x y = true) ys →
      Sorted (fun x y => PairLe proj x y = true) (blkMerge proj xs ys) := by
  intro xs ys
  induction xs, ys using blkMerge.induct proj with
  | case1 ys => intro _ hy; rwa [blkMerge_nil_left]
  | case2 xs h => intro hx _; rwa [blkMerge_nil_right]
  | case3 x xs y ys h ih =>
    intro hx hy
    rw [blkMerge_cons_cons_of_le h]
    obtain ⟨hx', hxs⟩ := (sorted_cons_iff _ x xs).mp hx
    obtain ⟨hy', hys⟩ := (sorted_cons_iff _ y ys).mp hy
    refine (sorted_cons_iff _ x (blkMerge proj xs (y :: ys))).mpr ⟨?_, ih hxs hy⟩
    intro w hw
    rcases blkMerge_mem hw with hw | hw
    · exact hx' w hw
    · rcases List.mem_cons.mp hw with rfl | hw'
      · exact h
      · exact PairLe_trans h (hy' w hw')
  | case4 x xs y ys h ih =>
    intro hx hy
    rw [blkMerge_cons_cons_of_not_le (by simpa using h)]
    obtain ⟨hx', hxs⟩ := (sorted_cons_iff _ x xs).mp hx
    obtain ⟨hy', hys⟩ := (sorted_cons_iff _ y ys).mp hy
    have hyx : PairLe proj y x = true := by
      rcases PairLe_total proj x y with hxy | hyx
      · exact absurd hxy (by simpa using h)
      · exact hyx
    refine (sorted_cons_iff _ y (blkMerge proj (x :: xs) ys)).mpr ⟨?_, ih hx hys⟩
    intro w hw
    rcases blkMerge_mem hw with hw | hw
    · rcases List.mem_cons.mp hw with rfl | hw'
      · exact hyx
      · exact PairLe_trans hyx (hx' w hw')
    · exact hy' w hw

/-- The merge of a left run whose head wins against the head of the right run's
current prefix starts with that head. -/
theorem blkMerge_cons_left {proj : α → β} {x : List α} {xs : List (List α)}
    {Y : List (List α)} {q : Nat}
    (h : ∀ y ys, Y.take q = y :: ys → PairLe proj x y = true) :
    blkMerge proj (x :: xs) (Y.take q) = x :: blkMerge proj xs (Y.take q) := by
  cases Y with
  | nil => rw [List.take_nil, blkMerge_nil_right, blkMerge_nil_right]
  | cons y ys =>
    cases q with
    | zero => rw [List.take_zero, blkMerge_nil_right, blkMerge_nil_right]
    | succ q => rw [List.take_succ_cons, blkMerge_cons_cons_of_le (h y (ys.take q) List.take_succ_cons)]

/-- The merge of a right run whose head wins against the head of the left run's
current prefix starts with that head. -/
theorem blkMerge_cons_right {proj : α → β} {y : List α} {ys : List (List α)}
    {X : List (List α)} {p : Nat}
    (h : ∀ x xs, X.take p = x :: xs → PairLe proj x y = false) :
    blkMerge proj (X.take p) (y :: ys) = y :: blkMerge proj (X.take p) ys := by
  cases X with
  | nil => rw [List.take_nil, blkMerge_nil_left, blkMerge_nil_left]
  | cons x xs =>
    cases p with
    | zero => rw [List.take_zero, blkMerge_nil_left, blkMerge_nil_left]
    | succ p => rw [List.take_succ_cons, blkMerge_cons_cons_of_not_le (h x (xs.take p) List.take_succ_cons)]

/-- **Prefix decomposition of the block merge.** After `j` steps the merge of the
two runs agrees with the merge of the prefixes `xs.take p`, `ys.take q`
(`p + q = j`), and block `j` comes from one of those two prefixes, with the merge's
left-biased decision rule spelled out. -/
theorem blkMerge_take_succ (proj : α → β) :
    ∀ (xs ys : List (List α)) (j : Nat), j < (blkMerge proj xs ys).length →
    ∃ p q, p ≤ xs.length ∧ q ≤ ys.length ∧ p + q = j ∧
      (blkMerge proj xs ys).take j = blkMerge proj (xs.take p) (ys.take q) ∧
      ((∃ b, xs[p]? = some b ∧ (blkMerge proj xs ys)[j]? = some b ∧
          ∀ c, ys[q]? = some c → PairLe proj b c = true)
       ∨ (∃ b, ys[q]? = some b ∧ (blkMerge proj xs ys)[j]? = some b ∧
          ∀ c, xs[p]? = some c → PairLe proj c b = false)) := by
  intro xs ys
  induction xs, ys using blkMerge.induct proj with
  | case1 ys =>
    intro j hj
    have hj' : j < ys.length := by simpa [blkMerge_nil_left] using hj
    refine ⟨0, j, by simp, by omega, by omega, ?_, Or.inr ⟨ys[j]'hj', ?_, ?_, ?_⟩⟩
    · simp [blkMerge_nil_left]
    · exact List.getElem?_eq_getElem hj'
    · rw [blkMerge_nil_left]
      exact List.getElem?_eq_getElem hj'
    · intro c hc
      simp at hc
  | case2 xs hne =>
    intro j hj
    have hj' : j < xs.length := by simpa [blkMerge_nil_right] using hj
    refine ⟨j, 0, by omega, by simp, by omega, ?_, Or.inl ⟨xs[j]'hj', ?_, ?_, ?_⟩⟩
    · simp [blkMerge_nil_right]
    · exact List.getElem?_eq_getElem hj'
    · rw [blkMerge_nil_right]
      exact List.getElem?_eq_getElem hj'
    · intro c hc
      simp at hc
  | case3 x xs y ys h ih =>
    intro j hj
    cases j with
    | zero =>
      refine ⟨0, 0, by simp, by simp, by simp, ?_, Or.inl ⟨x, ?_, ?_, ?_⟩⟩
      · simp [blkMerge_cons_cons_of_le h, blkMerge_nil_left]
      · rw [List.getElem?_cons_zero]
      · rw [blkMerge_cons_cons_of_le h, List.getElem?_cons_zero]
      · intro c hc
        rw [List.getElem?_cons_zero] at hc
        rw [← Option.some.inj hc]
        exact h
    | succ k =>
      have hk : k < (blkMerge proj xs (y :: ys)).length := by
        simp [blkMerge_cons_cons_of_le h] at hj; omega
      obtain ⟨p', q', hp', hq', hpq, htake, hdisj⟩ := ih k hk
      have hcond : ∀ y' ys', (y :: ys).take q' = y' :: ys' → PairLe proj x y' = true := by
        intro y' ys' heq
        cases q' with
        | zero => simp at heq
        | succ q'' =>
          rw [List.take_succ_cons] at heq
          cases heq
          exact h
      have htake' : (blkMerge proj (x :: xs) (y :: ys)).take (k + 1) =
          blkMerge proj ((x :: xs).take (p' + 1)) ((y :: ys).take q') := by
        calc (blkMerge proj (x :: xs) (y :: ys)).take (k + 1)
            = (x :: blkMerge proj xs (y :: ys)).take (k + 1) := by
              rw [blkMerge_cons_cons_of_le h]
          _ = x :: (blkMerge proj xs (y :: ys)).take k := by rw [List.take_succ_cons]
          _ = x :: blkMerge proj (xs.take p') ((y :: ys).take q') := by rw [htake]
          _ = blkMerge proj (x :: xs.take p') ((y :: ys).take q') :=
              (blkMerge_cons_left (x := x) (xs := xs.take p') (Y := y :: ys) (q := q') hcond).symm
          _ = blkMerge proj ((x :: xs).take (p' + 1)) ((y :: ys).take q') := by
              rw [List.take_succ_cons]
      refine ⟨p' + 1, q', by simp; omega, hq', by omega, htake', ?_⟩
      rcases hdisj with ⟨b, hxb, hLb, hcond2⟩ | ⟨b, hyb, hLb, hcond2⟩
      · refine Or.inl ⟨b, ?_, ?_, hcond2⟩
        · rw [List.getElem?_cons_succ]; exact hxb
        · rw [blkMerge_cons_cons_of_le h, List.getElem?_cons_succ]; exact hLb
      · refine Or.inr ⟨b, hyb, ?_, ?_⟩
        · rw [blkMerge_cons_cons_of_le h, List.getElem?_cons_succ]; exact hLb
        · intro c hc
          rw [List.getElem?_cons_succ] at hc
          exact hcond2 c hc
  | case4 x xs y ys h ih =>
    intro j hj
    cases j with
    | zero =>
      have hfalse : PairLe proj x y = false := Bool.eq_false_iff.mpr h
      refine ⟨0, 0, by simp, by simp, by simp, ?_, Or.inr ⟨y, ?_, ?_, ?_⟩⟩
      · simp [blkMerge_cons_cons_of_not_le hfalse, blkMerge_nil_left]
      · rw [List.getElem?_cons_zero]
      · rw [blkMerge_cons_cons_of_not_le hfalse, List.getElem?_cons_zero]
      · intro c hc
        rw [List.getElem?_cons_zero] at hc
        rw [← Option.some.inj hc]
        exact hfalse
    | succ k =>
      have hfalse : PairLe proj x y = false := Bool.eq_false_iff.mpr h
      have hk : k < (blkMerge proj (x :: xs) ys).length := by
        simp [blkMerge_cons_cons_of_not_le hfalse] at hj; omega
      obtain ⟨p', q', hp', hq', hpq, htake, hdisj⟩ := ih k hk
      have hcond : ∀ x' xs', (x :: xs).take p' = x' :: xs' → PairLe proj x' y = false := by
        intro x' xs' heq
        cases p' with
        | zero => simp at heq
        | succ p'' =>
          rw [List.take_succ_cons] at heq
          cases heq
          exact hfalse
      have htake' : (blkMerge proj (x :: xs) (y :: ys)).take (k + 1) =
          blkMerge proj ((x :: xs).take p') ((y :: ys).take (q' + 1)) := by
        calc (blkMerge proj (x :: xs) (y :: ys)).take (k + 1)
            = (y :: blkMerge proj (x :: xs) ys).take (k + 1) := by
              rw [blkMerge_cons_cons_of_not_le hfalse]
          _ = y :: (blkMerge proj (x :: xs) ys).take k := by rw [List.take_succ_cons]
          _ = y :: blkMerge proj ((x :: xs).take p') (ys.take q') := by rw [htake]
          _ = blkMerge proj ((x :: xs).take p') (y :: ys.take q') :=
              (blkMerge_cons_right (y := y) (ys := ys.take q') (X := x :: xs) (p := p') hcond).symm
          _ = blkMerge proj ((x :: xs).take p') ((y :: ys).take (q' + 1)) := by
              rw [List.take_succ_cons]
      refine ⟨p', q' + 1, hp', by simp; omega, by omega, htake', ?_⟩
      rcases hdisj with ⟨b, hxb, hLb, hcond2⟩ | ⟨b, hyb, hLb, hcond2⟩
      · refine Or.inl ⟨b, hxb, ?_, ?_⟩
        · rw [blkMerge_cons_cons_of_not_le hfalse, List.getElem?_cons_succ]; exact hLb
        · intro c hc
          rw [List.getElem?_cons_succ] at hc
          exact hcond2 c hc
      · refine Or.inr ⟨b, ?_, ?_, hcond2⟩
        · rw [List.getElem?_cons_succ]; exact hyb
        · rw [blkMerge_cons_cons_of_not_le hfalse, List.getElem?_cons_succ]; exact hLb

/-! ## The counting lemma -/

/-- A block straddles `t` when one of its elements is strictly above `t`. -/
def Straddle (proj : α → β) (t : β) (c : List α) : Prop :=
  ∃ x ∈ c, Cmp.blt t (proj x) = true

/-- At most one block of `l` straddles `t` (positionally, since equal blocks can
occur twice). -/
def StraddleUnique (proj : α → β) (t : β) (l : List (List α)) : Prop :=
  ∀ (i j : Nat) (hi : i < l.length) (hj : j < l.length), i < j →
    ¬(Straddle proj t (l[i]'hi) ∧ Straddle proj t (l[j]'hj))

omit [Cmp β] in
theorem keyFst_eq_some_of_head {proj : α → β} {c : List α} {x : α} (h : c.head? = some x) :
    keyFst proj c = some (proj x) := by
  simp [keyFst, h]

/-- A positive count exposes an element satisfying the predicate (constructively,
unlike the contrapositive of `countP_eq_zero`). -/
theorem exists_of_countP_pos {γ : Type w} {p : γ → Bool} {l : List γ}
    (h : 0 < l.countP p) : ∃ x ∈ l, p x = true := by
  have hf : l.filter p ≠ [] := by
    intro hnil
    have h0 : l.countP p = 0 := by rw [List.countP_eq_length_filter, hnil]; rfl
    omega
  obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil hf
  have hmem : x ∈ l.filter p := by rw [hx]; exact List.mem_cons_self ..
  exact ⟨x, (List.mem_filter.mp hmem).1, (List.mem_filter.mp hmem).2⟩

/-- One straddling block contributes at most its length (which is at most `bs`). -/
theorem countP_flatten_le_of_straddleUnique {proj : α → β} {t : β} {l : List (List α)}
    {bs : Nat} (hlen : ∀ c ∈ l, c.length ≤ bs) (h : StraddleUnique proj t l) :
    (l.flatten).countP (fun x => Cmp.blt t (proj x)) ≤ bs := by
  induction l with
  | nil => simp
  | cons c rest ih =>
    rw [List.flatten_cons, List.countP_append]
    by_cases hc : c.countP (fun x => Cmp.blt t (proj x)) = 0
    · rw [hc, Nat.zero_add]
      refine ih (fun d hd => hlen d (List.mem_cons_of_mem c hd)) ?_
      intro i j hi hj hij hst
      refine h (i + 1) (j + 1) (by simpa) (by simpa) (by omega) ?_
      rwa [List.getElem_cons_succ, List.getElem_cons_succ]
    · have hcpos : 0 < c.countP (fun x => Cmp.blt t (proj x)) := by omega
      obtain ⟨y, hyc, hyblt⟩ : ∃ y ∈ c, Cmp.blt t (proj y) = true :=
        exists_of_countP_pos (p := fun x => Cmp.blt t (proj x)) (l := c) hcpos
      have hrest : ∀ d ∈ rest, d.countP (fun x => Cmp.blt t (proj x)) = 0 := by
        intro d hd
        by_cases hd0 : d.countP (fun x => Cmp.blt t (proj x)) = 0
        · exact hd0
        · exfalso
          have hdpos : 0 < d.countP (fun x => Cmp.blt t (proj x)) := by omega
          obtain ⟨x, hxd, hxblt⟩ : ∃ x ∈ d, Cmp.blt t (proj x) = true :=
            exists_of_countP_pos (p := fun x => Cmp.blt t (proj x)) (l := d) hdpos
          obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hd
          exact h 0 (i + 1) (by simp) (by simp; omega) (by omega)
            ⟨⟨y, hyc, hyblt⟩, ⟨x, hxd, hxblt⟩⟩
      have hrest' : ∀ x ∈ rest.flatten, Cmp.blt t (proj x) = false := by
        intro x hx
        obtain ⟨d, hd, hxd⟩ := List.mem_flatten.mp hx
        cases hb : Cmp.blt t (proj x) with
        | false => rfl
        | true =>
          have hpos : 0 < d.countP (fun z => Cmp.blt t (proj z)) :=
            countP_pos_of_mem (p := fun z => Cmp.blt t (proj z)) hxd hb
          rw [hrest d hd] at hpos
          omega
      rw [countP_eq_zero_of_all hrest', Nat.add_zero]
      exact Nat.le_trans List.countP_le_length (hlen c List.mem_cons_self)

/-- In a run-ordered block list, no element of the blocks before block `p` exceeds the
first key of block `p`.  (This is the "left part contributes nothing" half of the
counting argument for the block merge.) -/
theorem countP_take_flatten_eq_zero {proj : α → β} {xs : List (List α)}
    (hxr : RunOrdered proj xs) {p : Nat} {b : List α} {a : α}
    (hxb : xs[p]? = some b) (ha : b.head? = some a) :
    ((xs.take p).flatten).countP (fun x => Cmp.blt (proj a) (proj x)) = 0 := by
  apply countP_eq_zero_of_all
  intro x hx
  obtain ⟨c, hc, hxc⟩ := List.mem_flatten.mp hx
  obtain ⟨i, hi, hci⟩ := List.mem_iff_getElem.mp hc
  have hp : p < xs.length := (List.getElem?_eq_some_iff.mp hxb).1
  have hxpeq : xs[p] = b := (List.getElem?_eq_some_iff.mp hxb).2
  have hi' : i < xs.length :=
    Nat.lt_of_lt_of_le hi (by rw [List.length_take]; exact Nat.min_le_right _ _)
  have hip : i < p :=
    Nat.lt_of_lt_of_le hi (by rw [List.length_take]; exact Nat.min_le_left _ _)
  have hcieq : xs[i] = c := by
    have h1 : (xs.take p)[i]? = some c := by rw [List.getElem?_eq_getElem hi, hci]
    rw [List.getElem?_take, ite_eq_left hip] at h1
    exact (List.getElem?_eq_some_iff.mp h1).2
  have hall : AllLe (KeyLe proj) c b := by
    have h1 := hxr.allLe_getElem i p hi' hp (by omega)
    rwa [hcieq, hxpeq] at h1
  exact Cmp.blt_eq_false_iff.mpr (hall x hxc a (List.mem_of_mem_head? (by simp [ha])))

/-- At most `bs` elements of the blocks before block `j` exceed the first key of block
`j`, as long as those blocks are pairwise ordered below `j`'s block.  Together with the
previous lemma this bounds the two runs' contributions to the merged prefix. -/
theorem countP_flatten_take_le {proj : α → β} {bs : Nat} {ys : List (List α)}
    (hbs : 0 < bs) (hyr : RunOrdered proj ys) (hylen : ∀ c ∈ ys, c.length = bs)
    {q : Nat} {b : List α} {a : α} (ha : b.head? = some a)
    (hpre : ∀ c ∈ ys.take q, PairLe proj c b = true) :
    ((ys.take q).flatten).countP (fun x => Cmp.blt (proj a) (proj x)) ≤ bs := by
  refine countP_flatten_le_of_straddleUnique (fun c hc =>
    Nat.le_of_eq (hylen c (List.mem_of_mem_take hc))) ?_
  intro i j hi hj hij hst
  have hi' : i < ys.length := by rw [List.length_take] at hi; omega
  have hj' : j < ys.length := by rw [List.length_take] at hj; omega
  have hst' : Straddle proj (proj a) (ys[i]'(by omega)) ∧
      Straddle proj (proj a) (ys[j]'(by omega)) := by
    rwa [List.getElem_take, List.getElem_take] at hst
  obtain ⟨x, hxmem, hxblt⟩ := hst'.1
  have hle1 : AllLe (KeyLe proj) (ys[i]'(by omega)) (ys[j]'(by omega)) :=
    hyr.allLe_getElem i j hi' hj' hij
  have hhead : ys[j]'(by omega) ≠ [] := by
    intro hnil
    have hlenj := hylen (ys[j]'(by omega)) (List.getElem_mem hj')
    rw [hnil] at hlenj
    simp at hlenj
    omega
  have hblt_head : Cmp.blt (proj a) (proj ((ys[j]'(by omega)).head hhead)) = true :=
    Cmp.blt_of_blt_of_ble hxblt
      (hle1 x hxmem ((ys[j]'(by omega)).head hhead) (List.head_mem hhead))
  have hmemj : ys[j]'(by omega) ∈ ys.take q := by
    rw [← List.getElem_take (h := hj)]
    exact List.getElem_mem hj
  have hble := PairLe_ble_fst (hpre (ys[j]'(by omega)) hmemj)
  rw [keyFst_eq_some_of_head (List.head?_eq_some_iff.mpr ⟨_, (List.cons_head_tail hhead).symm⟩),
    keyFst_eq_some_of_head ha] at hble
  exact absurd hble (by
    show ¬(Cmp.ble (proj ((ys[j]'(by omega)).head hhead)) (proj a) = true)
    rw [Cmp.not_ble_of_blt hblt_head]
    exact Bool.false_ne_true)

/-- **The counting lemma.** In the pair-sorted block merge of the blocks of two
sorted runs, at most `bs` elements of the blocks before position `j` exceed the
first key of block `j`. This is the fact that lets `block_merge_pairwise` keep the
merged prefix below the untouched suffix. -/
theorem countP_blkMerge_take_le (proj : α → β) {bs : Nat} (hbs : 0 < bs)
    {xs ys : List (List α)} (hxr : RunOrdered proj xs) (hyr : RunOrdered proj ys)
    (hxlen : ∀ c ∈ xs, c.length = bs) (hylen : ∀ c ∈ ys, c.length = bs)
    {j : Nat} (hj : j < (blkMerge proj xs ys).length)
    {b : List α} (hb : (blkMerge proj xs ys)[j]? = some b) {a : α} (ha : b.head? = some a) :
    (((blkMerge proj xs ys).take j).flatten).countP (fun x => Cmp.blt (proj a) (proj x))
      ≤ bs := by
  obtain ⟨p, q, _, _, _, htake, hdisj⟩ := blkMerge_take_succ proj xs ys j hj
  have hpair := blkMerge_sorted proj xs ys
    (hxr.pairSorted (fun c hc hnil => by have := hxlen c hc; rw [hnil] at this; simp at this; omega))
    (hyr.pairSorted (fun c hc hnil => by have := hylen c hc; rw [hnil] at this; simp at this; omega))
  obtain ⟨hjlen, hbj⟩ := List.getElem?_eq_some_iff.mp hb
  have hLseq : (blkMerge proj xs ys).take j ++ [b] = (blkMerge proj xs ys).take (j + 1) := by
    rw [← hbj, ← List.concat_eq_append]
    exact List.take_concat_get hjlen
  have hpre : ∀ c ∈ (blkMerge proj xs ys).take j, PairLe proj c b = true := by
    intro c hc
    have hsorted : Sorted (fun x y => PairLe proj x y = true)
        ((blkMerge proj xs ys).take j ++ [b]) := by
      rw [hLseq]
      exact sorted_take hpair
    exact (sorted_append_iff.mp hsorted).2.2 c hc b (List.mem_singleton_self b)
  have ha' : a ∈ b := List.mem_of_mem_head? (by simp [ha])
  have hpreX : ∀ c ∈ xs.take p, PairLe proj c b = true := by
    intro c hc
    refine hpre c ?_
    rw [htake]
    exact mem_blkMerge (proj := proj) (xs := xs.take p) (ys := ys.take q) (b := c) (Or.inl hc)
  have hpreY : ∀ c ∈ ys.take q, PairLe proj c b = true := by
    intro c hc
    refine hpre c ?_
    rw [htake]
    exact mem_blkMerge (proj := proj) (xs := xs.take p) (ys := ys.take q) (b := c) (Or.inr hc)
  rw [htake, countP_eq_of_perm (blkMerge_flatten_perm proj (xs.take p) (ys.take q)),
    List.countP_append]
  rcases hdisj with ⟨b', hxb, hLb, _⟩ | ⟨b', hyb, hLb, _⟩
  · have hbeq : b = b' := by rw [hb] at hLb; exact Option.some.inj hLb
    subst hbeq
    rw [countP_take_flatten_eq_zero hxr hxb ha, Nat.zero_add]
    exact countP_flatten_take_le hbs hyr hylen ha hpreY
  · have hbeq : b = b' := by rw [hb] at hLb; exact Option.some.inj hLb
    subst hbeq
    rw [countP_take_flatten_eq_zero hyr hyb ha, Nat.add_zero]
    exact countP_flatten_take_le hbs hxr hxlen ha hpreX

/-! ## Multiset inclusion and the merge of two blocks -/

/-- `SubMul l₁ l₂` says every element of `l₁` occurs in `l₂` at least as often.
This count form of multiset inclusion is exactly what the counting argument uses,
and it is closed under appending on both sides. -/
def SubMul {γ : Type w} (l₁ l₂ : List γ) : Prop := ∀ p : γ → Bool, l₁.countP p ≤ l₂.countP p

theorem SubMul.refl {γ : Type w} (l : List γ) : SubMul l l := fun _ => Nat.le_refl _

theorem SubMul.trans {γ : Type w} {a b c : List γ} (h₁ : SubMul a b) (h₂ : SubMul b c) :
    SubMul a c := fun p => Nat.le_trans (h₁ p) (h₂ p)

theorem SubMul.append {γ : Type w} {a b c d : List γ} (h₁ : SubMul a c)
    (h₂ : SubMul b d) : SubMul (a ++ b) (c ++ d) :=
  fun p => by rw [List.countP_append, List.countP_append]; have := h₁ p; have := h₂ p; omega

theorem SubMul.append_right {γ : Type w} {a b : List γ} (h : SubMul a b) (c : List γ) :
    SubMul a (b ++ c) :=
  fun p => by rw [List.countP_append]; have := h p; omega

theorem SubMul.append_left {γ : Type w} {a b : List γ} (h : SubMul a b) (c : List γ) :
    SubMul a (c ++ b) :=
  fun p => by rw [List.countP_append]; have := h p; omega

theorem SubMul.of_perm {γ : Type w} {a b : List γ} (h : List.Perm a b) : SubMul a b :=
  fun _ => Nat.le_of_eq (countP_eq_of_perm h)

theorem mergeTwo_length (proj : α → β) (xs ys : List α) :
    (mergeTwo proj xs ys).length = xs.length + ys.length := by
  induction xs, ys using mergeTwo.induct proj with
  | case1 ys => rw [mergeTwo_nil_left]; simp
  | case2 xs hne => rw [mergeTwo_nil_right]; simp
  | case3 x xs y ys h ih =>
    rw [mergeTwo_cons_cons_of_ble h]
    simp only [List.length_cons, ih]
    omega
  | case4 x xs y ys h ih =>
    rw [mergeTwo_cons_cons_of_not_ble (by simpa using h)]
    simp only [List.length_cons, ih]
    omega

/-- If at most `bs` elements of a sorted `2*bs` list exceed `t`, then the first
half of the list is entirely at most `t`. This is how the counting lemma turns
into `AllLe`. -/
theorem ble_of_countP_le {proj : α → β} {M : List α} {t : β} {bs : Nat}
    (hs : Sorted (KeyLe proj) M) (hlen : M.length = 2 * bs)
    (hc : M.countP (fun x => Cmp.blt t (proj x)) ≤ bs) :
    ∀ x ∈ M.take bs, Cmp.ble (proj x) t = true := by
  intro x hx
  by_cases hble : Cmp.ble (proj x) t = true
  · exact hble
  · exfalso
    have hxt : Cmp.ble (proj x) t = false := by cases h : Cmp.ble (proj x) t <;> simp_all
    have hblt : Cmp.blt t (proj x) = true := by
      refine Cmp.blt_of_ble_of_not_ble ?_ hxt
      rcases Cmp.ble_total t (proj x) with h | h
      · exact h
      · rw [h] at hble; exact absurd rfl hble
    have hdrop : ∀ y ∈ M.drop bs, Cmp.blt t (proj y) = true := by
      intro y hy
      exact Cmp.blt_of_blt_of_ble hblt
        (allLe_take_drop_of_sorted hs x hx y hy)
    have hc1 : 1 ≤ (M.take bs).countP (fun z => Cmp.blt t (proj z)) :=
      countP_pos_of_mem hx hblt
    have hc2 : (M.drop bs).countP (fun z => Cmp.blt t (proj z)) = bs := by
      rw [countP_eq_length_of_all hdrop, List.length_drop, hlen]
      omega
    have hsum := List.countP_append (l₁ := M.take bs) (l₂ := M.drop bs)
      (p := fun z => Cmp.blt t (proj z))
    rw [List.take_append_drop] at hsum
    omega

/-- First keys are nondecreasing along a block list. -/
def FstMono (proj : α → β) (l : List (List α)) : Prop :=
  ∀ (i j : Nat) (hi : i < l.length) (hj : j < l.length), i < j →
    occLe (keyFst proj l[i]) (keyFst proj l[j]) = true

theorem FstMono_of_pairSorted {proj : α → β} {l : List (List α)}
    (h : Sorted (fun x y => PairLe proj x y = true) l) : FstMono proj l := by
  intro i j hi hj hij
  exact PairLe_ble_fst (x := l[i]) (y := l[j])
    (List.Pairwise.rel_getElem_of_lt hi hj h hij)

theorem FstMono.tail {proj : α → β} {l : List (List α)} (h : FstMono proj l) :
    FstMono proj l.tail := by
  intro i j hi hj hij
  cases l with
  | nil => simp at hi
  | cons a t =>
    simp only [List.tail_cons] at hi hj ⊢
    have h1 := h (i + 1) (j + 1) (by simp; omega) (by simp; omega) (by omega)
    simpa only [List.getElem_cons_succ] using h1

/-! ## `block_merge_pairwise` -/

/-- The dirty block can move past the high block: the multiset is unchanged. -/
theorem perm_swap_append_left {γ : Type w} (D H Z Y : List γ) :
    List.Perm (H ++ D ++ Z ++ Y) (D ++ H ++ Z ++ Y) := by
  simpa [List.append_assoc] using
    List.Perm.append_right (Z ++ Y) (List.perm_append_comm (l₁ := H) (l₂ := D))

/-- Stable under gluing a middle and a suffix: if `a ++ b` permutes `u ++ v` then
`a ++ x ++ b ++ y` permutes `u ++ x ++ v ++ y`. This is the shape in which the
merge replaces the two live blocks of `block_merge_pairwise`. -/
theorem Perm.append_mid {γ : Type w} {a b u v x y : List γ}
    (h : List.Perm (a ++ b) (u ++ v)) :
    List.Perm (a ++ x ++ b ++ y) (u ++ x ++ v ++ y) := by
  have h1 : List.Perm (a ++ (x ++ b) ++ y) (a ++ (b ++ x) ++ y) :=
    List.Perm.append_right y (List.Perm.append_left a (List.perm_append_comm (l₁ := x) (l₂ := b)))
  have h2 : List.Perm (u ++ (x ++ v) ++ y) (u ++ (v ++ x) ++ y) :=
    List.Perm.append_right y (List.Perm.append_left u (List.perm_append_comm (l₁ := x) (l₂ := v)))
  have h3 : List.Perm (a ++ (b ++ x) ++ y) (u ++ (v ++ x) ++ y) := by
    simpa only [List.append_assoc] using List.Perm.append_right (x ++ y) h
  have h4 : List.Perm (a ++ (x ++ b) ++ y) (u ++ (x ++ v) ++ y) := h1.trans (h3.trans h2.symm)
  simpa only [List.append_assoc] using h4

theorem SubMul.of_perm_append {γ : Type w} {a b L : List γ} (h : List.Perm (a ++ L) b) :
    SubMul a b := by
  intro p
  have h1 : (a ++ L).countP p = b.countP p := countP_eq_of_perm h
  rw [List.countP_append] at h1
  omega

theorem SubMul.drop {γ : Type w} {M : List γ} {bs : Nat} : SubMul (M.drop bs) M :=
  SubMul.of_perm_append ((List.perm_append_comm (l₁ := M.drop bs) (l₂ := M.take bs)).trans
    (List.Perm.of_eq (List.take_append_drop bs M)))

theorem length_flatten_eq {γ : Type w} {l : List (List γ)} {n : Nat}
    (h : ∀ b ∈ l, b.length = n) : l.flatten.length = l.length * n := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.flatten_cons, List.length_append, h a (by simp),
      ih (fun b hb => h b (List.mem_cons_of_mem a hb)), List.length_cons, Nat.succ_mul]
    omega

/-- In a sorted block, the first element is below all of them. -/
theorem allLe_singleton_head {proj : α → β} {b : List α} {a : α}
    (hb : Sorted (KeyLe proj) b) (ha : b.head? = some a) : AllLe (KeyLe proj) [a] b := by
  obtain ⟨t, rfl⟩ := List.head?_eq_some_iff.mp ha
  intro x hx y hy
  rw [List.mem_singleton] at hx
  subst hx
  rcases List.mem_cons.mp hy with rfl | hy'
  · exact Cmp.ble_refl _
  · exact (List.pairwise_cons.mp hb).1 y hy'

/-- A list whose elements are all at most `a` lies below a sorted block whose
first key is `a`. -/
theorem allLe_of_ble_head {proj : α → β} {X : List α} {a : α} {b : List α}
    (hX : ∀ x ∈ X, Cmp.ble (proj x) (proj a) = true)
    (hb : Sorted (KeyLe proj) b) (ha : b.head? = some a) : AllLe (KeyLe proj) X b :=
  fun x hx y hy => Cmp.ble_trans (hX x hx) (allLe_singleton_head hb ha a (List.mem_singleton_self a) y hy)

/-- The counting lemma in the split form used by the loop invariant: with
`blks = b0 :: mid ++ W :: rest`, at most `bs` elements of `b0 :: mid` exceed the
first key of `W`. -/
theorem countP_split_le (proj : α → β) {bs : Nat} (hbs : 0 < bs)
    {blks xs ys : List (List α)} (hblks : blks = blkMerge proj xs ys)
    (hxr : RunOrdered proj xs) (hyr : RunOrdered proj ys)
    (hxlen : ∀ c ∈ xs, c.length = bs) (hylen : ∀ c ∈ ys, c.length = bs)
    {b0 W : List α} {mid rest : List (List α)} (h : blks = b0 :: mid ++ W :: rest)
    {a : α} (ha : W.head? = some a) :
    (((b0 :: mid).flatten).countP (fun x => Cmp.blt (proj a) (proj x))) ≤ bs := by
  have hj : mid.length + 1 < blks.length := by
    rw [h]
    simp only [List.length_cons, List.length_append]
    omega
  have hb : blks[mid.length + 1]? = some W := by
    rw [h, List.cons_append, List.getElem?_cons_succ, List.getElem?_append_right (by omega)]
    simp
  have htake : blks.take (mid.length + 1) = b0 :: mid := by
    rw [h, List.cons_append, List.take_succ_cons, List.take_append_of_le_length (by omega),
      List.take_length]
  have hj' : mid.length + 1 < (blkMerge proj xs ys).length := by rwa [hblks] at hj
  have hb' : (blkMerge proj xs ys)[mid.length + 1]? = some W := by rwa [← hblks]
  have hc := countP_blkMerge_take_le proj hbs hxr hyr hxlen hylen hj' hb' ha
  rw [← hblks] at hc
  rwa [htake] at hc

/-- Invariant of the `block_merge_pairwise` state. The current block list is
`done ++ D :: H :: suffix`: `done` is the finished prefix, `D` the dirty block
carried along (always a copy of the first input block), `H` the high block (the
previous merge's second half, or the first untouched block at the start) and
`suffix` the untouched rest. `blks = b₀ :: mid ++ suffix` records the input, and
`H`'s elements all come from `mid`. -/
structure BmInv (proj : α → β) (bs : Nat) (blks : List (List α))
    (done : List (List α)) (D H : List α) (suffix : List (List α)) where
  b0 : List α
  mid : List (List α)
  hdecomp : blks = b0 :: mid ++ suffix
  hdone : done.length + 1 = mid.length
  hD : D = b0
  hperm : List.Perm (done ++ D :: H :: suffix).flatten blks.flatten
  hdonelen : ∀ b ∈ done, b.length = bs
  hHlen : H.length = bs
  hsorted : Sorted (KeyLe proj) done.flatten
  hle : AllLe (KeyLe proj) done.flatten (H :: suffix).flatten
  hsub : SubMul H mid.flatten
  hsortedD : Sorted (KeyLe proj) D
  hsortedH : Sorted (KeyLe proj) H
  hsortedSuffix : ∀ b ∈ suffix, Sorted (KeyLe proj) b
  hfst : FstMono proj suffix

/-- C++'s `block_merge_pairwise` loop, with explicit fuel. `rest = H :: Z :: …`:
`H` is the current high block and `Z` the next untouched one; their merge is
written to the finished prefix and the next high block, and `D` (the input's first
block, never read) is carried along. The last turn skips the block swap, which is
what leaves `D` at the very end. -/
def blockMergeStd (proj : α → β) (bs : Nat) :
    Nat → List (List α) → List α → List (List α) → List (List α)
  | 0, done, D, rest => done ++ D :: rest
  | fuel + 1, done, D, H :: Z :: (W :: rest') =>
      blockMergeStd proj bs fuel (done ++ [(mergeTwo proj H Z).take bs]) D
        ((mergeTwo proj H Z).drop bs :: W :: rest')
  | _ + 1, done, D, H :: Z :: [] =>
      done ++ [(mergeTwo proj H Z).take bs, (mergeTwo proj H Z).drop bs, D]
  | _ + 1, done, D, rest => done ++ D :: rest

/-- C++'s `block_merge_pairwise` on the whole block list. -/
def blockMergePairwise (proj : α → β) (bs : Nat) (blks : List (List α)) : List (List α) :=
  match blks with
  | [] => []
  | b0 :: rest => blockMergeStd proj bs rest.length [] b0 rest

/-- Below `a` in the first key of every block, everything in the flattened blocks
is above `a`. -/
theorem allLe_of_ble_head? {proj : α → β} {X : List α} {a : α} {l : List (List α)}
    (hX : ∀ x ∈ X, Cmp.ble (proj x) (proj a) = true)
    (hl : ∀ b ∈ l, Sorted (KeyLe proj) b) (hne : ∀ b ∈ l, b ≠ [])
    (hfirst : ∀ b ∈ l, ∀ c, b.head? = some c → Cmp.ble (proj a) (proj c) = true) :
    AllLe (KeyLe proj) X l.flatten := by
  intro x hx y hy
  obtain ⟨b, hb, hyb⟩ := List.mem_flatten.mp hy
  have hbne := hne b hb
  have hhead : b.head? = some (b.head hbne) :=
    List.head?_eq_some_iff.mpr ⟨b.tail, (List.cons_head_tail hbne).symm⟩
  have h1 := hfirst b hb (b.head hbne) hhead
  have h2 : AllLe (KeyLe proj) [b.head hbne] b := allLe_singleton_head (hl b hb) hhead
  exact Cmp.ble_trans (hX x hx)
    (Cmp.ble_trans h1 (h2 (b.head hbne) (List.mem_singleton_self _) y hyb))

/-- `block_merge_pairwise` leaves the first `n_blocks - 1` blocks sorted. This is
the induction over the loop: the invariant is `BmInv`, the counting lemma supplies
"the new finished block is below everything left", and the last turn (which skips
the swap) puts the dirty block at the very end. -/
theorem blockMergeStd_spec (proj : α → β) {bs : Nat} {blks xs ys : List (List α)}
    (hblks : blks = blkMerge proj xs ys) (hbs : 0 < bs)
    (hxr : RunOrdered proj xs) (hyr : RunOrdered proj ys)
    (hxlen : ∀ c ∈ xs, c.length = bs) (hylen : ∀ c ∈ ys, c.length = bs)
    (hsorted : ∀ b ∈ blks, Sorted (KeyLe proj) b) :
    ∀ (fuel : Nat) (done : List (List α)) (D H : List α) (suffix : List (List α)),
      2 ≤ (H :: suffix).length → (H :: suffix).length ≤ fuel →
      BmInv proj bs blks done D H suffix →
      Sorted (KeyLe proj)
        ((blockMergeStd proj bs fuel done D (H :: suffix)).flatten.take
          ((blks.length - 1) * bs)) := by
  have hblocks : ∀ b ∈ blks, b.length = bs := by
    intro b hb
    rw [hblks] at hb
    rcases blkMerge_mem hb with h | h
    · exact hxlen b h
    · exact hylen b h
  have hbne : ∀ b ∈ blks, b ≠ [] := by
    intro b hb hnil
    have hlen := hblocks b hb
    rw [hnil] at hlen
    simp at hlen
    omega
  intro fuel
  induction fuel with
  | zero => intro done D H suffix h2 hf _; exfalso; omega
  | succ fuel ih =>
    intro done D H suffix h2 hf hinv
    obtain ⟨b0, mid, hdecomp, hdone, hD, hperm, hdonelen, hHlen, hsrt, hle, hsub, hDsort,
      hHsort, hsufsort, hfst⟩ := hinv
    cases suffix with
    | nil => exfalso; simp at h2
    | cons Z suffix' =>
      cases suffix' with
      | nil =>
        -- last turn: merge `H` and `Z`, skip the block swap
        have hZmem : Z ∈ blks := by rw [hdecomp]; simp
        have hZlen : Z.length = bs := hblocks Z hZmem
        have hZsort : Sorted (KeyLe proj) Z := hsorted Z hZmem
        have hMlen : (mergeTwo proj H Z).length = 2 * bs := by
          rw [mergeTwo_length, hHlen, hZlen]; omega
        have hMsorted : Sorted (KeyLe proj) (mergeTwo proj H Z) :=
          mergeTwo_sorted proj H Z hHsort hZsort
        have hMmem : ∀ y ∈ mergeTwo proj H Z, y ∈ H ++ Z :=
          List.Perm.subset (mergeTwo_perm proj H Z)
        have hleM : AllLe (KeyLe proj) done.flatten (mergeTwo proj H Z) :=
          allLe_of_subset_right (by simpa using hle) hMmem
        have hsortedfinal : Sorted (KeyLe proj)
            (done.flatten ++ ((mergeTwo proj H Z).take bs ++ (mergeTwo proj H Z).drop bs)) :=
          sorted_append hsrt
            (sorted_append (sorted_take hMsorted) (sorted_drop hMsorted)
              (allLe_take_drop_of_sorted hMsorted))
            (allLe_append_right.mpr ⟨allLe_take_right hleM, allLe_drop_right hleM⟩)
        have hblkslen : blks.length = done.length + 3 := by
          rw [hdecomp]
          simp only [List.length_cons, List.length_append, List.length_nil]
          omega
        have hflatlen : done.flatten.length = done.length * bs := length_flatten_eq hdonelen
        have h1len : ((mergeTwo proj H Z).take bs ++ (mergeTwo proj H Z).drop bs).length = 2 * bs := by
          rw [List.take_append_drop, hMlen]
        have hXlen : (done.flatten ++ ((mergeTwo proj H Z).take bs ++ (mergeTwo proj H Z).drop bs)).length
            = (blks.length - 1) * bs := by
          rw [List.length_append, hflatlen, h1len, hblkslen,
            show done.length + 3 - 1 = done.length + 2 by omega, Nat.add_mul]
        rw [blockMergeStd.eq_3]
        have htakeconv :
            (done ++ [(mergeTwo proj H Z).take bs, (mergeTwo proj H Z).drop bs, D]).flatten.take
              ((blks.length - 1) * bs)
              = done.flatten ++ ((mergeTwo proj H Z).take bs ++ (mergeTwo proj H Z).drop bs) := by
          have hflat : (done ++ [(mergeTwo proj H Z).take bs, (mergeTwo proj H Z).drop bs, D]).flatten
              = (done.flatten ++ ((mergeTwo proj H Z).take bs ++ (mergeTwo proj H Z).drop bs)) ++ D := by
            rw [List.flatten_append, List.flatten_cons, List.flatten_cons, List.flatten_cons,
              List.flatten_nil, List.append_nil]
            simp only [List.append_assoc]
          rw [hflat, ← hXlen, List.take_append_of_le_length (h := Nat.le_refl _), List.take_length]
        rw [htakeconv]
        exact hsortedfinal
      | cons W suffix'' =>
        have hWmem : W ∈ blks := by rw [hdecomp]; simp
        have hWne : W ≠ [] := hbne W hWmem
        have hWsort : Sorted (KeyLe proj) W := hsorted W hWmem
        have hZmem : Z ∈ blks := by rw [hdecomp]; simp
        have hZlen : Z.length = bs := hblocks Z hZmem
        have hZsort : Sorted (KeyLe proj) Z := hsorted Z hZmem
        have hMlen : (mergeTwo proj H Z).length = 2 * bs := by
          rw [mergeTwo_length, hHlen, hZlen]; omega
        have hMsorted : Sorted (KeyLe proj) (mergeTwo proj H Z) :=
          mergeTwo_sorted proj H Z hHsort hZsort
        have hsplit : blks = (b0 :: (mid ++ [Z])) ++ (W :: suffix'') := by
          rw [hdecomp]
          show (b0 :: mid) ++ (Z :: W :: suffix'') = (b0 :: (mid ++ [Z])) ++ (W :: suffix'')
          rw [List.cons_append, List.cons_append, List.append_assoc, List.singleton_append]
        have hSufInBlks : ∀ b ∈ suffix'', b ∈ blks := by
          intro b hb
          rw [hdecomp]
          exact List.mem_cons_of_mem b0
            (List.mem_append_right _ (List.mem_cons_of_mem Z (List.mem_cons_of_mem W hb)))
        obtain ⟨a, ha⟩ : ∃ a, W.head? = some a := by
          obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil hWne
          exact ⟨a, rfl⟩
        have hcountB : (((b0 :: (mid ++ [Z])).flatten).countP
            (fun x => Cmp.blt (proj a) (proj x))) ≤ bs :=
          countP_split_le proj hbs hblks hxr hyr hxlen hylen hsplit ha
        have hsubMid : SubMul (H ++ Z) ((mid ++ [Z]).flatten) := by
          have h1 : SubMul (H ++ Z) (mid.flatten ++ Z) := SubMul.append hsub (SubMul.refl Z)
          simpa [List.flatten_append, List.flatten_cons] using h1
        have hMidMem : SubMul ((mid ++ [Z]).flatten) ((b0 :: (mid ++ [Z])).flatten) :=
          SubMul.append_left (SubMul.refl ((mid ++ [Z]).flatten)) b0
        have hcountHz : ((H ++ Z).countP (fun x => Cmp.blt (proj a) (proj x))) ≤ bs :=
          Nat.le_trans (hsubMid (fun x => Cmp.blt (proj a) (proj x)))
            (Nat.le_trans (hMidMem (fun x => Cmp.blt (proj a) (proj x))) hcountB)
        have hcountM : ((mergeTwo proj H Z).countP (fun x => Cmp.blt (proj a) (proj x))) ≤ bs :=
          Nat.le_trans (SubMul.of_perm (mergeTwo_perm proj H Z) _) hcountHz
        have hMt : ∀ x ∈ (mergeTwo proj H Z).take bs, Cmp.ble (proj x) (proj a) = true :=
          ble_of_countP_le hMsorted hMlen hcountM
        have hleW : AllLe (KeyLe proj) ((mergeTwo proj H Z).take bs) W :=
          allLe_of_ble_head hMt hWsort ha
        have hfstW : ∀ b ∈ suffix'', ∀ c, b.head? = some c →
            Cmp.ble (proj a) (proj c) = true := by
          intro b hb c hc
          obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hb
          have h1 := hfst 1 (i + 2) (by simp) (by simp; omega) (by omega)
          rw [List.getElem_cons_succ, List.getElem_cons_zero, List.getElem_cons_succ,
            List.getElem_cons_succ] at h1
          rw [keyFst_eq_some_of_head ha, keyFst_eq_some_of_head hc] at h1
          simpa [occLe] using h1
        have hleSuf : AllLe (KeyLe proj) ((mergeTwo proj H Z).take bs) suffix''.flatten :=
          allLe_of_ble_head? hMt (fun b hb => hsufsort b (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hb)))
            (fun b hb => hbne b (hSufInBlks b hb)) hfstW
        have hleHZ : AllLe (KeyLe proj) done.flatten (H ++ Z) :=
          allLe_of_subset_right hle (fun y hy => by
            rcases List.mem_append.mp hy with h | h
            · exact List.mem_append_left _ h
            · exact List.mem_append_right _ (List.mem_append_left _ h))
        have hMmem : ∀ y ∈ mergeTwo proj H Z, y ∈ H ++ Z :=
          List.Perm.subset (mergeTwo_perm proj H Z)
        have hleM : AllLe (KeyLe proj) done.flatten (mergeTwo proj H Z) :=
          allLe_of_subset_right hleHZ hMmem
        have hnew : BmInv proj bs blks (done ++ [(mergeTwo proj H Z).take bs])
            D ((mergeTwo proj H Z).drop bs) (W :: suffix'') := by
          refine ⟨b0, mid ++ [Z], hsplit, ?_, hD, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [List.length_append, List.length_singleton, hdone]; simp
          · have hMz : List.Perm ((mergeTwo proj H Z).take bs ++ (mergeTwo proj H Z).drop bs)
                (H ++ Z) := by
              rw [List.take_append_drop]; exact mergeTwo_perm proj H Z
            have hstep : List.Perm
                ((mergeTwo proj H Z).take bs ++ D ++ (mergeTwo proj H Z).drop bs ++
                  (W :: suffix'').flatten)
                (D ++ H ++ Z ++ (W :: suffix'').flatten) :=
              (Perm.append_mid (x := D) (y := (W :: suffix'').flatten) hMz).trans
                (perm_swap_append_left D H Z (W :: suffix'').flatten)
            have hmid := List.Perm.append_left done.flatten hstep
            have hpermb : List.Perm
                (done.flatten ++ (D ++ H ++ Z ++ (W :: suffix'').flatten)) blks.flatten := by
              simpa [List.flatten_append, List.flatten_cons, List.append_assoc] using hperm
            simpa [List.flatten_append, List.flatten_cons, List.append_assoc] using hmid.trans hpermb
          · intro b hb
            rcases List.mem_append.mp hb with hb | hb
            · exact hdonelen b hb
            · rw [List.mem_singleton] at hb
              subst hb
              rw [List.length_take, hMlen, Nat.min_eq_left (by omega)]
          · rw [List.length_drop, hMlen]; omega
          · simpa [List.flatten_append, List.flatten_cons] using
              sorted_append hsrt (sorted_take hMsorted) (allLe_take_right hleM)
          · have hdone' : AllLe (KeyLe proj) done.flatten
                ((mergeTwo proj H Z).drop bs ++ (W ++ suffix''.flatten)) := by
              refine allLe_append_right.mpr ⟨?_, ?_⟩
              · exact allLe_of_subset_right hleHZ (fun y hy => hMmem y (mem_of_mem_drop hy))
              · refine allLe_append_right.mpr ⟨?_, ?_⟩
                · exact allLe_of_subset_right hle (fun y hy =>
                    List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ hy)))
                · exact allLe_of_subset_right hle (fun y hy =>
                    List.mem_append_right _ (List.mem_append_right _
                      (List.mem_append_right _ hy)))
            have htake' : AllLe (KeyLe proj) ((mergeTwo proj H Z).take bs)
                ((mergeTwo proj H Z).drop bs ++ (W ++ suffix''.flatten)) := by
              refine allLe_append_right.mpr ⟨?_, ?_⟩
              · exact allLe_take_drop_of_sorted hMsorted
              · exact allLe_append_right.mpr ⟨hleW, hleSuf⟩
            have hfl : (done ++ [(mergeTwo proj H Z).take bs]).flatten
                = done.flatten ++ (mergeTwo proj H Z).take bs := by
              simp [List.flatten_append, List.flatten_cons]
            rw [hfl]
            exact allLe_append_left.mpr ⟨hdone', htake'⟩
          · exact (SubMul.drop.trans (SubMul.of_perm (mergeTwo_perm proj H Z))).trans hsubMid
          · exact hDsort
          · exact sorted_drop hMsorted
          · intro b hb
            rcases List.mem_cons.mp hb with rfl | hb
            · exact hWsort
            · exact hsufsort b (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hb))
          · exact hfst.tail
        have hfuel' : (List.drop bs (mergeTwo proj H Z) :: W :: suffix'').length ≤ fuel := by
          simp only [List.length_cons] at hf ⊢
          omega
        rw [blockMergeStd.eq_2]
        exact ih (done ++ [(mergeTwo proj H Z).take bs]) D ((mergeTwo proj H Z).drop bs)
          (W :: suffix'') (by simp) hfuel' hnew

/-- **`block_merge_pairwise` finishes all but the last block.** -/
theorem blockMergePairwise_sorted (proj : α → β) {bs : Nat} {blks xs ys : List (List α)}
    (hblks : blks = blkMerge proj xs ys) (hbs : 0 < bs)
    (hxr : RunOrdered proj xs) (hyr : RunOrdered proj ys)
    (hxlen : ∀ c ∈ xs, c.length = bs) (hylen : ∀ c ∈ ys, c.length = bs)
    (hsorted : ∀ b ∈ blks, Sorted (KeyLe proj) b) :
    Sorted (KeyLe proj)
      ((blockMergePairwise proj bs blks).flatten.take ((blks.length - 1) * bs)) := by
  have hblocks : ∀ b ∈ blks, b.length = bs := by
    intro b hb
    rw [hblks] at hb
    rcases blkMerge_mem hb with h | h
    · exact hxlen b h
    · exact hylen b h
  have hpair : Sorted (fun x y => PairLe proj x y = true) blks := by
    rw [hblks]
    refine blkMerge_sorted proj xs ys ?_ ?_
    · exact hxr.pairSorted (fun c hc hnil => by have := hxlen c hc; rw [hnil] at this; simp at this; omega)
    · exact hyr.pairSorted (fun c hc hnil => by have := hylen c hc; rw [hnil] at this; simp at this; omega)
  cases blks with
  | nil => simp [blockMergePairwise, Sorted]
  | cons b0 rest =>
    cases rest with
    | nil => simp [blockMergePairwise, blockMergeStd, Sorted]
    | cons H rest' =>
      cases rest' with
      | nil =>
        have hb0 : Sorted (KeyLe proj) b0 := hsorted b0 (by simp)
        have hb0len : b0.length = bs := hblocks b0 (by simp)
        have hgoal : (blockMergePairwise proj bs [b0, H]).flatten.take
            ((([b0, H] : List (List α)).length - 1) * bs) = b0 := by
          rw [show blockMergePairwise proj bs [b0, H] = [b0, H] from rfl]
          rw [show ([b0, H] : List (List α)).length - 1 = 1 from rfl, Nat.one_mul]
          rw [List.flatten_cons, List.flatten_cons, List.flatten_nil, List.append_nil]
          rw [List.take_append_of_le_length (h := by omega)]
          rw [List.take_of_length_le (h := by omega)]
        rw [hgoal]
        exact hb0
      | cons W suffix' =>
        have hHlen : H.length = bs := hblocks H (by simp)
        have hlen2 : 2 ≤ (H :: W :: suffix').length := by
          simp only [List.length_cons]; omega
        refine blockMergeStd_spec proj hblks hbs hxr hyr hxlen hylen hsorted
          (H :: W :: suffix').length [] b0 H (W :: suffix') hlen2 (Nat.le_refl _) ?_
        refine ⟨b0, [H], by simp, by simp, rfl, by simp, ?_, hHlen, sorted_nil _, ?_,
          (by simpa using SubMul.refl H), hsorted b0 (by simp), hsorted H (by simp), ?_,
          FstMono_of_pairSorted (sorted_drop (n := 2) hpair)⟩
        · intro b hb; simp at hb
        · intro x hx; simp at hx
        · intro b hb; exact hsorted b (by simp [hb])

/-! ## `block_selection_sort` -/

/-- C++'s `block_selection_sort` on the aligned prefix `A ++ B` (the `bs`-blocks of
the two sorted runs), reordered by the `(first key, last key)` pair. -/
def blockSelectionSort (proj : α → β) (bs p q : Nat) (A B : List α) : List (List α) :=
  blkMerge proj (chunks bs p A) (chunks bs q B)

/-- The block sort keeps every block internally sorted. -/
theorem blockSelectionSort_all_sorted {proj : α → β} {A B : List α} {p q bs : Nat}
    (hA : Sorted (KeyLe proj) A) (hB : Sorted (KeyLe proj) B) :
    ∀ b ∈ blockSelectionSort proj bs p q A B, Sorted (KeyLe proj) b := by
  unfold blockSelectionSort
  intro b hb
  rcases blkMerge_mem hb with h | h
  · exact chunksAux_all_sorted p A hA b h
  · exact chunksAux_all_sorted q B hB b h

/-- Every block of the aligned prefix still has length `bs`. -/
theorem blockSelectionSort_all_length {proj : α → β} {A B : List α} {p q bs : Nat}
    (hbs : 0 < bs) (hA : A.length = p * bs) (hB : B.length = q * bs) :
    ∀ b ∈ blockSelectionSort proj bs p q A B, b.length = bs := by
  unfold blockSelectionSort
  intro b hb
  rcases blkMerge_mem hb with h | h
  · exact chunksAux_all_length hbs p A (by omega) b h
  · exact chunksAux_all_length hbs q B (by omega) b h

/-- The block sort permutes the aligned prefix. -/
theorem blockSelectionSort_flatten_perm {proj : α → β} {A B : List α} {p q bs : Nat}
    (hA : A.length = p * bs) (hB : B.length = q * bs) :
    (blockSelectionSort proj bs p q A B).flatten.Perm (A ++ B) := by
  unfold blockSelectionSort
  have h := blkMerge_flatten_perm proj (chunks bs p A) (chunks bs q B)
  rw [chunks_flatten, chunks_flatten,
    List.take_of_length_le (by omega), List.take_of_length_le (by omega)] at h
  exact h

/-- The number of blocks is `p + q`, and they are ordered by key pair. -/
theorem chunks_length {bs m : Nat} (l : List α) (hbs : 0 < bs) (h : m * bs ≤ l.length) :
    (chunks bs m l).length = m :=
  chunksAux_length hbs m l h

theorem blockSelectionSort_length {proj : α → β} {A B : List α} {p q bs : Nat}
    (hbs : 0 < bs) (hA : A.length = p * bs) (hB : B.length = q * bs) :
    (blockSelectionSort proj bs p q A B).length = p + q := by
  unfold blockSelectionSort
  rw [blkMerge_length, chunks_length A hbs (by omega), chunks_length B hbs (by omega)]

theorem blockSelectionSort_pairSorted {proj : α → β} {A B : List α} {p q bs : Nat}
    (hbs : 0 < bs) (hA : A.length = p * bs) (hB : B.length = q * bs)
    (hAs : Sorted (KeyLe proj) A) (hBs : Sorted (KeyLe proj) B) :
    Sorted (fun x y => PairLe proj x y = true) (blockSelectionSort proj bs p q A B) := by
  unfold blockSelectionSort
  refine blkMerge_sorted proj _ _ ?_ ?_
  · refine (chunksAux_runOrdered p A hAs).pairSorted ?_
    intro c hc hnil
    have hlen := chunksAux_all_length hbs p A (by omega) c hc
    rw [hnil] at hlen; simp at hlen; omega
  · refine (chunksAux_runOrdered q B hBs).pairSorted ?_
    intro c hc hnil
    have hlen := chunksAux_all_length hbs q B (by omega) c hc
    rw [hnil] at hlen; simp at hlen; omega

/-! ## `block_merge_pairwise` only permutes -/

/-- The block merges only permute the flattened blocks. -/
theorem blockMergeStd_flatten_perm (proj : α → β) (bs : Nat) :
    ∀ (fuel : Nat) (done : List (List α)) (D H : List α) (suffix : List (List α))
      (L0 : List (List α)),
      (done ++ D :: H :: suffix).flatten.Perm L0.flatten →
      (blockMergeStd proj bs fuel done D (H :: suffix)).flatten.Perm L0.flatten := by
  intro fuel
  induction fuel with
  | zero => intro done D H suffix L0 h; simpa [blockMergeStd] using h
  | succ fuel ih =>
    intro done D H suffix L0 h
    cases suffix with
    | nil => simpa [blockMergeStd] using h
    | cons Z suffix' =>
      cases suffix' with
      | nil =>
        rw [blockMergeStd.eq_3]
        have hMz : List.Perm ((mergeTwo proj H Z).take bs ++ (mergeTwo proj H Z).drop bs)
            (H ++ Z) := by
          rw [List.take_append_drop]; exact mergeTwo_perm proj H Z
        have hstep : List.Perm
            (done.flatten ++ ((mergeTwo proj H Z).take bs ++ (mergeTwo proj H Z).drop bs ++ D))
            (done.flatten ++ (D ++ (H ++ Z))) := by
          refine List.Perm.append_left done.flatten ?_
          exact (List.Perm.append_right D hMz).trans
            (List.perm_append_comm (l₁ := H ++ Z) (l₂ := D))
        have hold : List.Perm (done.flatten ++ (D ++ (H ++ Z))) L0.flatten := by
          simpa [List.flatten_append, List.flatten_cons, List.append_assoc] using h
        have hnew : (done ++ [(mergeTwo proj H Z).take bs, (mergeTwo proj H Z).drop bs, D]).flatten
            = done.flatten ++ ((mergeTwo proj H Z).take bs ++ (mergeTwo proj H Z).drop bs ++ D) := by
          rw [List.flatten_append, List.flatten_cons, List.flatten_cons, List.flatten_cons,
            List.flatten_nil, List.append_nil]
          simp only [List.append_assoc]
        rw [hnew]
        exact hstep.trans hold
      | cons W suffix'' =>
        rw [blockMergeStd.eq_2]
        apply ih
        have hMz : List.Perm ((mergeTwo proj H Z).take bs ++ (mergeTwo proj H Z).drop bs)
            (H ++ Z) := by
          rw [List.take_append_drop]; exact mergeTwo_perm proj H Z
        have hstep : List.Perm
            (done.flatten ++ ((mergeTwo proj H Z).take bs ++
              (D ++ ((mergeTwo proj H Z).drop bs ++ (W :: suffix'').flatten))))
            (done.flatten ++ (D ++ (H ++ (Z ++ (W :: suffix'').flatten)))) := by
          refine List.Perm.append_left done.flatten ?_
          have h1 : List.Perm
              ((mergeTwo proj H Z).take bs ++ D ++ (mergeTwo proj H Z).drop bs ++
                (W :: suffix'').flatten)
              (H ++ D ++ Z ++ (W :: suffix'').flatten) :=
            Perm.append_mid (x := D) (y := (W :: suffix'').flatten) hMz
          have h2 : List.Perm (H ++ D ++ Z ++ (W :: suffix'').flatten)
              (D ++ H ++ Z ++ (W :: suffix'').flatten) :=
            perm_swap_append_left D H Z (W :: suffix'').flatten
          simpa only [List.append_assoc] using h1.trans h2
        have hold : List.Perm
            (done.flatten ++ (D ++ (H ++ (Z ++ (W :: suffix'').flatten)))) L0.flatten := by
          simpa [List.flatten_append, List.flatten_cons, List.append_assoc] using h
        have hgoal : ((done ++ [(mergeTwo proj H Z).take bs]) ++
              D :: (mergeTwo proj H Z).drop bs :: W :: suffix'').flatten
            = done.flatten ++ ((mergeTwo proj H Z).take bs ++
                (D ++ ((mergeTwo proj H Z).drop bs ++ (W :: suffix'').flatten))) := by
          rw [List.flatten_append, List.flatten_append, List.flatten_cons, List.flatten_cons,
            List.flatten_cons, List.flatten_nil, List.append_nil]
          simp only [List.append_assoc]
        rw [hgoal]
        exact hstep.trans hold

/-- `block_merge_pairwise` only permutes the flattened blocks. -/
theorem blockMergePairwise_flatten_perm (proj : α → β) (bs : Nat) (blks : List (List α)) :
    (blockMergePairwise proj bs blks).flatten.Perm blks.flatten := by
  cases blks with
  | nil => simp [blockMergePairwise]
  | cons b0 rest =>
    cases rest with
    | nil => simp [blockMergePairwise, blockMergeStd]
    | cons H suffix =>
      exact blockMergeStd_flatten_perm proj bs (H :: suffix).length [] b0 H suffix
        (b0 :: H :: suffix) (by simp)

/-! ## `inplace_unstable_merge` -/

/-- Newton's iteration keeps a positive guess positive. -/
theorem sqrt_iter_next_pos {n guess : Nat} (hn : 2 ≤ n) (hx : 0 < guess) :
    0 < (guess + n / guess) / 2 := by
  rcases Nat.lt_or_ge (guess + n / guess) 2 with hlt | hge
  · exfalso
    have h2 : guess < 2 := Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hlt
    have hg : guess = 1 := Nat.le_antisymm (Nat.le_of_lt_succ h2) (Nat.succ_le_of_lt hx)
    subst hg
    rw [Nat.div_one] at hlt
    omega
  · exact Nat.div_pos hge (by decide)

theorem sqrt_iter_pos {n : Nat} (hn : 2 ≤ n) :
    ∀ guess, 0 < guess → 0 < Nat.sqrt.iter n guess :=
  Nat.sqrt.iter.induct n (fun g => 0 < g → 0 < Nat.sqrt.iter n g)
    (fun x hlt ih hx => by
      rw [Nat.sqrt.iter.eq_1, dite_eq_left hlt]
      exact ih (sqrt_iter_next_pos hn hx))
    (fun x hnot hx => by
      rw [Nat.sqrt.iter.eq_1, dite_eq_right hnot]
      exact hx)

/-- `Nat.sqrt` of a positive number is positive, proved constructively (core's
`Nat.lt_succ_sqrt` pulls in `Classical.choice`, which this file must avoid). -/
theorem sqrt_pos_of_pos {n : Nat} (h : 0 < n) : 0 < Nat.sqrt n := by
  match n with
  | 0 => omega
  | 1 => rw [Nat.sqrt.eq_def, ite_eq_left (by decide : 1 ≤ 1)]; decide
  | m + 2 =>
    have hn : 2 ≤ m + 2 := by omega
    rw [Nat.sqrt.eq_def, ite_eq_right (by omega : ¬ (m + 2 ≤ 1))]
    exact sqrt_iter_pos hn _ (by rw [Nat.one_shiftLeft]; exact Nat.two_pow_pos _)

/-- C++'s `inplace_unstable_merge` on a list, with `k` the split index: the aligned
rotation, the two block phases, the tail bubble sort and the rotation merge. -/
def unstableMerge (proj : α → β) (l : List α) (k : Nat) : List α :=
  if l.length ≤ 1 then l
  else
    let bs := Nat.sqrt l.length
    let la := k / bs * bs
    let ra := (l.length - k) / bs * bs
    let al := la + ra
    let A1 := l.take la
    let B1 := (l.drop k).take ra
    let blks := blockSelectionSort proj bs (la / bs) (ra / bs) A1 B1
    let blks' := blockMergePairwise proj bs blks
    let l2 := blks'.flatten ++ (rotRange l la k (k + ra)).drop al
    let l3 := l2.take (al - bs) ++ bubbleSort proj (l2.drop (al - bs))
    mergeByRotation proj l3 0 (al - bs) l.length

/-- **`inplace_unstable_merge` sorts the whole range and only permutes it.** -/
theorem unstableMerge_sorted_and_perm (proj : α → β) (l : List α) {k : Nat}
    (hk : k ≤ l.length) (hA : SortedOn proj l 0 k) (hB : SortedOn proj l k l.length) :
    Sorted (KeyLe proj) (unstableMerge proj l k) ∧ (unstableMerge proj l k).Perm l := by
  by_cases hsmall : l.length ≤ 1
  · rw [unstableMerge, ite_eq_left hsmall]
    refine ⟨?_, List.Perm.refl _⟩
    match l with
    | [] => exact sorted_nil _
    | [x] =>
      cases k with
      | zero => simpa [SortedOn] using hB
      | succ k' =>
        have hk' : k' = 0 := by simp at hk; omega
        subst hk'
        simpa [SortedOn] using hA
  · have hlen : 2 ≤ l.length := by omega
    rw [unstableMerge, ite_eq_right hsmall]
    simp only []
    generalize hbsdef : Nat.sqrt l.length = bs
    generalize hladef : k / bs * bs = la
    generalize hradef : (l.length - k) / bs * bs = ra
    generalize haldef : la + ra = al
    generalize hA1def : l.take la = A1
    generalize hA2def : (l.drop la).take (k - la) = A2
    generalize hB1def : (l.drop k).take ra = B1
    generalize hB2def : l.drop (k + ra) = B2
    generalize hblksdef : blockSelectionSort proj bs (la / bs) (ra / bs) A1 B1 = blks
    generalize hblks'def : blockMergePairwise proj bs blks = blks'
    generalize hl2def : blks'.flatten ++ (rotRange l la k (k + ra)).drop al = l2
    generalize hl3def : l2.take (al - bs) ++ bubbleSort proj (l2.drop (al - bs)) = l3
    have hbs : 0 < bs := by rw [← hbsdef]; exact sqrt_pos_of_pos (by omega)
    have hlak : la ≤ k := by rw [← hladef]; exact Nat.div_mul_le_self k bs
    have hrale : ra ≤ l.length - k := by
      rw [← hradef]; exact Nat.div_mul_le_self (l.length - k) bs
    have hkr : k + ra ≤ l.length := by omega
    have hA1len : A1.length = la := by
      rw [← hA1def, List.length_take, Nat.min_eq_left (by omega)]
    have hA2len : A2.length = k - la := by
      rw [← hA2def, List.length_take, List.length_drop, Nat.min_eq_left (by omega)]
    have hB1len : B1.length = ra := by
      rw [← hB1def, List.length_take, List.length_drop, Nat.min_eq_left (by omega)]
    have hB2len : B2.length = l.length - (k + ra) := by
      rw [← hB2def, List.length_drop]
    have hpbs : la / bs * bs = la := by
      rw [← hladef]; rw [Nat.mul_div_cancel (k / bs) hbs]
    have hqbs : ra / bs * bs = ra := by
      rw [← hradef]; rw [Nat.mul_div_cancel ((l.length - k) / bs) hbs]
    -- the four-part decomposition of `l` and of the rotated list
    have hl : l = A1 ++ A2 ++ B1 ++ B2 := by
      have h1 : l = l.take la ++ (l.drop la).take (k - la) ++ l.drop k := take_drop_splice hlak
      have h2 : l.drop k = (l.drop k).take ra ++ l.drop (k + ra) := by
        rw [← List.drop_drop (i := ra) (j := k), List.take_append_drop]
      rw [h1, h2, ← hA1def, ← hA2def, ← hB1def, ← hB2def]
      simp only [List.append_assoc]
    have hrot : rotRange l la k (k + ra) = A1 ++ B1 ++ A2 ++ B2 := by
      rw [hl, ← hA1len, ← hB1len, show k = A1.length + A2.length by omega]
      exact rotRange_append A1 A2 B1 B2
    have hrd : (rotRange l la k (k + ra)).drop al = A2 ++ B2 := by
      rw [hrot, ← haldef,
        show A1 ++ B1 ++ A2 ++ B2 = (A1 ++ B1) ++ (A2 ++ B2) by simp only [List.append_assoc]]
      rw [List.drop_append_of_le_length (by simp [hA1len, hB1len]),
        List.drop_eq_nil_of_le (by simp [hA1len, hB1len]), List.nil_append]
    -- sortedness of the aligned runs
    have hA1sort : Sorted (KeyLe proj) A1 := by
      simpa [List.take_take, Nat.min_eq_left hlak, ← hA1def] using sorted_take (n := la) hA
    have hB1sort : Sorted (KeyLe proj) B1 := by
      simpa [List.take_take, Nat.min_eq_left hrale, ← hB1def] using sorted_take (n := ra) hB
    -- the block sort permutes and its blocks are sorted
    have hblks_perm : blks.flatten.Perm (A1 ++ B1) := by
      rw [← hblksdef]
      exact blockSelectionSort_flatten_perm (p := la / bs) (q := ra / bs) (by omega) (by omega)
    have hblks'len : (blks'.flatten).length = al := by
      have h1 : (blks'.flatten).length = blks.flatten.length := by
        rw [← hblks'def]
        exact (blockMergePairwise_flatten_perm proj bs blks).length_eq
      rw [h1, hblks_perm.length_eq, List.length_append, hA1len, hB1len, ← haldef]
    have hblkslen : blks.length = la / bs + ra / bs := by
      rw [← hblksdef]
      exact blockSelectionSort_length (proj := proj) (A := A1) (B := B1) (p := la / bs)
        (q := ra / bs) (bs := bs) hbs (by omega) (by omega)
    have hal_m : al = blks.length * bs := by
      rw [← haldef, hblkslen, Nat.add_mul, hpbs, hqbs]
    -- the block phase sorts everything but the last block
    have hpref : Sorted (KeyLe proj) ((blks'.flatten).take (al - bs)) := by
      have hspec := blockMergePairwise_sorted proj (bs := bs) (blks := blks)
        (xs := chunks bs (la / bs) A1) (ys := chunks bs (ra / bs) B1)
        (by rw [← hblksdef]; rfl) hbs
        (chunksAux_runOrdered (la / bs) A1 hA1sort)
        (chunksAux_runOrdered (ra / bs) B1 hB1sort)
        (fun c hc => chunksAux_all_length hbs (la / bs) A1 (by omega) c hc)
        (fun c hc => chunksAux_all_length hbs (ra / bs) B1 (by omega) c hc)
        (fun c hc => by
          rw [← hblksdef] at hc
          exact blockSelectionSort_all_sorted hA1sort hB1sort c hc)
      rw [hblks'def] at hspec
      rwa [show (blks.length - 1) * bs = al - bs by rw [hal_m, Nat.sub_mul, Nat.one_mul]] at hspec
    -- lengths and permutations of the two intermediate arrays
    have hl2len : l2.length = l.length := by
      rw [← hl2def, List.length_append, hblks'len, hrd, List.length_append, hA2len, hB2len]
      omega
    have hl2perm : l2.Perm l := by
      rw [← hl2def, hrd]
      have h1 : (blks'.flatten ++ (A2 ++ B2)).Perm ((A1 ++ B1) ++ (A2 ++ B2)) :=
        List.Perm.append_right _
          (by rw [← hblks'def]
              exact (blockMergePairwise_flatten_perm proj bs blks).trans hblks_perm)
      have h2 : ((A1 ++ B1) ++ (A2 ++ B2)).Perm l := by
        rw [show (A1 ++ B1) ++ (A2 ++ B2) = A1 ++ B1 ++ A2 ++ B2 by
          simp only [List.append_assoc]]
        rw [← hrot]
        exact rotRange_perm hlak (by omega) hkr
      exact h1.trans h2
    have hl3perm : l3.Perm l2 := by
      rw [← hl3def]
      have h := List.Perm.append_left (l2.take (al - bs)) (bubbleSort_perm proj (l2.drop (al - bs)))
      rwa [List.take_append_drop] at h
    -- the tail sort
    have hsortHead : SortedOn proj l3 0 (al - bs) := by
      rw [← hl3def]
      rw [SortedOn, Nat.sub_zero, List.drop_zero]
      rw [List.take_append_of_le_length (h := by rw [List.length_take]; omega),
        List.take_take, Nat.min_self]
      rw [← hl2def, List.take_append_of_le_length (h := by rw [hblks'len]; omega)]
      exact hpref
    have hsortTail : SortedOn proj l3 (al - bs) l.length := by
      rw [← hl3def]
      rw [SortedOn]
      rw [List.drop_append_of_le_length (by rw [List.length_take]; omega),
        List.drop_eq_nil_of_le (by rw [List.length_take]; omega), List.nil_append]
      have hlen : (bubbleSort proj (l2.drop (al - bs))).length = l.length - (al - bs) := by
        rw [(bubbleSort_perm proj (l2.drop (al - bs))).length_eq, List.length_drop, hl2len]
      rw [List.take_of_length_le (by omega)]
      exact bubbleSort_sorted proj _
    have hl3eq : l3.length = l.length := hl3perm.length_eq.trans hl2perm.length_eq
    have hmerge := mergeByRotation_sorted proj (l := l3) (first := 0) (mid := al - bs)
      (last := l.length) (by omega) (by omega) (by omega) hsortHead hsortTail
    have hmergeperm := mergeByRotation_perm proj (l := l3) (first := 0) (mid := al - bs)
      (last := l.length) (by omega) (by omega) (by omega) hsortHead hsortTail
    refine ⟨?_, hmergeperm.trans (hl3perm.trans hl2perm)⟩
    rw [SortedOn, Nat.sub_zero, List.drop_zero] at hmerge
    rwa [List.take_of_length_le (by rw [hmergeperm.length_eq, hl3eq]; omega)] at hmerge

/-- The `Array`-level statement, matching the C++ signature
`inplace_unstable_merge(first, mid, last)`: the whole array is sorted and only
permuted. -/
def unstableMergeArray (proj : α → β) (a : Array α) (mid : Nat) : Array α :=
  (unstableMerge proj a.toList mid).toArray

theorem unstableMergeArray_sorted_and_perm (proj : α → β) (a : Array α) {mid : Nat}
    (hmid : mid ≤ a.size) (hA : SortedOn proj a.toList 0 mid)
    (hB : SortedOn proj a.toList mid a.toList.length) :
    Sorted (KeyLe proj) (unstableMergeArray proj a mid).toList ∧
      (unstableMergeArray proj a mid).toList.Perm a.toList := by
  unfold unstableMergeArray
  rw [List.toList_toArray]
  exact unstableMerge_sorted_and_perm proj a.toList (by simpa using hmid) hA hB
