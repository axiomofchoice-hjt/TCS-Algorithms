/-
  The labelled block phase of C++'s `inplace_stable_merge`
  (`include/tcs/inplace/stable_merge.hpp`: `block_selection_sort`,
  `block_merge_pairwise`, `inplace_block_merge_pairwise`).

  The C++ distinguishes equal keys by *labels*: every block carries a label whose
  order is the order of the blocks in the array, and the two runs being merged are
  compared by `(key, label)` instead of by key. The labels are buffer values, so
  only their relative order matters; this module therefore models them by *tags*,
  the position of an element in the array. Tagging an element `x` at position `i`
  by `(x, i)` turns the C++ comparison into the lexicographic order
  `KeyLe (tagProj proj)` on tagged elements, under which the block phase is a plain
  merge.

  Its data part is then the `(key, tag)`-sorted merge of the blocks, and the
  specification proved below is exactly what the assembly needs: the data region is
  sorted, it is a permutation of what went in, and every equal-key subsequence
  survives. The last point is where stability comes from, because the tags increase
  along the array: sorting by `(key, tag)` sorts equal keys into their input order.

  Two structural notes. `blkLe`/`blkSortTag` mirror `block_selection_sort` (an
  insertion sort with the same comparison is enough: the *result* of the sort does
  not matter for the data region, only that the blocks are permuted with their
  elements, which is why the proofs below never use its order). And a merge of two
  blocks is `mergeTwo` at the tagged type: ties in the key fall to the smaller tag,
  which is the C++ tie-break by label.
-/
import Tcs.StableMerge

namespace Tcs

variable {α : Type u} {β : Type v} [Cmp β]

/-! ## Tags: the model of the C++ labels -/

/-- Tag each element with its position in the array, starting at `off`. -/
def tagFrom (off : Nat) : List α → List (α × Nat)
  | [] => []
  | x :: xs => (x, off) :: tagFrom (off + 1) xs

@[simp] theorem tagFrom_nil (off : Nat) : tagFrom off ([] : List α) = [] := rfl

@[simp] theorem tagFrom_cons (off : Nat) (x : α) (xs : List α) :
    tagFrom off (x :: xs) = (x, off) :: tagFrom (off + 1) xs := rfl

/-- Erasing the tags gives the original list. -/
theorem tagFrom_map_fst (off : Nat) (l : List α) : (tagFrom off l).map Prod.fst = l := by
  induction l generalizing off with
  | nil => rfl
  | cons x xs ih => simp [ih]

/-- The tags of `tagFrom off l` are exactly `off … off + l.length - 1`. -/
theorem tagFrom_snd_lt (off : Nat) : ∀ {l : List α} {p : α × Nat},
    p ∈ tagFrom off l → off ≤ p.2 ∧ p.2 < off + l.length := by
  intro l
  induction l generalizing off with
  | nil => intro p hp; simp at hp
  | cons x xs ih =>
    intro p hp
    rw [tagFrom_cons, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact ⟨Nat.le_refl _, by simp⟩
    · obtain ⟨h₁, h₂⟩ := ih (off + 1) hp
      exact ⟨Nat.le_trans (Nat.le_succ off) h₁, by simp only [List.length_cons]; omega⟩

/-- Equal tags in one tagged list mean equal entries: the tags increase strictly. -/
theorem tagFrom_snd_inj (off : Nat) : ∀ {l : List α} {p q : α × Nat},
    p ∈ tagFrom off l → q ∈ tagFrom off l → p.2 = q.2 → p = q := by
  intro l
  induction l generalizing off with
  | nil => intro p q hp; simp at hp
  | cons x xs ih =>
    intro p q hp hq heq
    rw [tagFrom_cons, List.mem_cons] at hp hq
    rcases hp with rfl | hp <;> rcases hq with rfl | hq
    · rfl
    · exact absurd heq (by have h := (tagFrom_snd_lt (off + 1) hq).1; omega)
    · exact absurd heq.symm (by have h := (tagFrom_snd_lt (off + 1) hp).1; omega)
    · exact ih (off + 1) hp hq heq

/-! ## The tag order -/

/-- The tagged key: the key first, the tag breaking ties (the C++ label comparison). -/
def tagProj (proj : α → β) (p : α × Nat) : β × Nat := (proj p.1, p.2)

/-- The tag order is at least as strong as the key order. -/
theorem ble_fst_of_prod_ble {a b : β × Nat} (h : Cmp.ble a b = true) :
    Cmp.ble a.1 b.1 = true := by
  rcases Cmp.prod_ble_iff.mp h with h | ⟨h, _⟩
  · exact Cmp.ble_of_blt h
  · rw [← h]; exact Cmp.ble_refl _

/-- Sorting by `(key, tag)` sorts by key. -/
theorem sorted_map_fst_of_sorted_tag {proj : α → β} {X : List (α × Nat)}
    (h : Sorted (KeyLe (tagProj proj)) X) : Sorted (KeyLe proj) (X.map Prod.fst) := by
  induction X with
  | nil => exact sorted_nil _
  | cons a t ih =>
    rw [List.map_cons]
    obtain ⟨h₁, h₂⟩ := (sorted_cons_iff (KeyLe (tagProj proj)) a t).mp h
    refine (sorted_cons_iff (KeyLe proj) a.1 (t.map Prod.fst)).mpr ⟨?_, ih h₂⟩
    intro y hy
    obtain ⟨z, hz, hzy⟩ := List.mem_map.mp hy
    rw [← hzy]
    exact ble_fst_of_prod_ble (h₁ z hz)

/-- Different tags make the tag order strict, so it cannot hold both ways. -/
theorem tagLe_not_both_of_snd_ne {proj : α → β} {a b : α × Nat} (hne : a.2 ≠ b.2) :
    ¬(KeyLe (tagProj proj) a b ∧ KeyLe (tagProj proj) b a) := by
  rintro ⟨h₁, h₂⟩
  rcases Cmp.prod_ble_iff.mp h₁ with hlt | ⟨heq, hle⟩
  · rcases Cmp.prod_ble_iff.mp h₂ with hlt' | ⟨heq', -⟩
    · exact absurd hlt' (by rw [Cmp.not_blt_of_blt hlt]; exact Bool.false_ne_true)
    · exact absurd (heq' ▸ hlt) (by simp [Cmp.blt_irrefl])
  · rcases Cmp.prod_ble_iff.mp h₂ with hlt' | ⟨-, hle'⟩
    · exact absurd (heq ▸ hlt') (by simp [Cmp.blt_irrefl])
    · exact hne (Nat.le_antisymm hle hle')

/-- Two lists that are permutations of each other and sorted by the same relation are
equal, provided the relation is antisymmetric on the members of the first list. -/
theorem eq_of_sorted_perm {γ : Type w} {r : γ → γ → Prop} {l₁ l₂ : List γ}
    (hanti : ∀ a ∈ l₁, ∀ b ∈ l₁, r a b → r b a → a = b)
    (h₁ : Sorted r l₁) (h₂ : Sorted r l₂) (hp : l₁.Perm l₂) : l₁ = l₂ := by
  revert hanti h₁ h₂ hp
  induction l₁ generalizing l₂ with
  | nil => intro _ _ _ hp; exact (hp.symm.eq_nil).symm
  | cons a t ih =>
    intro hanti h₁ h₂ hp
    cases l₂ with
    | nil => exact absurd hp.eq_nil (List.cons_ne_nil a t)
    | cons b u =>
      obtain ⟨h₁a, h₁t⟩ := (sorted_cons_iff r a t).mp h₁
      obtain ⟨h₂b, h₂u⟩ := (sorted_cons_iff r b u).mp h₂
      have ha : a ∈ b :: u := hp.subset (List.mem_cons.mpr (Or.inl rfl))
      have hb : b ∈ a :: t := hp.symm.subset (List.mem_cons.mpr (Or.inl rfl))
      have hab : a = b := by
        rcases List.mem_cons.mp ha with h | h
        · exact h
        · rcases List.mem_cons.mp hb with h' | h'
          · exact h'.symm
          · exact hanti a (List.mem_cons.mpr (Or.inl rfl)) b (List.mem_cons_of_mem a h')
              (h₁a b h') (h₂b a h)
      subst hab
      rw [ih (fun x hx y hy => hanti x (List.mem_cons_of_mem a hx) y
        (List.mem_cons_of_mem a hy)) h₁t h₂u hp.cons_inv]

/-! ## Filtering tagged lists by key -/

/-- Key-filtering commutes with erasing the tags. -/
theorem keyFilter_map_fst (proj : α → β) (k : β) (X : List (α × Nat)) :
    keyFilter proj k (X.map Prod.fst) =
      (keyFilter (fun p : α × Nat => proj p.1) k X).map Prod.fst := by
  simp only [keyFilter, List.filter_map]
  rfl

/-- Tags increase along a tagged list. -/
theorem tagFrom_sorted_snd (off : Nat) (l : List α) :
    Sorted (fun a b : α × Nat => a.2 ≤ b.2) (tagFrom off l) := by
  induction l generalizing off with
  | nil => exact sorted_nil _
  | cons x xs ih =>
    refine (sorted_cons_iff _ _ _).mpr ⟨?_, ih (off + 1)⟩
    intro y hy
    have h := (tagFrom_snd_lt (off + 1) hy).1
    omega

/-- A list with a fixed key whose tags increase is sorted under the tag order. -/
theorem sorted_tag_of_snd_le {proj : α → β} {k : β} {X : List (α × Nat)}
    (h : Sorted (fun a b : α × Nat => a.2 ≤ b.2) X) (hk : ∀ p ∈ X, proj p.1 = k) :
    Sorted (KeyLe (tagProj proj)) X := by
  induction X with
  | nil => exact sorted_nil _
  | cons a t ih =>
    obtain ⟨h₁, h₂⟩ := (sorted_cons_iff _ _ _).mp h
    refine (sorted_cons_iff _ _ _).mpr ⟨?_, ih h₂ (fun p hp => hk p (List.mem_cons_of_mem a hp))⟩
    intro y hy
    have ha := hk a (List.mem_cons.mpr (Or.inl rfl))
    have hyk := hk y (List.mem_cons_of_mem a hy)
    have hy2 := h₁ y hy
    show Cmp.ble (tagProj proj a) (tagProj proj y) = true
    simp only [tagProj]
    rw [ha, hyk]
    exact Cmp.prod_ble_iff.mpr (Or.inr ⟨rfl, hy2⟩)

/-- Within one key, the key-filter of a tagged list is sorted under the tag order. -/
theorem sorted_filter_tagFrom (proj : α → β) (off : Nat) (k : β) (l : List α) :
    Sorted (KeyLe (tagProj proj))
      ((tagFrom off l).filter fun p => Cmp.beq (proj p.1) k) := by
  refine sorted_tag_of_snd_le (k := k)
    ((tagFrom_sorted_snd off l).filter fun p : α × Nat => Cmp.beq (proj p.1) k) ?_
  intro p hp
  exact Cmp.beq_eq (List.mem_filter.mp hp).2

/-- Distinct tags survive a permutation. -/
theorem snd_inj_of_perm_tagFrom {X : List (α × Nat)} {l : List α} {off : Nat}
    (hp : X.Perm (tagFrom off l)) : ∀ a ∈ X, ∀ b ∈ X, a.2 = b.2 → a = b := by
  intro a ha b hb hab
  exact tagFrom_snd_inj off (hp.mem_iff.mp ha) (hp.mem_iff.mp hb) hab

/-! ## The block phase on tagged blocks -/

/-- The merge of two tagged runs: the C++ label comparison, as an order. -/
def mergeTag (proj : α → β) (A B : List (α × Nat)) : List (α × Nat) :=
  mergeTwo (tagProj proj) A B

/-- Merge the blocks left to right, folding the next block in each time. This is the
pairwise block merge: only the unfinished tail takes part in the next merge, and the
`take`/`drop` split it induces is invisible here because a merge writes a prefix of
its result and keeps the rest as the tail. -/
def seqMergeTag (proj : α → β) : List (List (α × Nat)) → List (α × Nat)
  | [] => []
  | b :: bs => bs.foldl (fun acc c => mergeTag proj acc c) b

theorem foldl_mergeTag_perm (proj : α → β) (bs : List (List (α × Nat)))
    (acc : List (α × Nat)) :
    (bs.foldl (fun acc c => mergeTag proj acc c) acc).Perm (acc ++ bs.flatten) := by
  induction bs generalizing acc with
  | nil => simp
  | cons c cs ih =>
    simp only [List.foldl_cons, List.flatten_cons]
    refine (ih (mergeTag proj acc c)).trans ?_
    simpa only [mergeTag, List.append_assoc] using
      List.Perm.append_right cs.flatten (mergeTwo_perm (tagProj proj) acc c)

theorem seqMergeTag_perm (proj : α → β) (blks : List (List (α × Nat))) :
    (seqMergeTag proj blks).Perm blks.flatten := by
  cases blks with
  | nil => simp [seqMergeTag]
  | cons b bs => simpa [seqMergeTag, List.flatten_cons] using foldl_mergeTag_perm proj bs b

theorem foldl_mergeTag_sorted (proj : α → β) (bs : List (List (α × Nat)))
    (acc : List (α × Nat)) (hacc : Sorted (KeyLe (tagProj proj)) acc)
    (hbs : ∀ b ∈ bs, Sorted (KeyLe (tagProj proj)) b) :
    Sorted (KeyLe (tagProj proj)) (bs.foldl (fun acc c => mergeTag proj acc c) acc) := by
  induction bs generalizing acc with
  | nil => exact hacc
  | cons c cs ih =>
    simp only [List.foldl_cons]
    exact ih (mergeTag proj acc c) (mergeTwo_sorted (tagProj proj) acc c hacc (hbs c (by simp)))
      (fun b hb => hbs b (by simp [hb]))

theorem seqMergeTag_sorted (proj : α → β) (blks : List (List (α × Nat)))
    (h : ∀ b ∈ blks, Sorted (KeyLe (tagProj proj)) b) :
    Sorted (KeyLe (tagProj proj)) (seqMergeTag proj blks) := by
  cases blks with
  | nil => exact sorted_nil _
  | cons b bs =>
    exact foldl_mergeTag_sorted proj bs b (h b (by simp)) (fun c hc => h c (by simp [hc]))

/-- The C++ block comparison: the first key, then the label. -/
def blkLe (proj : α → β) (a b : List (α × Nat)) : Bool :=
  match a.head?, b.head? with
  | some x, some y => Cmp.ble (tagProj proj x) (tagProj proj y)
  | none, _ => true
  | some _, none => false

/-- Insert a block into a block list ordered by `blkLe`. -/
def insertBlk (proj : α → β) (b : List (α × Nat)) :
    List (List (α × Nat)) → List (List (α × Nat))
  | [] => [b]
  | c :: cs => if blkLe proj b c then b :: c :: cs else c :: insertBlk proj b cs

/-- C++'s `block_selection_sort` as the equivalent insertion sort: order the blocks by
(first key, label). Only "the blocks are permuted and keep their elements" is used
below, since the data region does not depend on the block order. -/
def blkSortTag (proj : α → β) : List (List (α × Nat)) → List (List (α × Nat))
  | [] => []
  | b :: bs => insertBlk proj b (blkSortTag proj bs)

theorem insertBlk_flatten_perm (proj : α → β) (b : List (α × Nat))
    (r : List (List (α × Nat))) :
    (insertBlk proj b r).flatten.Perm (b ++ r.flatten) := by
  induction r with
  | nil => exact List.Perm.refl (b ++ ([] : List (List (α × Nat))).flatten)
  | cons c cs ih =>
    cases h : blkLe proj b c with
    | true => simp [insertBlk, h, List.flatten_cons]
    | false =>
      simp only [insertBlk, h, List.flatten_cons]
      refine (List.Perm.append_left c ih).trans ?_
      simpa only [List.append_assoc] using
        List.Perm.append_right cs.flatten (List.perm_append_comm (l₁ := c) (l₂ := b))

theorem blkSortTag_flatten_perm (proj : α → β) (blks : List (List (α × Nat))) :
    (blkSortTag proj blks).flatten.Perm blks.flatten := by
  induction blks with
  | nil => simp [blkSortTag]
  | cons b bs ih =>
    simp only [blkSortTag, List.flatten_cons]
    exact (insertBlk_flatten_perm proj b (blkSortTag proj bs)).trans
      (List.Perm.append_left b ih)

theorem insertBlk_all_sorted (proj : α → β) {b : List (α × Nat)}
    {r : List (List (α × Nat))} (hb : Sorted (KeyLe (tagProj proj)) b)
    (hr : ∀ c ∈ r, Sorted (KeyLe (tagProj proj)) c) :
    ∀ c ∈ insertBlk proj b r, Sorted (KeyLe (tagProj proj)) c := by
  induction r with
  | nil =>
    intro c hc
    have hcb : c = b := by simpa [insertBlk] using hc
    rw [hcb]
    exact hb
  | cons d ds ih =>
    cases h : blkLe proj b d with
    | true =>
      intro x hx
      simp only [insertBlk, h] at hx
      rcases List.mem_cons.mp hx with hxb | hx
      · rw [hxb]; exact hb
      rcases List.mem_cons.mp hx with hxd | hx
      · rw [hxd]; exact hr d (List.mem_cons.mpr (Or.inl rfl))
      · exact hr x (List.mem_cons.mpr (Or.inr hx))
    | false =>
      intro x hx
      simp only [insertBlk, h] at hx
      rcases List.mem_cons.mp hx with hxd | hx
      · rw [hxd]; exact hr d (List.mem_cons.mpr (Or.inl rfl))
      · exact ih (fun y hy => hr y (List.mem_cons.mpr (Or.inr hy))) x hx

theorem blkSortTag_all_sorted (proj : α → β) {blks : List (List (α × Nat))}
    (h : ∀ b ∈ blks, Sorted (KeyLe (tagProj proj)) b) :
    ∀ b ∈ blkSortTag proj blks, Sorted (KeyLe (tagProj proj)) b := by
  induction blks with
  | nil => intro b hb; simp [blkSortTag] at hb
  | cons c cs ih =>
    simp only [blkSortTag]
    exact insertBlk_all_sorted proj (h c (by simp))
      (fun b hb => ih (fun b hb' => h b (by simp [hb'])) b hb)

/-! ## The block phase's data region -/

/-- The data region the block phase produces: the `(key, tag)`-sorted merge of the
blocks, with the tags erased. -/
def blkPhaseData (proj : α → β) (blks : List (List (α × Nat))) : List α :=
  (seqMergeTag proj (blkSortTag proj blks)).map Prod.fst

/-- **The block phase, end to end.** If the tagged blocks partition a region whose
elements carry their positions, and every block is sorted under the tag order, then
the data region is key-sorted, a permutation of the region, and every equal-key
subsequence survives. -/
theorem blkPhaseData_spec (proj : α → β) {blks : List (List (α × Nat))} {l : List α}
    {off : Nat} (hperm : blks.flatten.Perm (tagFrom off l))
    (hsort : ∀ b ∈ blks, Sorted (KeyLe (tagProj proj)) b) :
    Sorted (KeyLe proj) (blkPhaseData proj blks) ∧
      (blkPhaseData proj blks).Perm l ∧
      ∀ k : β, keyFilter proj k (blkPhaseData proj blks) = keyFilter proj k l := by
  have hblks' : (blkSortTag proj blks).flatten.Perm (tagFrom off l) :=
    (blkSortTag_flatten_perm proj blks).trans hperm
  have hsort' : ∀ b ∈ blkSortTag proj blks, Sorted (KeyLe (tagProj proj)) b :=
    blkSortTag_all_sorted proj hsort
  have hXperm : (seqMergeTag proj (blkSortTag proj blks)).Perm (tagFrom off l) :=
    (seqMergeTag_perm proj _).trans hblks'
  have hXsort : Sorted (KeyLe (tagProj proj)) (seqMergeTag proj (blkSortTag proj blks)) :=
    seqMergeTag_sorted proj _ hsort'
  refine ⟨sorted_map_fst_of_sorted_tag hXsort, ?_, ?_⟩
  · exact (hXperm.map Prod.fst).trans (by rw [tagFrom_map_fst])
  · intro k
    have hF₁ : Sorted (KeyLe (tagProj proj))
        ((seqMergeTag proj (blkSortTag proj blks)).filter fun p => Cmp.beq (proj p.1) k) :=
      hXsort.filter _
    have hF₂ : Sorted (KeyLe (tagProj proj))
        ((tagFrom off l).filter fun p => Cmp.beq (proj p.1) k) :=
      sorted_filter_tagFrom proj off k l
    have hFperm : ((seqMergeTag proj (blkSortTag proj blks)).filter
        fun p => Cmp.beq (proj p.1) k).Perm
        ((tagFrom off l).filter fun p => Cmp.beq (proj p.1) k) :=
      hXperm.filter _
    have hinj := snd_inj_of_perm_tagFrom hXperm
    have hFeq : ((seqMergeTag proj (blkSortTag proj blks)).filter
        fun p => Cmp.beq (proj p.1) k) =
        ((tagFrom off l).filter fun p => Cmp.beq (proj p.1) k) :=
      eq_of_sorted_perm
        (fun a ha b hb h₁ h₂ => by
          by_cases hab : a.2 = b.2
          · exact hinj a ((List.mem_filter.mp ha).1) b ((List.mem_filter.mp hb).1) hab
          · exact absurd ⟨h₁, h₂⟩ (tagLe_not_both_of_snd_ne hab))
        hF₁ hF₂ hFperm
    calc keyFilter proj k (blkPhaseData proj blks)
        = (keyFilter (fun p : α × Nat => proj p.1) k
            (seqMergeTag proj (blkSortTag proj blks))).map Prod.fst :=
          keyFilter_map_fst proj k _
      _ = (keyFilter (fun p : α × Nat => proj p.1) k (tagFrom off l)).map Prod.fst := by
          simp only [keyFilter, hFeq]
      _ = keyFilter proj k ((tagFrom off l).map Prod.fst) :=
          (keyFilter_map_fst proj k (tagFrom off l)).symm
      _ = keyFilter proj k l := by rw [tagFrom_map_fst]

end Tcs
