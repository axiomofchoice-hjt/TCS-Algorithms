/-
  The assembly of C++'s `inplace_stable_merge` (`include/tcs/inplace/stable_merge.hpp`,
  lines 241-292): the list-level model of the whole routine, both branches, and the
  proof that it meets `StableMergeSpec`.

  The model is the one validated against an exact index-level simulation of the C++:
  `stable_unique_limit` becomes `uniqueLimitRange`, `align_blocks_limit` becomes
  `alignBlocksLimit`, the labelled block phase becomes `blkPhaseData` on the tagged
  blocks of the aligned data region (the tags are absolute positions, so equal keys
  fall back to their input order), and the two finishing `inplace_merge_with_rotation`
  calls become `mergeByRotationStable`. The scratch/buffer region is modelled as
  unchanged by the block phase: the C++ only permutes it there, and both orders
  bubble-sort to the same result.

  This module only gathers what the lower layers already proved; the new work is the
  plumbing: tagged blocks, the internal structure of `align_blocks_limit`'s output
  (every `block_size`-block of the aligned prefix is internally sorted, and the tail
  is sorted), and the two finishing merges.
-/
import Tcs.StableBlock
import Tcs.StableMerge
import Tcs.UnstableMerge

namespace Tcs

variable {α : Type u} {β : Type v} [Cmp β]

/-! ## Tagged blocks

The block phase of the C++ works on `block_size`-sized blocks and labels them with
buffer values; the model labels every block with the absolute position of its first
element. `tagChunksAux` is `chunksAux` (the fuel-explicit block decomposition of the
data region) with the tags added; `taggedBlocks` cuts exactly `l.length / bs + 1`
blocks, enough to cover `l`. -/

/-- The tagged version of `chunksAux`: the first `fuel` successive `bs`-blocks of `l`,
each tagged from `off` on. -/
def tagChunksAux (bs : Nat) : Nat → Nat → List α → List (List (α × Nat))
  | 0, _, _ => []
  | _ + 1, _, [] => []
  | fuel + 1, off, l@(_ :: _) =>
      tagFrom off (l.take bs) ::
        tagChunksAux bs fuel (off + (l.take bs).length) (l.drop bs)

/-- Tag the blocks of `l`, using absolute positions starting at `off`. -/
def taggedBlocks (bs off : Nat) (l : List α) : List (List (α × Nat)) :=
  tagChunksAux bs (l.length / bs + 1) off l

/-- Tags are appended along an append. -/
theorem tagFrom_append (off : Nat) (x y : List α) :
    tagFrom off (x ++ y) = tagFrom off x ++ tagFrom (off + x.length) y := by
  induction x generalizing off with
  | nil => simp
  | cons a t ih =>
      show (a, off) :: tagFrom (off + 1) (t ++ y) =
        (a, off) :: (tagFrom (off + 1) t ++ tagFrom (off + (t.length + 1)) y)
      rw [ih (off + 1), show off + (t.length + 1) = off + 1 + t.length by omega]

/-- A key-sorted run, tagged with increasing positions, is sorted under the tag order. -/
theorem sorted_tagFrom_of_sorted {proj : α → β} (off : Nat) {l : List α}
    (h : Sorted (KeyLe proj) l) : Sorted (KeyLe (tagProj proj)) (tagFrom off l) := by
  induction l generalizing off with
  | nil => exact sorted_nil _
  | cons x xs ih =>
      rw [tagFrom_cons]
      obtain ⟨h₁, h₂⟩ := (sorted_cons_iff (KeyLe proj) x xs).mp h
      refine (sorted_cons_iff (KeyLe (tagProj proj)) (x, off) (tagFrom (off + 1) xs)).mpr
        ⟨?_, ih (off + 1) h₂⟩
      intro y hy
      have hy1 : y.1 ∈ xs := by
        have hm : y.1 ∈ (tagFrom (off + 1) xs).map Prod.fst :=
          List.mem_map.mpr ⟨y, hy, rfl⟩
        rwa [tagFrom_map_fst] at hm
      have hle := h₁ y.1 hy1
      have hoff := (tagFrom_snd_lt (off + 1) hy).1
      show Cmp.ble (tagProj proj (x, off)) (tagProj proj y) = true
      simp only [tagProj]
      change Cmp.ble (proj x) (proj y.1) = true at hle
      rw [Cmp.ble_eq_blt_or_beq] at hle
      rcases Bool.or_eq_true_iff.mp hle with hb | hb
      · exact Cmp.prod_ble_iff.mpr (Or.inl hb)
      · exact Cmp.prod_ble_iff.mpr (Or.inr ⟨Cmp.beq_eq hb, Nat.le_trans (Nat.le_succ off) hoff⟩)

/-- The tagged blocks concatenate back to the tagged range. -/
theorem tagChunksAux_flatten (bs off : Nat) : ∀ (fuel : Nat) (l : List α),
    (tagChunksAux bs fuel off l).flatten = tagFrom off (l.take (fuel * bs))
  | 0, l => by simp [tagChunksAux]
  | fuel + 1, [] => by simp [tagChunksAux]
  | fuel + 1, a :: t => by
      have htake : (a :: t).take ((fuel + 1) * bs) =
          (a :: t).take bs ++ ((a :: t).drop bs).take (fuel * bs) := by
        rw [show (fuel + 1) * bs = bs + fuel * bs by rw [Nat.succ_mul, Nat.add_comm]]
        rw [take_add']
      rw [tagChunksAux, List.flatten_cons, tagChunksAux_flatten bs _ fuel ((a :: t).drop bs),
        htake, tagFrom_append]

/-- Tagging the blocks of a region gives the tagged region. -/
theorem taggedBlocks_flatten {bs : Nat} (hbs : 0 < bs) (off : Nat) (l : List α) :
    (taggedBlocks bs off l).flatten = tagFrom off l := by
  unfold taggedBlocks
  rw [tagChunksAux_flatten]
  have hle : l.length ≤ (l.length / bs + 1) * bs := by
    calc l.length = bs * (l.length / bs) + l.length % bs := (Nat.div_add_mod l.length bs).symm
      _ ≤ bs * (l.length / bs) + bs := Nat.add_le_add_left (Nat.le_of_lt (Nat.mod_lt l.length hbs)) _
      _ = (l.length / bs + 1) * bs := by rw [Nat.mul_comm (l.length / bs + 1) bs, Nat.mul_succ]
  rw [List.take_of_length_le hle]

/-- Every tagged block of a key-sorted run is sorted under the tag order. -/
theorem tagChunksAux_all_sorted {proj : α → β} {bs : Nat} :
    ∀ (fuel off : Nat) (l : List α), Sorted (KeyLe proj) l →
      ∀ b ∈ tagChunksAux bs fuel off l, Sorted (KeyLe (tagProj proj)) b
  | 0, off, l, _, b, hb => by simp [tagChunksAux] at hb
  | fuel + 1, off, [], _, b, hb => by simp [tagChunksAux] at hb
  | fuel + 1, off, a :: t, hs, b, hb => by
      rw [tagChunksAux, List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact sorted_tagFrom_of_sorted off (sorted_take hs)
      · exact tagChunksAux_all_sorted fuel _ ((a :: t).drop bs) (sorted_drop hs) b hb

/-- The block decomposition is additive: `p` blocks of `X` and `q` of `Y` are the
`p + q` blocks of `X ++ Y` when `X` is exactly `p` blocks long. -/
theorem tagChunksAux_append_of_length {bs : Nat} (hbs : 0 < bs) :
    ∀ p q (off : Nat) (X Y : List α), X.length = p * bs →
      tagChunksAux bs (p + q) off (X ++ Y) =
        tagChunksAux bs p off X ++ tagChunksAux bs q (off + X.length) Y := by
  intro p
  induction p with
  | zero =>
      intro q off X Y hX
      have hXnil : X = [] := List.eq_nil_of_length_eq_zero (by simpa using hX)
      subst hXnil
      simp [tagChunksAux]
  | succ p ih =>
      intro q off X Y hX
      cases X with
      | nil =>
        rw [List.length_nil] at hX
        exact absurd (hX.symm ▸ Nat.mul_pos (Nat.succ_pos p) hbs) (Nat.lt_irrefl 0)
      | cons a t =>
        have hlen : bs ≤ (a :: t).length := by
          rw [hX, Nat.succ_mul]
          exact Nat.le_add_left bs (p * bs)
        have hdrop : ((a :: t).drop bs).length = p * bs := by
          rw [List.length_drop, hX, Nat.succ_mul, Nat.add_sub_cancel]
        have htake : (a :: (t ++ Y)).take bs = (a :: t).take bs := by
          rw [← List.cons_append]
          exact List.take_append_of_le_length hlen
        have hdropeq : (a :: (t ++ Y)).drop bs = (a :: t).drop bs ++ Y := by
          rw [← List.cons_append]
          exact List.drop_append_of_le_length hlen
        have hoffeq : off + ((a :: t).take bs).length + ((a :: t).drop bs).length =
            off + (a :: t).length := by
          rw [List.length_take, List.length_drop, Nat.min_eq_left hlen,
            Nat.add_assoc, Nat.add_sub_of_le hlen]
        rw [List.cons_append]
        simp only [Nat.succ_add, tagChunksAux.eq_3, htake, hdropeq]
        rw [ih q (off + ((a :: t).take bs).length) ((a :: t).drop bs) Y hdrop, hoffeq,
          List.cons_append]

/-! ## The structure of `align_blocks_limit`'s output

`alignBlocksLimit proj bs nb l 0 mid last` rounds the split down to `m := (mid / bs) * bs`,
merges the range `[m, last)` in place, and cuts the block region off after `l2 := bs * nb`.
When it does not have to over-shoot (`m ≤ l2`) the result is the first merge's output;
when it does (`l2 < m`) it merges again from `l2`. In both cases the region from `l2` on
is a suffix of a sorted `mergeTwo`, and every `bs`-block of the region before `l2` lies
inside one of the two sorted pieces the split at the `bs`-multiple `m` creates. -/

theorem alignBlocksLimit_fst_le (proj : α → β) {bs nb : Nat} {l : List α} {mid last : Nat}
    (hle : (mid / bs) * bs ≤ bs * nb) :
    (alignBlocksLimit proj bs nb l 0 mid last).1
      = mergeByRotationStable proj l ((mid / bs) * bs) mid last := by
  unfold alignBlocksLimit
  simp only [Nat.sub_zero, Nat.zero_add]
  rw [ite_eq_right (Nat.not_lt.mpr hle)]

theorem alignBlocksLimit_fst_gt (proj : α → β) {bs nb : Nat} {l : List α} {mid last : Nat}
    (hgt : bs * nb < (mid / bs) * bs) :
    (alignBlocksLimit proj bs nb l 0 mid last).1
      = mergeByRotationStable proj
          (mergeByRotationStable proj l ((mid / bs) * bs) mid last)
          (bs * nb) ((mid / bs) * bs) last := by
  unfold alignBlocksLimit
  simp only [Nat.sub_zero, Nat.zero_add]
  rw [ite_eq_left hgt]

/-- The non-overshooting case of `align_blocks_limit`: the region from `l2` on is a
suffix of the mergeTwo, and every `bs`-block before `l2` lies inside one of the two
sorted pieces the split at the `bs`-multiple `m` creates. -/
theorem alignLimit_le_tail_and_blocks (proj : α → β) {bs nb off mid last : Nat} {l : List α}
    (hbs : 0 < bs) (hmid_last : mid ≤ last) (hlen : last = l.length)
    (hle : (mid / bs) * bs ≤ bs * nb) (hl2 : bs * nb ≤ last)
    (hX : Sorted (KeyLe proj) (l.take ((mid / bs) * bs)))
    (hA : Sorted (KeyLe proj) ((l.drop ((mid / bs) * bs)).take (mid - (mid / bs) * bs)))
    (hB : Sorted (KeyLe proj) ((l.drop mid).take (last - mid))) :
    Sorted (KeyLe proj) ((alignBlocksLimit proj bs nb l 0 mid last).1.drop (bs * nb)) ∧
      (∀ b ∈ taggedBlocks bs off ((alignBlocksLimit proj bs nb l 0 mid last).1.take (bs * nb)),
        Sorted (KeyLe (tagProj proj)) b) := by
  have hm_mid : (mid / bs) * bs ≤ mid := Nat.div_mul_le_self mid bs
  have hlast_le : last ≤ l.length := Nat.le_of_eq hlen
  have hl : (mid / bs) * bs ≤ l.length := Nat.le_trans hm_mid (Nat.le_trans hmid_last hlast_le)
  generalize hM1 : mergeTwo proj ((l.drop ((mid / bs) * bs)).take (mid - (mid / bs) * bs))
      ((l.drop mid).take (last - mid)) = M1
  have hM1sort : Sorted (KeyLe proj) M1 := by
    rw [← hM1]; exact mergeTwo_sorted proj _ _ hA hB
  have hM1len : M1.length = last - (mid / bs) * bs := by
    rw [← hM1]; exact mergeTwo_pieces_length proj hm_mid hmid_last hlast_le
  have hdrop_last : l.drop last = [] := List.drop_eq_nil_of_le (Nat.le_of_eq hlen.symm)
  have hA1 : (alignBlocksLimit proj bs nb l 0 mid last).1 = l.take ((mid / bs) * bs) ++ M1 := by
    rw [alignBlocksLimit_fst_le proj hle,
      mergeByRotationStable_spec (proj := proj) (l := l) (first := (mid / bs) * bs)
        (mid := mid) (last := last) hA hB,
      hdrop_last, List.append_nil, hM1]
  have hlen_take : (l.take ((mid / bs) * bs)).length = (mid / bs) * bs := by
    rw [List.length_take]; exact Nat.min_eq_left hl
  have hdrop_take : (l.take ((mid / bs) * bs)).drop (bs * nb) = [] :=
    List.drop_eq_nil_of_le (by rw [hlen_take]; exact hle)
  have htail : (alignBlocksLimit proj bs nb l 0 mid last).1.drop (bs * nb) =
      M1.drop (bs * nb - (mid / bs) * bs) := by
    rw [hA1, List.drop_append, hdrop_take, List.nil_append, hlen_take]
  have hdata : (alignBlocksLimit proj bs nb l 0 mid last).1.take (bs * nb) =
      l.take ((mid / bs) * bs) ++ M1.take (bs * nb - (mid / bs) * bs) := by
    rw [hA1, List.take_append, hlen_take,
      List.take_of_length_le (l := l.take ((mid / bs) * bs)) (i := bs * nb) (by
        rw [List.length_take, Nat.min_eq_left hl]; exact hle)]
  refine ⟨?_, ?_⟩
  · rw [htail]; exact sorted_drop hM1sort
  · intro b hb
    rw [hdata] at hb
    have hle' : (mid / bs) * bs ≤ nb * bs := by rw [Nat.mul_comm nb bs]; exact hle
    have hp_nb : mid / bs ≤ nb := Nat.le_of_mul_le_mul_right hle' hbs
    have hp_le : mid / bs ≤ nb + 1 := Nat.le_succ_of_le hp_nb
    have hXYlen : (l.take ((mid / bs) * bs) ++ M1.take (bs * nb - (mid / bs) * bs)).length =
        bs * nb := by
      rw [List.length_append, hlen_take, List.length_take, hM1len,
        Nat.min_eq_left (Nat.sub_le_sub_right hl2 ((mid / bs) * bs)),
        Nat.add_sub_of_le hle]
    have hblocks : taggedBlocks bs off
        (l.take ((mid / bs) * bs) ++ M1.take (bs * nb - (mid / bs) * bs)) =
        tagChunksAux bs (mid / bs) off (l.take ((mid / bs) * bs)) ++
          tagChunksAux bs (nb + 1 - mid / bs) (off + (l.take ((mid / bs) * bs)).length)
            (M1.take (bs * nb - (mid / bs) * bs)) := by
      unfold taggedBlocks
      rw [hXYlen, Nat.mul_div_cancel_left nb hbs]
      have hdist := tagChunksAux_append_of_length hbs (mid / bs) (nb + 1 - mid / bs) off
        (l.take ((mid / bs) * bs)) (M1.take (bs * nb - (mid / bs) * bs)) hlen_take
      rwa [Nat.add_sub_of_le hp_le] at hdist
    rw [hblocks, List.mem_append] at hb
    rcases hb with hb | hb
    · exact tagChunksAux_all_sorted (mid / bs) off (l.take ((mid / bs) * bs)) hX b hb
    · exact tagChunksAux_all_sorted (nb + 1 - mid / bs)
        (off + (l.take ((mid / bs) * bs)).length) (M1.take (bs * nb - (mid / bs) * bs))
        (sorted_take hM1sort) b hb

/-- The overshooting case of `align_blocks_limit`: the second merge starts at `l2 < m`,
so the region before `l2` is a prefix of the (sorted) prefix of `l`, and the region
from `l2` on is the sorted `mergeTwo` of two sorted pieces. -/
theorem alignLimit_gt_tail_and_blocks (proj : α → β) {bs nb off mid last : Nat} {l : List α}
    (_hbs : 0 < bs) (hmid_last : mid ≤ last) (hlen : last = l.length)
    (hgt : bs * nb < (mid / bs) * bs) (hl2 : bs * nb ≤ last)
    (hX : Sorted (KeyLe proj) (l.take ((mid / bs) * bs)))
    (hA : Sorted (KeyLe proj) ((l.drop ((mid / bs) * bs)).take (mid - (mid / bs) * bs)))
    (hB : Sorted (KeyLe proj) ((l.drop mid).take (last - mid))) :
    Sorted (KeyLe proj) ((alignBlocksLimit proj bs nb l 0 mid last).1.drop (bs * nb)) ∧
      (∀ b ∈ taggedBlocks bs off ((alignBlocksLimit proj bs nb l 0 mid last).1.take (bs * nb)),
        Sorted (KeyLe (tagProj proj)) b) := by
  have hm_mid : (mid / bs) * bs ≤ mid := Nat.div_mul_le_self mid bs
  have hlast_le : last ≤ l.length := Nat.le_of_eq hlen
  have hl : (mid / bs) * bs ≤ l.length := Nat.le_trans hm_mid (Nat.le_trans hmid_last hlast_le)
  have hl2_m : bs * nb ≤ (mid / bs) * bs := Nat.le_of_lt hgt
  generalize hl1 : mergeByRotationStable proj l ((mid / bs) * bs) mid last = l1
  have hl1_take : l1.take ((mid / bs) * bs) = l.take ((mid / bs) * bs) := by
    rw [← hl1]; exact mergeByRotationStable_take_self proj hl hA hB
  have hl1_len : l1.length = l.length := by
    rw [← hl1]
    exact (perm_mergeByRotationStable (proj := proj) hm_mid hmid_last hA hB).length_eq
  have hl1_drop : (l1.drop ((mid / bs) * bs)).take (last - (mid / bs) * bs) =
      mergeTwo proj ((l.drop ((mid / bs) * bs)).take (mid - (mid / bs) * bs))
        ((l.drop mid).take (last - mid)) := by
    rw [← hl1]
    exact mergeByRotationStable_drop_self proj hm_mid hmid_last hlast_le hA hB
  have hpiece1 : Sorted (KeyLe proj)
      ((l1.drop (bs * nb)).take ((mid / bs) * bs - bs * nb)) := by
    rw [← drop_take' l1 (bs * nb) ((mid / bs) * bs), hl1_take]
    exact sorted_drop (n := bs * nb) hX
  have hpiece2 : Sorted (KeyLe proj)
      ((l1.drop ((mid / bs) * bs)).take (last - (mid / bs) * bs)) := by
    rw [hl1_drop]; exact mergeTwo_sorted proj _ _ hA hB
  generalize hM2 : mergeTwo proj ((l1.drop (bs * nb)).take ((mid / bs) * bs - bs * nb))
      ((l1.drop ((mid / bs) * bs)).take (last - (mid / bs) * bs)) = M2
  have hM2sort : Sorted (KeyLe proj) M2 := by
    rw [← hM2]; exact mergeTwo_sorted proj _ _ hpiece1 hpiece2
  have hM2len : M2.length = last - bs * nb := by
    rw [← hM2]
    exact mergeTwo_pieces_length (proj := proj) (l := l1) (m := bs * nb)
      (mid := (mid / bs) * bs) (last := last) hl2_m (Nat.le_trans hm_mid hmid_last)
      (by rw [hl1_len]; exact hlast_le)
  have hdrop_last1 : l1.drop last = [] :=
    List.drop_eq_nil_of_le (by rw [hl1_len]; exact Nat.le_of_eq hlen.symm)
  have hA1 : (alignBlocksLimit proj bs nb l 0 mid last).1 = l1.take (bs * nb) ++ M2 := by
    rw [alignBlocksLimit_fst_gt proj hgt, hl1,
      mergeByRotationStable_spec (proj := proj) (l := l1) (first := bs * nb)
        (mid := (mid / bs) * bs) (last := last) hpiece1 hpiece2,
      hdrop_last1, List.append_nil, hM2]
  have hlen_take1 : (l1.take (bs * nb)).length = bs * nb := by
    rw [List.length_take, hl1_len]; exact Nat.min_eq_left (Nat.le_trans hl2 hlast_le)
  have htail : (alignBlocksLimit proj bs nb l 0 mid last).1.drop (bs * nb) = M2 := by
    rw [hA1, List.drop_append, hlen_take1,
      List.drop_eq_nil_of_le (Nat.le_of_eq hlen_take1), Nat.sub_self, List.drop_zero, List.nil_append]
  have hdata : (alignBlocksLimit proj bs nb l 0 mid last).1.take (bs * nb) = l1.take (bs * nb) := by
    rw [hA1, List.take_append, hlen_take1, Nat.sub_self, List.take_zero, List.append_nil,
      List.take_of_length_le (Nat.le_of_eq hlen_take1)]
  have hdata2 : l1.take (bs * nb) = l.take (bs * nb) := by
    calc l1.take (bs * nb) = (l1.take ((mid / bs) * bs)).take (bs * nb) := by
          rw [List.take_take, Nat.min_eq_left hl2_m]
      _ = (l.take ((mid / bs) * bs)).take (bs * nb) := by rw [hl1_take]
      _ = l.take (bs * nb) := by rw [List.take_take, Nat.min_eq_left hl2_m]
  have hdataX : (l.take ((mid / bs) * bs)).take (bs * nb) = l.take (bs * nb) := by
    rw [List.take_take, Nat.min_eq_left hl2_m]
  have hdata_sorted : Sorted (KeyLe proj) (l.take (bs * nb)) :=
    hdataX ▸ sorted_take (n := bs * nb) hX
  refine ⟨?_, ?_⟩
  · rw [htail]; exact hM2sort
  · intro b hb
    rw [hdata, hdata2] at hb
    unfold taggedBlocks at hb
    exact tagChunksAux_all_sorted _ off (l.take (bs * nb)) hdata_sorted b hb

/-! ## The two finishing merges

After the block phase the list is `br ++ sd ++ tail` with `br` the bubble-sorted buffer,
`sd` the sorted data region and `tail` the (sorted) rest. The C++ merges `br` with `sd`
and then that with `tail`; the result is the stable merge `mergeTwo (mergeTwo br sd) tail`. -/

theorem rotationMergeAssembly_eq (proj : α → β) {A B C : List α}
    (hA : Sorted (KeyLe proj) A) (hB : Sorted (KeyLe proj) B) (hC : Sorted (KeyLe proj) C) :
    mergeByRotationStable proj
        (mergeByRotationStable proj (A ++ B ++ C) 0 A.length (A.length + B.length))
        0 (A.length + B.length)
        (mergeByRotationStable proj (A ++ B ++ C) 0 A.length (A.length + B.length)).length
      = mergeTwo proj (mergeTwo proj A B) C := by
  have h1 : (A ++ B ++ C).take A.length = A := by
    rw [List.take_append_of_le_length (by simp), List.take_append_length]
  have h2 : (A ++ B ++ C).drop A.length = B ++ C := by
    rw [List.drop_append_of_le_length (by simp), List.drop_append_length]
  have h3 : (A ++ B ++ C).drop (A.length + B.length) = C := by
    rw [show A.length + B.length = (A ++ B).length by rw [List.length_append],
      List.drop_append_length]
  have hm1 : mergeByRotationStable proj (A ++ B ++ C) 0 A.length (A.length + B.length)
      = mergeTwo proj A B ++ C := by
    rw [mergeByRotationStable_spec (proj := proj) (l := A ++ B ++ C) (first := 0)
      (mid := A.length) (last := A.length + B.length)
      (by rw [List.drop_zero, Nat.sub_zero, h1]; exact hA)
      (by rw [h2, Nat.add_sub_cancel_left, List.take_append_length]; exact hB),
      List.take_zero, List.drop_zero, Nat.sub_zero, h1, Nat.add_sub_cancel_left, h2,
      List.take_append_length, h3, List.nil_append]
  rw [hm1]
  have hidx : (mergeTwo proj A B ++ C).length - (A.length + B.length) = C.length := by
    rw [List.length_append, mergeTwo_length, Nat.add_sub_cancel_left]
  have hdrop : (mergeTwo proj A B ++ C).drop (A.length + B.length) = C := by
    rw [show A.length + B.length = (mergeTwo proj A B).length by rw [mergeTwo_length],
      List.drop_append_length]
  have htake : (mergeTwo proj A B ++ C).take (A.length + B.length) = mergeTwo proj A B := by
    rw [List.take_append_of_le_length (Nat.le_of_eq (mergeTwo_length proj A B).symm),
      List.take_of_length_le (Nat.le_of_eq (mergeTwo_length proj A B))]
  rw [mergeByRotationStable_spec (proj := proj) (l := mergeTwo proj A B ++ C) (first := 0)
    (mid := A.length + B.length) (last := (mergeTwo proj A B ++ C).length)
    (by rw [List.drop_zero, Nat.sub_zero, htake]; exact mergeTwo_sorted proj A B hA hB)
    (by rw [hdrop, hidx, List.take_of_length_le (Nat.le_refl _)]; exact hC),
    List.take_zero, List.drop_zero, Nat.sub_zero, htake, hdrop, hidx,
    List.take_of_length_le (Nat.le_refl _),
    List.drop_eq_nil_of_le (Nat.le_refl _), List.nil_append, List.append_nil]

/-- **The two finishing merges meet the stable-merge specification.** -/
theorem rotationMergeAssembly (proj : α → β) {A B C : List α}
    (hA : Sorted (KeyLe proj) A) (hB : Sorted (KeyLe proj) B) (hC : Sorted (KeyLe proj) C) :
    Sorted (KeyLe proj)
        (mergeByRotationStable proj
          (mergeByRotationStable proj (A ++ B ++ C) 0 A.length (A.length + B.length))
          0 (A.length + B.length)
          (mergeByRotationStable proj (A ++ B ++ C) 0 A.length (A.length + B.length)).length) ∧
      (mergeByRotationStable proj
          (mergeByRotationStable proj (A ++ B ++ C) 0 A.length (A.length + B.length))
          0 (A.length + B.length)
          (mergeByRotationStable proj (A ++ B ++ C) 0 A.length (A.length + B.length)).length).Perm
        (A ++ B ++ C) ∧
      (∀ k : β, keyFilter proj k
        (mergeByRotationStable proj
          (mergeByRotationStable proj (A ++ B ++ C) 0 A.length (A.length + B.length))
          0 (A.length + B.length)
          (mergeByRotationStable proj (A ++ B ++ C) 0 A.length (A.length + B.length)).length) =
        keyFilter proj k (A ++ B ++ C)) := by
  rw [rotationMergeAssembly_eq proj hA hB hC]
  refine ⟨mergeTwo_sorted proj _ _ (mergeTwo_sorted proj A B hA hB) hC, ?_, ?_⟩
  · exact (mergeTwo_perm proj (mergeTwo proj A B) C).trans
      (List.Perm.append_right C (mergeTwo_perm proj A B))
  · intro k
    rw [mergeTwo_keyFilter proj k (mergeTwo proj A B) C (mergeTwo_sorted proj A B hA hB) hC,
      mergeTwo_keyFilter proj k A B hA hB, keyFilter_append, keyFilter_append]

/-! ## The model

The two branches share everything except the block size, the number of blocks and the
tag offset, so they are the same `stableMergePipeline`. `stableMerge` then only has to
choose the branch, exactly as the C++ does. -/

/-- The common body of both branches with the block size `bs`, `nb` blocks and buffer
size `off`: extract the buffer, align the blocks, run the labelled block phase on the
data region (the buffer is only permuted there), bubble-sort the buffer, and finish with
the two rotation merges. -/
def stableMergePipeline (proj : α → β) (bs nb off : Nat) (buf L' R' : List α) : List α :=
  let d := L' ++ R'
  let a := alignBlocksLimit proj bs nb d 0 L'.length d.length
  let data := a.1.take (bs * nb)
  let tail := a.1.drop (bs * nb)
  let sd := blkPhaseData proj (taggedBlocks bs off data)
  let br := bubbleSort proj buf
  let m1 := mergeByRotationStable proj (br ++ sd ++ tail) 0 br.length (br.length + sd.length)
  mergeByRotationStable proj m1 0 (br.length + sd.length) m1.length

/-- The double-buffer branch (`buffer_len = n_blocks + block_size`): `n_blocks` blocks of
the data region, `block_size` of the buffer's elements as the second half of the labels. -/
def stableMergeDouble (proj : α → β) (bs : Nat) (buf L' R' : List α) : List α :=
  stableMergePipeline proj bs ((L' ++ R').length / bs) buf.length buf L' R'

/-- The single-buffer branch: `buffer_len` blocks, the whole buffer as labels. -/
def stableMergeSingle (proj : α → β) (bs : Nat) (buf L' R' : List α) : List α :=
  stableMergePipeline proj bs buf.length buf.length buf L' R'

/-- C++'s `inplace_stable_merge` on a list: below 25 elements it bubble-sorts, otherwise
it runs `stable_unique_limit`, then the double- or single-buffer block pipeline. -/
def stableMerge (proj : α → β) (l : List α) (k : Nat) : List α :=
  if l.length ≤ 24 then bubbleSort proj l
  else
    let bs := Nat.sqrt l.length
    let r := uniqueLimitRange proj (l.length / bs + bs) (l.take k) (l.drop k)
    if r.1.length = l.length / bs + bs then
      stableMergeDouble proj bs r.1 r.2.1 r.2.2
    else
      stableMergeSingle proj ((l.length - r.1.length) / r.1.length) r.1 r.2.1 r.2.2

/-! ## Small helpers on the aligned region -/

theorem taggedBlocks_nil (bs off : Nat) : taggedBlocks bs off ([] : List α) = [] := by
  unfold taggedBlocks
  simp [tagChunksAux]

/-- The piece `[m, mid)` of `l₁ ++ l₂` is the piece `[m, mid)` of `l₁`. -/
theorem drop_take_drop_eq {l₁ l₂ : List α} {m mid : Nat} (hm : m ≤ l₁.length)
    (hmid : l₁.length = mid) :
    ((l₁ ++ l₂).drop m).take (mid - m) = l₁.drop m := by
  rw [List.drop_append_of_le_length hm,
    show mid - m = (l₁.drop m).length by rw [List.length_drop, hmid],
    List.take_append_length]

/-- With a zero block size `align_blocks_limit` just merges the two runs: `m = l2 = 0`,
so the region before `l2` is empty and the region from `l2` on is the whole first merge. -/
theorem alignBlocksLimit_zero_fst (proj : α → β) {nb : Nat} {L' R : List α}
    (hL' : Sorted (KeyLe proj) L') (hR : Sorted (KeyLe proj) R) :
    (alignBlocksLimit proj 0 nb (L' ++ R) 0 L'.length (L' ++ R).length).1 =
      mergeTwo proj L' R := by
  rw [alignBlocksLimit_fst_le (proj := proj) (bs := 0) (nb := nb) (l := L' ++ R)
      (mid := L'.length) (last := (L' ++ R).length) (by simp)]
  rw [Nat.div_zero, Nat.zero_mul]
  rw [mergeByRotationStable_spec (proj := proj) (l := L' ++ R) (first := 0)
      (mid := L'.length) (last := (L' ++ R).length)
      (by rw [List.drop_zero, Nat.sub_zero, List.take_append_length]; exact hL')
      (by rw [List.drop_left, List.length_append, Nat.add_sub_cancel_left, List.take_length];
          exact hR),
    List.take_zero, List.drop_zero, Nat.sub_zero,
    List.take_append_length, List.drop_left, List.length_append, Nat.add_sub_cancel_left,
    List.take_length]
  rw [← List.length_append, List.drop_eq_nil_of_le (Nat.le_refl _), List.nil_append,
    List.append_nil]

/-! ## The pipeline is a stable sort of `buf ++ L' ++ R'` -/

theorem stableMergePipeline_stableSort (proj : α → β) {bs nb off : Nat} {buf L' R' : List α}
    (hL' : Sorted (KeyLe proj) L') (hR' : Sorted (KeyLe proj) R')
    (hl2 : bs * nb ≤ (L' ++ R').length) :
    StableSort proj (buf ++ L' ++ R') (stableMergePipeline proj bs nb off buf L' R') := by
  simp only [stableMergePipeline]
  generalize ha : alignBlocksLimit proj bs nb (L' ++ R') 0 L'.length (L' ++ R').length = a
  generalize hdata : a.1.take (bs * nb) = data
  generalize htail : a.1.drop (bs * nb) = tail
  generalize hsd : blkPhaseData proj (taggedBlocks bs off data) = sd
  generalize hbr : bubbleSort proj buf = br
  generalize hm1 : mergeByRotationStable proj (br ++ sd ++ tail) 0 br.length
      (br.length + sd.length) = m1
  have hmid_last : L'.length ≤ (L' ++ R').length := by
    rw [List.length_append]; exact Nat.le_add_right _ _
  have hA1 : Sorted (KeyLe proj) (((L' ++ R').drop 0).take (L'.length - 0)) := by
    rw [List.drop_zero, Nat.sub_zero, List.take_append_length]; exact hL'
  have hB1 : Sorted (KeyLe proj)
      (((L' ++ R').drop L'.length).take ((L' ++ R').length - L'.length)) := by
    rw [List.drop_left, List.length_append, Nat.add_sub_cancel_left, List.take_length]
    exact hR'
  have hX0 : Sorted (KeyLe proj) ((L' ++ R').take ((L'.length / bs) * bs)) := by
    rw [List.take_append_of_le_length (Nat.div_mul_le_self L'.length bs)]
    exact sorted_take hL'
  have hA0 : Sorted (KeyLe proj)
      (((L' ++ R').drop ((L'.length / bs) * bs)).take (L'.length - (L'.length / bs) * bs)) := by
    rw [drop_take_drop_eq (l₁ := L') (l₂ := R') (m := (L'.length / bs) * bs)
      (mid := L'.length) (Nat.div_mul_le_self _ _) rfl]
    exact sorted_drop hL'
  have hB0 : Sorted (KeyLe proj)
      (((L' ++ R').drop L'.length).take ((L' ++ R').length - L'.length)) := hB1
  have ha_perm : a.1.Perm (L' ++ R') := by
    rw [← ha]
    exact alignBlocksLimit_perm (proj := proj) (bs := bs) (nb := nb) (l := L' ++ R')
      (first := 0) (mid := L'.length) (last := (L' ++ R').length)
      (Nat.zero_le _) hmid_last (Nat.le_refl _) hA1 hB1
  have ha_kf : ∀ k : β, keyFilter proj k a.1 = keyFilter proj k (L' ++ R') := by
    intro k
    rw [← ha]
    exact alignBlocksLimit_keyFilter (proj := proj) (bs := bs) (nb := nb) (l := L' ++ R')
      (first := 0) (mid := L'.length) (last := (L' ++ R').length)
      (Nat.zero_le _) hmid_last (Nat.le_refl _) hA1 hB1 k
  have hdata_tail : data ++ tail = a.1 := by rw [← hdata, ← htail, List.take_append_drop]
  -- the tail of the aligned region is sorted
  have htail_sorted : Sorted (KeyLe proj) tail := by
    rw [← htail, ← ha]
    by_cases hbs0 : bs = 0
    · rw [hbs0, Nat.zero_mul, List.drop_zero, alignBlocksLimit_zero_fst proj hL' hR']
      exact mergeTwo_sorted proj L' R' hL' hR'
    · have hbs : 0 < bs := Nat.pos_of_ne_zero hbs0
      by_cases hle : (L'.length / bs) * bs ≤ bs * nb
      · exact (alignLimit_le_tail_and_blocks (off := off) proj hbs hmid_last rfl hle hl2 hX0 hA0 hB0).1
      · exact (alignLimit_gt_tail_and_blocks (off := off) proj hbs hmid_last rfl (Nat.lt_of_not_le hle)
          hl2 hX0 hA0 hB0).1
  -- every tagged block of the data region is sorted
  have hsort : ∀ b ∈ taggedBlocks bs off data, Sorted (KeyLe (tagProj proj)) b := by
    have hsortA : ∀ b ∈ taggedBlocks bs off
        ((alignBlocksLimit proj bs nb (L' ++ R') 0 L'.length (L' ++ R').length).1.take
          (bs * nb)), Sorted (KeyLe (tagProj proj)) b := by
      by_cases hbs0 : bs = 0
      · intro b hb
        rw [hbs0, Nat.zero_mul, List.take_zero, taggedBlocks_nil] at hb
        simp at hb
      · have hbs : 0 < bs := Nat.pos_of_ne_zero hbs0
        intro b hb
        by_cases hle : (L'.length / bs) * bs ≤ bs * nb
        · exact (alignLimit_le_tail_and_blocks (off := off) proj hbs hmid_last rfl hle hl2 hX0 hA0 hB0).2 b hb
        · exact (alignLimit_gt_tail_and_blocks (off := off) proj hbs hmid_last rfl (Nat.lt_of_not_le hle)
            hl2 hX0 hA0 hB0).2 b hb
    intro b hb
    rw [← hdata, ← ha] at hb
    exact hsortA b hb
  have hperm : (taggedBlocks bs off data).flatten.Perm (tagFrom off data) := by
    by_cases hbs0 : bs = 0
    · have hd0 : data = [] := by rw [← hdata, hbs0, Nat.zero_mul, List.take_zero]
      rw [hd0, taggedBlocks_nil]
      exact List.Perm.refl []
    · exact List.Perm.of_eq (taggedBlocks_flatten (Nat.pos_of_ne_zero hbs0) off data)
  have hsd_spec := blkPhaseData_spec proj (off := off) (l := data) hperm hsort
  have hsd_sorted : Sorted (KeyLe proj) sd := by rw [← hsd]; exact hsd_spec.1
  have hsd_perm : sd.Perm data := by rw [← hsd]; exact hsd_spec.2.1
  have hsd_kf : ∀ k : β, keyFilter proj k sd = keyFilter proj k data := by
    intro k; rw [← hsd]; exact hsd_spec.2.2 k
  have hbr_spec := bubbleSort_stableSort proj buf
  have hbr_sorted : Sorted (KeyLe proj) br := by rw [← hbr]; exact hbr_spec.1
  have hbr_perm : br.Perm buf := by rw [← hbr]; exact hbr_spec.2.1
  have hbr_kf : ∀ k : β, keyFilter proj k br = keyFilter proj k buf := by
    intro k; rw [← hbr]; exact hbr_spec.2.2 k
  have hend := rotationMergeAssembly proj hbr_sorted hsd_sorted htail_sorted
  refine ⟨?_, ?_, ?_⟩
  · rw [← hm1]; exact hend.1
  · rw [← hm1]
    refine hend.2.1.trans ?_
    have hp1 : (br ++ sd ++ tail).Perm (buf ++ data ++ tail) :=
      List.Perm.append_right tail
        ((List.Perm.append_right sd hbr_perm).trans (List.Perm.append_left buf hsd_perm))
    have hp2 : (buf ++ data ++ tail).Perm (buf ++ L' ++ R') := by
      rw [List.append_assoc, hdata_tail, List.append_assoc]
      exact List.Perm.append_left buf ha_perm
    exact hp1.trans hp2
  · intro k
    rw [← hm1, hend.2.2 k]
    calc keyFilter proj k (br ++ sd ++ tail)
        = keyFilter proj k br ++ keyFilter proj k sd ++ keyFilter proj k tail := by
          rw [keyFilter_append, keyFilter_append, List.append_assoc]
      _ = keyFilter proj k buf ++ keyFilter proj k data ++ keyFilter proj k tail := by
          rw [hbr_kf k, hsd_kf k]
      _ = keyFilter proj k buf ++ (keyFilter proj k data ++ keyFilter proj k tail) := by
          rw [List.append_assoc]
      _ = keyFilter proj k buf ++ keyFilter proj k (data ++ tail) := by rw [keyFilter_append]
      _ = keyFilter proj k buf ++ keyFilter proj k a.1 := by rw [hdata_tail]
      _ = keyFilter proj k buf ++ keyFilter proj k (L' ++ R') := by rw [ha_kf k]
      _ = keyFilter proj k (buf ++ L' ++ R') := by
          rw [keyFilter_append, keyFilter_append, keyFilter_append, List.append_assoc]

/-- The double-buffer branch is a stable sort of the whole extracted region. -/
theorem stableMergeDouble_stableSort (proj : α → β) (bs : Nat) (buf L' R' : List α)
    (hL' : Sorted (KeyLe proj) L') (hR' : Sorted (KeyLe proj) R') :
    StableSort proj (buf ++ L' ++ R') (stableMergeDouble proj bs buf L' R') := by
  unfold stableMergeDouble
  refine stableMergePipeline_stableSort proj hL' hR' ?_
  rw [Nat.mul_comm]
  exact Nat.div_mul_le_self _ _

/-- The single-buffer branch is a stable sort of the whole extracted region. -/
theorem stableMergeSingle_stableSort (proj : α → β) (bs : Nat) (buf L' R' : List α)
    (hL' : Sorted (KeyLe proj) L') (hR' : Sorted (KeyLe proj) R')
    (hbs : bs = (L' ++ R').length / buf.length) :
    StableSort proj (buf ++ L' ++ R') (stableMergeSingle proj bs buf L' R') := by
  subst hbs
  unfold stableMergeSingle
  exact stableMergePipeline_stableSort proj hL' hR' (Nat.div_mul_le_self _ _)

/-! ## The main theorem -/

/-- **The model of `inplace_stable_merge` stably merges the two runs.** The model works
on the concatenation `l = l.take k ++ l.drop k`; both branches meet `StableMergeSpec`
against the two runs. -/
theorem stableMerge_stableMergeSpec_gen (proj : α → β) (l : List α) (k : Nat)
    (_hk : k ≤ l.length) (hL : Sorted (KeyLe proj) (l.take k))
    (hR : Sorted (KeyLe proj) (l.drop k)) :
    StableMergeSpec proj (l.take k) (l.drop k) (stableMerge proj l k) := by
  by_cases hsmall : l.length ≤ 24
  · rw [stableMerge, ite_eq_left hsmall]
    obtain ⟨hs, hp, hkf⟩ := bubbleSort_stableSort proj l
    exact ⟨hs, hp.trans (List.Perm.of_eq (List.take_append_drop k l)).symm,
      fun t => by rw [hkf t, List.take_append_drop]⟩
  · rw [stableMerge, ite_eq_right hsmall]
    simp only []
    generalize hbs : Nat.sqrt l.length = bs
    generalize hmax : l.length / bs + bs = max
    generalize hr : uniqueLimitRange proj max (l.take k) (l.drop k) = r
    generalize hbuf : r.1 = buf
    generalize hL' : r.2.1 = L'
    generalize hR' : r.2.2 = R'
    have hspec := uniqueLimitRange_spec proj max hL hR
    rw [hr] at hspec
    have hL's : Sorted (KeyLe proj) L' := by rw [← hL']; exact hspec.2.2.1
    have hR's : Sorted (KeyLe proj) R' := by rw [← hR']; exact hspec.2.2.2.1
    have hlen : buf.length + (L' ++ R').length = l.length := by
      have hl := hspec.2.2.2.2.1.length_eq
      simpa [List.length_append, hbuf, hL', hR'] using hl
    have hperm : (buf ++ L' ++ R').Perm (l.take k ++ l.drop k) := by
      have hp := hspec.2.2.2.2.1
      rwa [hbuf, hL', hR'] at hp
    have hkf : ∀ t : β, keyFilter proj t (buf ++ L' ++ R') =
        keyFilter proj t (l.take k ++ l.drop k) := by
      intro t
      have hk' := hspec.2.2.2.2.2 t
      rwa [hbuf, hL', hR'] at hk'
    by_cases hdouble : buf.length = max
    · rw [ite_eq_left hdouble]
      have hb := stableMergeDouble_stableSort proj bs buf L' R' hL's hR's
      exact ⟨hb.1, hb.2.1.trans hperm, fun t => (hb.2.2 t).trans (hkf t)⟩
    · rw [ite_eq_right hdouble]
      have hbs' : (l.length - buf.length) / buf.length = (L' ++ R').length / buf.length := by
        rw [← hlen, Nat.add_sub_cancel_left]
      have hb := stableMergeSingle_stableSort proj ((l.length - buf.length) / buf.length)
        buf L' R' hL's hR's hbs'
      exact ⟨hb.1, hb.2.1.trans hperm, fun t => (hb.2.2 t).trans (hkf t)⟩

/-- **The model of `inplace_stable_merge` meets `StableMergeSpec`.** -/
theorem stableMerge_stableMergeSpec (proj : α → β) {L R : List α}
    (hL : Sorted (KeyLe proj) L) (hR : Sorted (KeyLe proj) R) :
    StableMergeSpec proj L R (stableMerge proj (L ++ R) L.length) := by
  have h := stableMerge_stableMergeSpec_gen proj (L ++ R) L.length (by simp)
    (by simpa using hL) (by simpa using hR)
  simpa using h

/-- The model computes the reference stable merge. -/
theorem stableMerge_eq_mergeTwo (proj : α → β) {L R : List α}
    (hL : Sorted (KeyLe proj) L) (hR : Sorted (KeyLe proj) R) :
    stableMerge proj (L ++ R) L.length = mergeTwo proj L R :=
  eq_mergeTwo_of_stableMergeSpec hL hR (stableMerge_stableMergeSpec proj hL hR)

/-! ## The `Array`-level statement -/

/-- The `Array`-level statement, matching the C++ signature
`inplace_stable_merge(first, mid, last)`: the array is stably merged. -/
def stableMergeArray (proj : α → β) (a : Array α) (mid : Nat) : Array α :=
  (stableMerge proj a.toList mid).toArray

theorem stableMergeArray_stableMergeSpec (proj : α → β) (a : Array α) {mid : Nat}
    (hmid : mid ≤ a.size) (hA : Sorted (KeyLe proj) (a.toList.take mid))
    (hB : Sorted (KeyLe proj) (a.toList.drop mid)) :
    StableMergeSpec proj (a.toList.take mid) (a.toList.drop mid)
      (stableMergeArray proj a mid).toList := by
  unfold stableMergeArray
  rw [List.toList_toArray]
  exact stableMerge_stableMergeSpec_gen proj a.toList mid (by simpa using hmid) hA hB

end Tcs
