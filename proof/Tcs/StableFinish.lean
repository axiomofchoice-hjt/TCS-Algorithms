/-
  The finishing merges of C++'s `inplace_stable_merge`
  (`include/tcs/inplace/stable_merge.hpp` lines 275-277 and 286-288): the two calls

      inplace_merge_with_rotation(buf1, first, last, proj);
      first = buf1;
      inplace_merge_with_rotation(first, last, original_last, proj);

  which carry the sorted buffer region, the sorted block region and the untouched tail
  together. Both are `mergeByRotationStable`, and both `Sorted` hypotheses are regions
  the algorithm has already sorted; this module only does the index bookkeeping, so
  that the assembly can treat the whole tail of the routine as one rewrite to
  `mergeTwo (mergeTwo buf data) tail`.
-/
import Tcs.StableMerge

namespace Tcs

variable {α : Type u} {β : Type v} [Cmp β]

/-! ## Index normalisations of `br ++ sd ++ tail` -/

theorem take_br (br sd tail : List α) : (br ++ sd ++ tail).take br.length = br := by
  rw [List.append_assoc, List.take_left]

theorem drop_br (br sd tail : List α) : (br ++ sd ++ tail).drop br.length = sd ++ tail := by
  rw [List.append_assoc, List.drop_left]

theorem drop_br_sd (br sd tail : List α) :
    (br ++ sd ++ tail).drop (br.length + sd.length) = tail := by
  rw [List.append_assoc, ← List.drop_drop, List.drop_left, List.drop_left]

theorem take_drop_br (br sd tail : List α) :
    ((br ++ sd ++ tail).drop br.length).take (br.length + sd.length - br.length) = sd := by
  rw [drop_br, Nat.add_sub_cancel_left, List.take_left]

/-! ## The two finishing merges -/

/-- **First finishing merge**: with the buffer region `br`, the block region `sd` and the
tail `tail` laid out as `br ++ sd ++ tail`, merging `[0, br.length)` with
`[br.length, br.length + sd.length)` leaves `mergeTwo br sd ++ tail`. -/
theorem finishMerge_noTail (proj : α → β) {br sd tail : List α}
    (hbr : Sorted (KeyLe proj) br) (hsd : Sorted (KeyLe proj) sd) :
    mergeByRotationStable proj (br ++ sd ++ tail) 0 br.length (br.length + sd.length) =
      mergeTwo proj br sd ++ tail := by
  rw [mergeByRotationStable_spec (proj := proj) (hA := by simpa using hbr)
    (hB := by rw [take_drop_br]; exact hsd)]
  simp only [Nat.sub_zero, List.take_zero, List.drop_zero, List.nil_append]
  rw [take_br, take_drop_br, drop_br_sd]

/-- **Second finishing merge**: merging `[0, m)` with `[m, m1.length)` of a list whose
two pieces are sorted leaves the merge of the pieces. -/
theorem finishMerge_tail (proj : α → β) {m1 : List α} {m : Nat}
    (h1 : Sorted (KeyLe proj) (m1.take m)) (h2 : Sorted (KeyLe proj) (m1.drop m)) :
    mergeByRotationStable proj m1 0 m m1.length = mergeTwo proj (m1.take m) (m1.drop m) := by
  rw [mergeByRotationStable_spec (proj := proj) (hA := by simpa using h1)
    (hB := by rw [List.take_of_length_le (l := m1.drop m) (i := m1.length - m) (by simp)]; exact h2)]
  simp only [Nat.sub_zero, List.take_zero, List.drop_zero, List.nil_append]
  rw [List.take_of_length_le (l := m1.drop m) (i := m1.length - m) (by simp), List.drop_length,
    List.append_nil]

/-- **The whole tail of the routine**: after both finishing merges the range is
`mergeTwo (mergeTwo br sd) tail`. -/
theorem finishMerge_both (proj : α → β) {br sd tail : List α}
    (hbr : Sorted (KeyLe proj) br) (hsd : Sorted (KeyLe proj) sd)
    (htail : Sorted (KeyLe proj) tail) :
    mergeByRotationStable proj
        (mergeByRotationStable proj (br ++ sd ++ tail) 0 br.length (br.length + sd.length))
        0 (br.length + sd.length) (br.length + sd.length + tail.length) =
      mergeTwo proj (mergeTwo proj br sd) tail := by
  rw [finishMerge_noTail proj hbr hsd]
  have hlen : (mergeTwo proj br sd ++ tail).length = br.length + sd.length + tail.length := by
    rw [List.length_append, mergeTwo_length]
  have htake : (mergeTwo proj br sd ++ tail).take (br.length + sd.length) =
      mergeTwo proj br sd := by
    rw [← mergeTwo_length proj br sd, List.take_left]
  have hdrop : (mergeTwo proj br sd ++ tail).drop (br.length + sd.length) = tail := by
    rw [← mergeTwo_length proj br sd, List.drop_left]
  have hmain := finishMerge_tail proj (m1 := mergeTwo proj br sd ++ tail)
    (m := br.length + sd.length) (by rw [htake]; exact mergeTwo_sorted proj br sd hbr hsd)
    (by rw [hdrop]; exact htail)
  rw [htake, hdrop] at hmain
  rw [hlen] at hmain
  exact hmain

end Tcs
