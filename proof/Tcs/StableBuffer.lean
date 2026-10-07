/-
  Why the model is allowed to leave the buffer region alone.

  The C++ block phase permutes the buffer/scratch region - the label array and the
  internal buffer are swapped around as `merge_with_swap` runs - while the assembly's
  model of the block phase keeps that region unchanged and only re-sorts it
  afterwards. This module closes that gap: `stable_unique_limit` hands the block phase
  a buffer whose keys are pairwise different (`KeysNodup`, part of
  `uniqueLimitRange_spec`), and for such a list `bubble_sort` depends only on the
  multiset, so any permutation of the buffer sorts to the same list.
-/
import Tcs.StableBlock

namespace Tcs

variable {α : Type u} {β : Type v} [Cmp β]

/-- Pairwise different keys make the elements recoverable from their keys. -/
theorem eq_of_keysNodup {proj : α → β} {l : List α} (h : KeysNodup proj l) :
    ∀ a ∈ l, ∀ b ∈ l, proj a = proj b → a = b := by
  induction l with
  | nil => intro a ha; simp at ha
  | cons x xs ih =>
    rw [KeysNodup, List.pairwise_cons] at h
    intro a ha b hb hab
    rcases List.mem_cons.mp ha with hax | ha
    · rcases List.mem_cons.mp hb with hbx | hb
      · rw [hax, hbx]
      · have hbeq : Cmp.beq (proj x) (proj b) = true := by
          rw [← hax]
          exact Cmp.beq_iff.mpr ⟨Cmp.of_eq hab, Cmp.of_eq hab.symm⟩
        exact absurd hbeq (by rw [h.1 b hb]; exact Bool.false_ne_true)
    · rcases List.mem_cons.mp hb with hbx | hb
      · have hbeq : Cmp.beq (proj x) (proj a) = true := by
          rw [← hbx]
          exact Cmp.beq_iff.mpr ⟨Cmp.of_eq hab.symm, Cmp.of_eq hab⟩
        exact absurd hbeq (by rw [h.1 a ha]; exact Bool.false_ne_true)
      · exact ih h.2 a ha b hb hab

/-- **`bubble_sort` is insensitive to the order of a buffer with pairwise different
keys.** This is what lets the model of the block phase skip the permutation the C++
performs on the label/scratch region and re-sort it directly. -/
theorem bubbleSort_eq_of_perm_of_keysNodup (proj : α → β) {l l' : List α}
    (hp : l'.Perm l) (hnd : KeysNodup proj l) : bubbleSort proj l' = bubbleSort proj l := by
  have h1 : Sorted (KeyLe proj) (bubbleSort proj l') := bubbleSort_sorted proj l'
  have h2 : Sorted (KeyLe proj) (bubbleSort proj l) := bubbleSort_sorted proj l
  have hp' : (bubbleSort proj l').Perm (bubbleSort proj l) :=
    (bubbleSort_perm proj l').trans (hp.trans (bubbleSort_perm proj l).symm)
  refine eq_of_sorted_perm (fun a ha b hb hle₁ hle₂ => ?_) h1 h2 hp'
  exact eq_of_keysNodup hnd a (hp.mem_iff.mp ((bubbleSort_perm proj l').mem_iff.mp ha))
    b (hp.mem_iff.mp ((bubbleSort_perm proj l').mem_iff.mp hb)) (Cmp.ble_antisymm hle₁ hle₂)

end Tcs
