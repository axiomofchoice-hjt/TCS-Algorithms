/-
  Selection theory: what it means for a position to hold the k-th smallest element.

  Rank is defined through counts rather than through a sorted reference list, so
  that it stays meaningful with duplicate keys: `IsKthSmallest proj l k x` says
  that at most `k` keys of `l` lie below `proj x`, and more than `k` lie at most
  `proj x`. Two elements of rank `k` in one list therefore have equal keys
  (`isKthSmallest_unique`) - which is exactly what the C++ test checks by sorting
  a copy and comparing keys at index `k`.

  The transfer lemmas are the ones a partition-based selection needs: a rank
  inside a prefix or suffix survives when everything next to it is entirely
  above or entirely below the element.
-/
import Tcs.Spec
import Tcs.Count

namespace Tcs

variable {α : Type u} {β : Type v} [Cmp β]

/-- Keys of `l` strictly below `proj x`. -/
abbrev belowCount (proj : α → β) (l : List α) (x : α) : Nat :=
  l.countP (fun y => Cmp.blt (proj y) (proj x))

/-- Keys of `l` at most `proj x`. -/
abbrev uptoCount (proj : α → β) (l : List α) (x : α) : Nat :=
  l.countP (fun y => Cmp.ble (proj y) (proj x))

/-- `x` has rank `k` in `l`: the duplicate-tolerant "`k`-th smallest key".
`abbrev` so that instance search can decide concrete instances for the checks. -/
abbrev IsKthSmallest (proj : α → β) (l : List α) (k : Nat) (x : α) : Prop :=
  belowCount proj l x ≤ k ∧ k < uptoCount proj l x

/-- `r` selects rank `k` of `l`: `r` permutes `l` and its element at index `k` has
rank `k`. The split form `xs ++ y :: ys` keeps `getElem` proof arguments out of
the statement. -/
def Selects (proj : α → β) (k : Nat) (l r : List α) : Prop :=
  r.Perm l ∧ ∃ xs ys y, r = xs ++ y :: ys ∧ xs.length = k ∧ IsKthSmallest proj r k y

/-! ## Rank transfer -/

/-- A rank in a prefix is a rank of the whole, when the suffix holds nothing
smaller. -/
theorem isKthSmallest_append_left {proj : α → β} {l₁ l₂ : List α} {k : Nat} {x : α}
    (h : IsKthSmallest proj l₁ k x) (h₂ : belowCount proj l₂ x = 0) :
    IsKthSmallest proj (l₁ ++ l₂) k x := by
  unfold IsKthSmallest belowCount uptoCount at *
  refine ⟨?_, ?_⟩ <;> rw [List.countP_append]
  · rw [h₂, Nat.add_zero]; exact h.1
  · omega

/-- A rank in a suffix shifts by the prefix length, when the prefix lies entirely
below the element. -/
theorem isKthSmallest_append_right {proj : α → β} {l₁ l₂ : List α} {k : Nat} {x : α}
    (h : IsKthSmallest proj l₂ k x) (h₁ : belowCount proj l₁ x = l₁.length) :
    IsKthSmallest proj (l₁ ++ l₂) (l₁.length + k) x := by
  unfold IsKthSmallest belowCount uptoCount at *
  have h₁' : l₁.countP (fun y => Cmp.ble (proj y) (proj x)) = l₁.length :=
    List.countP_eq_length.mpr fun y hy => Cmp.ble_of_blt ((List.countP_eq_length.mp h₁) y hy)
  refine ⟨?_, ?_⟩ <;> rw [List.countP_append]
  · rw [h₁]; omega
  · rw [h₁']; omega

/-- Rank transfers between elements with equal keys. -/
theorem isKthSmallest_of_beq {proj : α → β} {l : List α} {k : Nat} {x y : α}
    (h : IsKthSmallest proj l k x) (hxy : Cmp.beq (proj x) (proj y) = true) :
    IsKthSmallest proj l k y := by
  unfold IsKthSmallest belowCount uptoCount at *
  have hxy' : proj x = proj y := Cmp.beq_eq hxy
  refine ⟨?_, ?_⟩
  · rw [← hxy']; exact h.1
  · rw [← hxy']; exact h.2

/-- Rank determines the key: two elements of the same rank in one list have equal
keys. -/
theorem isKthSmallest_unique {proj : α → β} {l : List α} {k : Nat} {x y : α}
    (hx : IsKthSmallest proj l k x) (hy : IsKthSmallest proj l k y) :
    Cmp.beq (proj x) (proj y) = true := by
  have key : ∀ {a b : α}, Cmp.blt (proj a) (proj b) = true →
      l.countP (fun z => Cmp.ble (proj z) (proj a)) ≤
        l.countP (fun z => Cmp.blt (proj z) (proj b)) := by
    intro a b hab
    refine countP_le_of_imp (fun z hz => ?_) l
    exact Cmp.blt_of_ble_of_blt hz hab
  have hnot₁ : ¬Cmp.blt (proj x) (proj y) = true := by
    intro hab
    have h := key hab
    unfold IsKthSmallest belowCount uptoCount at hx hy
    omega
  have hnot₂ : ¬Cmp.blt (proj y) (proj x) = true := by
    intro hba
    have h := key hba
    unfold IsKthSmallest belowCount uptoCount at hx hy
    omega
  rcases Cmp.ble_total (proj x) (proj y) with h | h
  · by_cases h' : Cmp.ble (proj y) (proj x) = true
    · exact Cmp.beq_iff.mpr ⟨h, h'⟩
    · have h'' : Cmp.ble (proj y) (proj x) = false := by
        cases hb : Cmp.ble (proj y) (proj x) <;> simp_all
      exact absurd (Cmp.blt_of_ble_of_not_ble h h'') hnot₁
  · by_cases h' : Cmp.ble (proj x) (proj y) = true
    · exact Cmp.beq_iff.mpr ⟨h', h⟩
    · have h'' : Cmp.ble (proj x) (proj y) = false := by
        cases hb : Cmp.ble (proj x) (proj y) <;> simp_all
      exact absurd (Cmp.blt_of_ble_of_not_ble h h'') hnot₂

/-! ## Sorted lists carry the rank of each position -/

/-- Key comparison relation of a sorted list. -/
def KeyLe (proj : α → β) (a b : α) : Prop :=
  Cmp.ble (proj a) (proj b) = true

/-- In a sorted list nothing below `l[k]` sits at index `k` or later. -/
theorem belowCount_le_of_sorted {proj : α → β} {l : List α} {k : Nat}
    (hs : Sorted (KeyLe proj) l) (hk : k < l.length) : belowCount proj l (l[k]'hk) ≤ k := by
  induction k generalizing l with
  | zero =>
    cases l with
    | nil => simp at hk
    | cons a t =>
      have hz : (a :: t)[0]'hk = a := by simp
      rw [hz]
      unfold belowCount
      rw [Nat.le_zero]
      refine countP_eq_zero_of_all ?_
      intro y hy
      rcases List.mem_cons.mp hy with hya | hy'
      · rw [hya]
        exact Cmp.blt_irrefl (proj a)
      · cases hb : Cmp.blt (proj y) (proj a) with
        | false => rfl
        | true =>
          have h₂ : Cmp.ble (proj a) (proj y) = true := List.rel_of_pairwise_cons hs hy'
          rw [Cmp.not_ble_of_blt hb] at h₂
          exact absurd h₂ (by simp)
  | succ k ih =>
    cases l with
    | nil => simp at hk
    | cons a t =>
      have hkt : k < t.length := by simpa using hk
      have hz : (a :: t)[k + 1]'hk = t[k]'hkt := by simp
      rw [hz]
      unfold belowCount
      rw [List.countP_cons]
      have ih' := ih (l := t) (List.Pairwise.of_cons hs) hkt
      have hif : (if Cmp.blt (proj a) (proj (t[k]'hkt)) then 1 else 0) ≤ 1 := by
        split <;> omega
      unfold belowCount at ih'
      omega

/-- In a sorted list every element up to index `k` is at most `l[k]`, so `l[k]`
has rank at most `k` from above. -/
theorem lt_uptoCount_of_sorted {proj : α → β} {l : List α} {k : Nat}
    (hs : Sorted (KeyLe proj) l) (hk : k < l.length) : k < uptoCount proj l (l[k]'hk) := by
  induction k generalizing l with
  | zero =>
    cases l with
    | nil => simp at hk
    | cons a t =>
      have hz : (a :: t)[0]'hk = a := by simp
      rw [hz]
      unfold uptoCount
      rw [List.countP_cons_of_pos (p := fun y => Cmp.ble (proj y) (proj a)) (a := a)
        (Cmp.ble_refl (proj a))]
      omega
  | succ k ih =>
    cases l with
    | nil => simp at hk
    | cons a t =>
      have hkt : k < t.length := by simpa using hk
      have hz : (a :: t)[k + 1]'hk = t[k]'hkt := by simp
      rw [hz]
      unfold uptoCount
      have ha : Cmp.ble (proj a) (proj (t[k]'hkt)) = true :=
        List.rel_of_pairwise_cons hs (List.getElem_mem hkt)
      rw [List.countP_cons_of_pos (p := fun y => Cmp.ble (proj y) (proj (t[k]'hkt))) (a := a) ha]
      have ih' := ih (l := t) (List.Pairwise.of_cons hs) hkt
      unfold uptoCount at ih'
      omega

/-- **Every position of a sorted list holds its own rank.** -/
theorem sorted_isKthSmallest {proj : α → β} {l : List α} {k : Nat}
    (hs : Sorted (KeyLe proj) l) (hk : k < l.length) :
    IsKthSmallest proj l k (l[k]'hk) :=
  ⟨belowCount_le_of_sorted hs hk, lt_uptoCount_of_sorted hs hk⟩

/-- A sorted permutation of `l` selects rank `k` of `l`. -/
theorem selects_of_sorted_perm {proj : α → β} {l r : List α} {k : Nat}
    (hperm : r.Perm l) (hs : Sorted (KeyLe proj) r) (hk : k < r.length) :
    Selects proj k l r := by
  refine ⟨hperm, r.take k, r.drop (k + 1), r[k]'hk, ?_, ?_, sorted_isKthSmallest hs hk⟩
  · rw [List.getElem_cons_drop hk]
    exact (List.take_append_drop k r).symm
  · rw [List.length_take]
    exact Nat.min_eq_left (Nat.le_of_lt hk)

/-! Concrete values, so a mis-stated definition cannot pass unnoticed. -/

example : IsKthSmallest (proj := fun n : Nat => n) [3, 1, 2] 0 1 := by decide

example : IsKthSmallest (proj := fun n : Nat => n) [3, 1, 2] 2 3 := by decide

example : ¬IsKthSmallest (proj := fun n : Nat => n) [3, 1, 2] 0 3 := by decide

/-- With duplicate keys every copy of the `k`-th smallest key has rank `k`. -/
example : IsKthSmallest (proj := fun n : Nat => n) [1, 1, 2] 1 1 := by decide

example : IsKthSmallest (proj := fun n : Nat => n) [1, 1, 2] 1 1 ∧
    IsKthSmallest (proj := fun n : Nat => n) [1, 1, 2] 1 1 :=
  ⟨by decide, by decide⟩

/-- A rank transfer end to end: `1` has rank `0` in `[1, 2, 3]` because the
suffix `[2, 3]` holds nothing below it. -/
example : IsKthSmallest (proj := fun n : Nat => n) [1, 2, 3] 0 1 :=
  isKthSmallest_append_left (l₁ := [1]) (l₂ := [2, 3])
    (k := 0) (x := 1)
    (by decide) (by decide)

end Tcs
