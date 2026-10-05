/-
  In-place unstable merge (`include/tcs/inplace/unstable_merge.hpp`), proved correct.

  Modelling. The C++ routines walk a random-access range `[first, last)` and never
  read outside it, so the whole range is modelled as one list `l : List α` and the
  iterators become `Nat` indices into `l`. `std::swap` at positions `i`, `j` is
  `Tcs.Bfprt.swapAt`, which is the identity out of range and only permutes.
  `std::ranges::rotate(first, mid, last)` is a *left* rotation of that sub-range:
  `rotRange l first mid last` places `[mid, last)` in front of `[first, mid)`.

  What is proved, for both routines:
  * `merge_with_swap` writes the pure merge of the two runs into `[output, output +
    (last - first))` while swapping the displaced elements into the consumed run
    positions; the surrounding positions `[output, last)` are permuted and
    everything outside is untouched.
  * `inplace_merge_with_rotation` leaves `[first, last)` sorted and permuted, with
    the complement of that range positionally unchanged.

  Neither routine is stable, which is why the specs speak about keys (`KeyLe proj`)
  and list permutations rather than about labelled elements.
-/
import Tcs.Bfprt

namespace Tcs

variable {α : Type u} {β : Type v} [Cmp β]

/-! ## Rotations -/

/-- `std::ranges::rotate(first, first + k, last)` on a whole list: the left
rotation by `k` moves `[k, length)` in front of `[0, k)`. -/
def rot (l : List α) (k : Nat) : List α := l.drop k ++ l.take k

theorem rot_perm (l : List α) (k : Nat) : (rot l k).Perm l :=
  (List.perm_append_comm).trans (List.Perm.of_eq (List.take_append_drop k l))

theorem rot_length (l : List α) (k : Nat) : (rot l k).length = l.length :=
  (rot_perm l k).length_eq

theorem rot_zero (l : List α) : rot l 0 = l := by simp [rot]

/-- Rotating a concatenation at the join simply swaps the two halves. This is the
alignment step of `inplace_merge_with_rotation`: the block of right-run elements
below the current left-run element is rotated in front of that element. -/
theorem rot_concat (A B : List α) : rot (A ++ B) A.length = B ++ A := by
  rw [rot, List.drop_append_length, List.take_append_length]

/-- `std::ranges::rotate(first + lo, first + mid, first + hi)` inside a list: only
the sub-range `[lo, hi)` is touched, and it is rotated left by `mid - lo`. -/
def rotRange (l : List α) (lo mid hi : Nat) : List α :=
  l.take lo ++ (l.drop mid).take (hi - mid) ++ (l.drop lo).take (mid - lo) ++ l.drop hi

/-- The shape `rotRange` produces on an explicit four-block decomposition. -/
theorem rotRange_append (X A B Y : List α) :
    rotRange (X ++ A ++ B ++ Y) X.length (X.length + A.length)
      (X.length + A.length + B.length) = X ++ B ++ A ++ Y := by
  have h1 : (X ++ A ++ B ++ Y).take X.length = X := by
    rw [List.take_append_of_le_length (l₁ := (X ++ A) ++ B) (l₂ := Y) (i := X.length) (by simp),
      List.take_append_of_le_length (l₁ := X ++ A) (l₂ := B) (i := X.length) (by simp),
      List.take_append_length]
  have h2 : (X ++ A ++ B ++ Y).drop (X.length + A.length) = B ++ Y := by
    rw [← List.length_append (as := X) (bs := A)]
    rw [List.drop_append_of_le_length (l₁ := (X ++ A) ++ B) (l₂ := Y) (i := (X ++ A).length) (by simp),
      List.drop_append_length]
  have h3 : (X ++ A ++ B ++ Y).drop X.length = A ++ B ++ Y := by
    rw [List.drop_append_of_le_length (l₁ := (X ++ A) ++ B) (l₂ := Y) (i := X.length) (by simp),
      List.drop_append_of_le_length (l₁ := X ++ A) (l₂ := B) (i := X.length) (by simp),
      List.drop_append_length]
  have h4 : (X ++ A ++ B ++ Y).drop (X.length + A.length + B.length) = Y := by
    rw [← List.length_append (as := X) (bs := A), ← List.length_append (as := X ++ A) (bs := B)]
    rw [List.drop_append_length]
  have e1 : X.length + A.length + B.length - (X.length + A.length) = B.length := by omega
  have e2 : X.length + A.length - X.length = A.length := by omega
  unfold rotRange
  rw [h1, h2, h3, h4, e1, e2,
      List.take_append_length,
      List.take_append_of_le_length (l₁ := A ++ B) (l₂ := Y) (i := A.length) (by simp),
      List.take_append_length]

/-- Rotating with the split at the left end changes nothing. -/
theorem rotRange_self_left {l : List α} {lo hi : Nat} (hlo : lo ≤ hi) (_hlen : hi ≤ l.length) :
    rotRange l lo lo hi = l := by
  have h : (l.drop lo).take (hi - lo) ++ l.drop hi = l.drop lo := by
    have h1 : (l.drop lo).drop (hi - lo) = l.drop hi := by
      rw [List.drop_drop, Nat.add_sub_of_le hlo]
    rw [← h1]
    exact List.take_append_drop (hi - lo) (l.drop lo)
  unfold rotRange
  rw [Nat.sub_self, List.take_zero, List.append_nil, List.append_assoc, h, List.take_append_drop]

/-- Rotating with the split at the right end changes nothing. -/
theorem rotRange_self_right {l : List α} {lo hi : Nat} (hlo : lo ≤ hi) (_hlen : hi ≤ l.length) :
    rotRange l lo hi hi = l := by
  have h : (l.drop lo).take (hi - lo) ++ l.drop hi = l.drop lo := by
    have h1 : (l.drop lo).drop (hi - lo) = l.drop hi := by
      rw [List.drop_drop, Nat.add_sub_of_le hlo]
    rw [← h1]
    exact List.take_append_drop (hi - lo) (l.drop lo)
  unfold rotRange
  rw [Nat.sub_self, List.take_zero, List.append_nil, List.append_assoc, h,
    List.take_append_drop]

/-- Constructive replacement for core's `drop_take'`, whose proof uses
`Classical.choice`: dropping `i` from the first `j` elements is the same as taking
`j - i` after dropping `i`. -/
theorem drop_take' : ∀ (l : List α) (i j : Nat), (l.take j).drop i = (l.drop i).take (j - i)
  | [], _, _ => by simp
  | _ :: _, 0, _ => by simp
  | _ :: _, _ + 1, 0 => by simp
  | _ :: t, i + 1, j + 1 => by
      rw [List.take_succ_cons, List.drop_succ_cons, Nat.succ_sub_succ_eq_sub]
      exact drop_take' t i j

/-- Constructive replacement for core's `take_add'`. -/
theorem take_add' : ∀ (l : List α) (i j : Nat), l.take (i + j) = l.take i ++ (l.drop i).take j
  | [], _, _ => by simp
  | _ :: _, 0, _ => by simp
  | a :: t, i + 1, j => by
      rw [Nat.succ_add, List.take_succ_cons, List.take_succ_cons, List.drop_succ_cons,
        take_add' t i j, List.cons_append]

/-- The sub-range `[lo, hi)` splits at any intermediate index. -/
theorem take_range_split {l : List α} {lo mid hi : Nat} (hlo : lo ≤ mid) (hmid : mid ≤ hi) :
    (l.drop lo).take (hi - lo) =
      (l.drop lo).take (mid - lo) ++ (l.drop mid).take (hi - mid) := by
  have h : mid - lo + (hi - mid) = hi - lo := by omega
  rw [← h, take_add', List.drop_drop, Nat.add_sub_of_le hlo]

theorem rotRange_perm {l : List α} {lo mid hi : Nat} (hlo : lo ≤ mid) (hmid : mid ≤ hi)
    (_hlen : hi ≤ l.length) : (rotRange l lo mid hi).Perm l := by
  have hsplit : (l.drop lo).take (hi - lo) =
      (l.drop lo).take (mid - lo) ++ (l.drop mid).take (hi - mid) := take_range_split hlo hmid
  have hs : ((l.drop mid).take (hi - mid) ++ (l.drop lo).take (mid - lo)).Perm
      ((l.drop lo).take (hi - lo)) := by
    rw [hsplit]
    exact List.perm_append_comm
  have h := Bfprt.splice_perm (l := l)
    (s := (l.drop mid).take (hi - mid) ++ (l.drop lo).take (mid - lo))
    (n := lo) (m := hi - lo) hs
  have heq : lo + (hi - lo) = hi := by omega
  rw [heq] at h
  unfold rotRange
  refine (List.Perm.of_eq ?_).symm.trans h
  simp only [List.append_assoc]

theorem rotRange_length {l : List α} {lo mid hi : Nat} (hlo : lo ≤ mid) (hmid : mid ≤ hi)
    (hlen : hi ≤ l.length) : (rotRange l lo mid hi).length = l.length :=
  (rotRange_perm hlo hmid hlen).length_eq

/-! ## "Everything in the first list is at most everything in the second" -/

/-- Pointwise order between two list blocks, the side condition of sorted
concatenation. -/
def AllLe {α : Type u} (R : α → α → Prop) (xs ys : List α) : Prop :=
  ∀ x ∈ xs, ∀ y ∈ ys, R x y

theorem allLe_append_right {R : α → α → Prop} {xs ys zs : List α} :
    AllLe R xs (ys ++ zs) ↔ AllLe R xs ys ∧ AllLe R xs zs := by
  unfold AllLe
  constructor
  · intro h
    exact ⟨fun x hx y hy => h x hx y (List.mem_append_left _ hy),
      fun x hx y hy => h x hx y (List.mem_append_right _ hy)⟩
  · rintro ⟨h₁, h₂⟩ x hx y hy
    rcases List.mem_append.mp hy with hy' | hy'
    · exact h₁ x hx y hy'
    · exact h₂ x hx y hy'

theorem allLe_append_left {R : α → α → Prop} {xs ys zs : List α} :
    AllLe R (xs ++ ys) zs ↔ AllLe R xs zs ∧ AllLe R ys zs := by
  unfold AllLe
  constructor
  · intro h
    exact ⟨fun x hx y hy => h x (List.mem_append_left _ hx) y hy,
      fun x hx y hy => h x (List.mem_append_right _ hx) y hy⟩
  · rintro ⟨h₁, h₂⟩ x hx y hy
    rcases List.mem_append.mp hx with hx' | hx'
    · exact h₁ x hx' y hy
    · exact h₂ x hx' y hy

theorem allLe_cons_left {R : α → α → Prop} {x : α} {xs zs : List α} :
    AllLe R (x :: xs) zs ↔ (∀ y ∈ zs, R x y) ∧ AllLe R xs zs := by
  unfold AllLe
  constructor
  · intro h
    exact ⟨fun y hy => h x (List.mem_cons_self) y hy,
      fun z hz y hy => h z (List.mem_cons_of_mem _ hz) y hy⟩
  · rintro ⟨h₁, h₂⟩ z hz y hy
    rcases List.mem_cons.mp hz with rfl | hz'
    · exact h₁ y hy
    · exact h₂ z hz' y hy

theorem allLe_cons_right {R : α → α → Prop} {x : α} {ys zs : List α} :
    AllLe R ys (x :: zs) ↔ (∀ z ∈ ys, R z x) ∧ AllLe R ys zs := by
  unfold AllLe
  constructor
  · intro h
    exact ⟨fun z hz => h z hz x (List.mem_cons_self),
      fun z hz y hy => h z hz y (List.mem_cons_of_mem _ hy)⟩
  · rintro ⟨h₁, h₂⟩ z hz y hy
    rcases List.mem_cons.mp hy with rfl | hy'
    · exact h₁ z hz
    · exact h₂ z hz y hy'

theorem allLe_nil_left {R : α → α → Prop} {ys : List α} : AllLe R [] ys :=
  fun _ hx => absurd hx List.not_mem_nil

theorem allLe_nil_right {R : α → α → Prop} {xs : List α} : AllLe R xs [] :=
  fun _ _ _ hy => absurd hy List.not_mem_nil

theorem allLe_of_sorted_append {R : α → α → Prop} {xs ys : List α}
    (h : Sorted R (xs ++ ys)) : AllLe R xs ys := by
  unfold Sorted at h
  exact (List.pairwise_append.mp h).2.2

theorem sorted_append_iff {R : α → α → Prop} {xs ys : List α} :
    Sorted R (xs ++ ys) ↔ Sorted R xs ∧ Sorted R ys ∧ AllLe R xs ys := by
  unfold Sorted
  exact List.pairwise_append

theorem sorted_append {R : α → α → Prop} {xs ys : List α} (hx : Sorted R xs) (hy : Sorted R ys)
    (hxy : AllLe R xs ys) : Sorted R (xs ++ ys) :=
  sorted_append_iff.mpr ⟨hx, hy, hxy⟩

theorem sorted_of_sorted_append_left {R : α → α → Prop} {xs ys : List α}
    (h : Sorted R (xs ++ ys)) : Sorted R xs :=
  (sorted_append_iff.mp h).1

theorem sorted_of_sorted_append_right {R : α → α → Prop} {xs ys : List α}
    (h : Sorted R (xs ++ ys)) : Sorted R ys :=
  (sorted_append_iff.mp h).2.1

/-! ## Range predicates -/

/-- `[lo, hi)` is sorted (the C++ `std::ranges::is_sorted` check on that range). -/
def SortedOn (proj : α → β) (l : List α) (lo hi : Nat) : Prop :=
  Sorted (KeyLe proj) ((l.drop lo).take (hi - lo))

/-- Every element of `[lo, hi)` is at least `proj x`. -/
def LeOn (proj : α → β) (l : List α) (lo hi : Nat) (x : α) : Prop :=
  ∀ y ∈ (l.drop lo).take (hi - lo), KeyLe proj x y

/-! ## The pure two-run merge -/

/-- The pure merge of two lists, taking from the *left* on ties, mirroring the
`proj(*left) <= proj(*right)` test of the C++ loop. -/
def mergeTwo (proj : α → β) : List α → List α → List α
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys =>
      if Cmp.ble (proj x) (proj y) then x :: mergeTwo proj xs (y :: ys)
      else y :: mergeTwo proj (x :: xs) ys

theorem mergeTwo_nil_left (proj : α → β) (ys : List α) : mergeTwo proj [] ys = ys := by
  simp [mergeTwo]

theorem mergeTwo_nil_right (proj : α → β) (xs : List α) : mergeTwo proj xs [] = xs := by
  cases xs <;> simp [mergeTwo]

theorem mergeTwo_cons_cons_of_ble {proj : α → β} {x y : α} {xs ys : List α}
    (h : Cmp.ble (proj x) (proj y) = true) :
    mergeTwo proj (x :: xs) (y :: ys) = x :: mergeTwo proj xs (y :: ys) := by
  rw [mergeTwo.eq_3, ite_eq_left h]

theorem mergeTwo_cons_cons_of_not_ble {proj : α → β} {x y : α} {xs ys : List α}
    (h : Cmp.ble (proj x) (proj y) = false) :
    mergeTwo proj (x :: xs) (y :: ys) = y :: mergeTwo proj (x :: xs) ys := by
  rw [mergeTwo.eq_3, ite_eq_right (by rw [h]; exact Bool.false_ne_true)]

/-- Every element of a merge comes from one of the two inputs. -/
theorem mergeTwo_all (proj : α → β) {P : α → Prop} :
    ∀ xs ys : List α, (∀ z ∈ xs, P z) → (∀ z ∈ ys, P z) → ∀ z ∈ mergeTwo proj xs ys, P z := by
  intro xs ys
  induction xs, ys using mergeTwo.induct proj with
  | case1 ys => intro _ hy z hz; rw [mergeTwo_nil_left] at hz; exact hy z hz
  | case2 xs hne => intro hx _ z hz; rw [mergeTwo_nil_right] at hz; exact hx z hz
  | case3 x xs y ys h ih =>
    intro hx hy z hz
    rw [mergeTwo_cons_cons_of_ble h] at hz
    rcases List.mem_cons.mp hz with rfl | hz'
    · exact hx z (List.mem_cons_self)
    · exact ih (fun w hw => hx w (List.mem_cons_of_mem _ hw)) hy z hz'
  | case4 x xs y ys h ih =>
    intro hx hy z hz
    rw [mergeTwo_cons_cons_of_not_ble (by simpa using h)] at hz
    rcases List.mem_cons.mp hz with rfl | hz'
    · exact hy z (List.mem_cons_self)
    · exact ih hx (fun w hw => hy w (List.mem_cons_of_mem _ hw)) z hz'

theorem mergeTwo_allLe_right {proj : α → β} {R : α → α → Prop} {zs xs ys : List α}
    (hx : AllLe R zs xs) (hy : AllLe R zs ys) : AllLe R zs (mergeTwo proj xs ys) :=
  fun z hz w hw =>
    mergeTwo_all proj xs ys (fun w hw => hx z hz w hw) (fun w hw => hy z hz w hw) w hw

theorem mergeTwo_allLe_left {proj : α → β} {R : α → α → Prop} {xs ys zs : List α}
    (hx : AllLe R xs zs) (hy : AllLe R ys zs) : AllLe R (mergeTwo proj xs ys) zs :=
  fun w hw z hz =>
    mergeTwo_all proj xs ys (fun w hw => hx w hw z hz) (fun w hw => hy w hw z hz) w hw

theorem mergeTwo_sorted (proj : α → β) :
    ∀ xs ys : List α, Sorted (KeyLe proj) xs → Sorted (KeyLe proj) ys →
      Sorted (KeyLe proj) (mergeTwo proj xs ys) := by
  intro xs ys
  induction xs, ys using mergeTwo.induct proj with
  | case1 ys => intro _ hy; rwa [mergeTwo_nil_left]
  | case2 xs hne => intro hx _; rwa [mergeTwo_nil_right]
  | case3 x xs y ys h ih =>
    intro hx hy
    rw [mergeTwo_cons_cons_of_ble h]
    obtain ⟨hx', hxs⟩ := (sorted_cons_iff (KeyLe proj) x xs).mp hx
    obtain ⟨hy', hys⟩ := (sorted_cons_iff (KeyLe proj) y ys).mp hy
    have hxy : KeyLe proj x y := h
    refine (sorted_cons_iff (KeyLe proj) x (mergeTwo proj xs (y :: ys))).mpr ⟨?_, ih hxs hy⟩
    apply mergeTwo_all proj xs (y :: ys) (P := KeyLe proj x)
    · exact hx'
    · intro w hw
      rcases List.mem_cons.mp hw with rfl | hw'
      · exact hxy
      · exact Cmp.ble_trans hxy (hy' w hw')
  | case4 x xs y ys h ih =>
    intro hx hy
    rw [mergeTwo_cons_cons_of_not_ble (by simpa using h)]
    obtain ⟨hx', hxs⟩ := (sorted_cons_iff (KeyLe proj) x xs).mp hx
    obtain ⟨hy', hys⟩ := (sorted_cons_iff (KeyLe proj) y ys).mp hy
    have hyx : KeyLe proj y x := by
      rcases Cmp.ble_total (proj x) (proj y) with hxy | hyx
      · exact absurd hxy h
      · exact hyx
    refine (sorted_cons_iff (KeyLe proj) y (mergeTwo proj (x :: xs) ys)).mpr ⟨?_, ih hx hys⟩
    apply mergeTwo_all proj (x :: xs) ys (P := KeyLe proj y)
    · intro w hw
      rcases List.mem_cons.mp hw with rfl | hw'
      · exact hyx
      · exact Cmp.ble_trans hyx (hx' w hw')
    · exact hy'

/-! ## Generic list helpers -/

/-- A list splits at index `lo` into its prefix and the sub-range starting there. -/
theorem take_drop_splice {l : List α} {lo hi : Nat} (h : lo ≤ hi) :
    l = l.take lo ++ (l.drop lo).take (hi - lo) ++ l.drop hi := by
  have h1 : (l.drop lo).take (hi - lo) ++ l.drop hi = l.drop lo := by
    have h2 : (l.drop lo).drop (hi - lo) = l.drop hi := by
      rw [List.drop_drop, Nat.add_sub_of_le h]
    rw [← h2]
    exact List.take_append_drop (hi - lo) (l.drop lo)
  rw [List.append_assoc, h1, List.take_append_drop]

/-- Permutations of two lists glued between the same prefix and suffix cancel. -/
theorem perm_cancel_context {l₁ l₂ l₃ l₄ : List α}
    (h : List.Perm (l₁ ++ l₂ ++ l₃) (l₁ ++ l₄ ++ l₃)) : List.Perm l₂ l₄ := by
  rw [List.append_assoc l₁ l₂ l₃, List.append_assoc l₁ l₄ l₃] at h
  exact (List.perm_append_right_iff (l₁ := l₂) (l₂ := l₄) l₃).mp
    ((List.perm_append_left_iff (l₁ := l₂ ++ l₃) (l₂ := l₄ ++ l₃) l₁).mp h)

/-- A permutation that fixes the prefix before `lo` and the suffix from `hi` on
permutes the sub-range `[lo, hi)` too. -/
theorem perm_range_of_perm {l l' : List α} {lo hi : Nat} (hperm : List.Perm l' l)
    (hpre : l'.take lo = l.take lo) (hpost : l'.drop hi = l.drop hi) (h : lo ≤ hi) :
    List.Perm ((l'.drop lo).take (hi - lo)) ((l.drop lo).take (hi - lo)) := by
  have hs' : l' = l'.take lo ++ (l'.drop lo).take (hi - lo) ++ l'.drop hi :=
    take_drop_splice (l := l') h
  have hs : l = l.take lo ++ (l.drop lo).take (hi - lo) ++ l.drop hi :=
    take_drop_splice (l := l) h
  have h2 : List.Perm (l'.take lo ++ (l'.drop lo).take (hi - lo) ++ l'.drop hi)
      (l.take lo ++ (l.drop lo).take (hi - lo) ++ l.drop hi) :=
    ((List.Perm.of_eq hs').symm.trans hperm).trans (List.Perm.of_eq hs)
  rw [hpre, hpost] at h2
  exact perm_cancel_context h2

/-- A non-empty range `[lo, hi)` exposes the head element: it is `l[lo]` and the
rest of the range continues from `lo + 1`. -/
theorem exists_cons_drop_take {l : List α} {lo hi : Nat} (h : lo < hi) (hlen : hi ≤ l.length) :
    ∃ x xs, (l.drop lo).take (hi - lo) = x :: xs ∧ l[lo]? = some x ∧
      (l.drop (lo + 1)).take (hi - (lo + 1)) = xs := by
  have hne : (l.drop lo).take (hi - lo) ≠ [] := by
    intro hnil
    rcases (List.take_eq_nil_iff.mp hnil) with hz | hz
    · omega
    · have := List.drop_eq_nil_iff.mp hz
      omega
  obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil hne
  refine ⟨x, xs, hx, ?_, ?_⟩
  · have h0 : 0 < hi - lo := by omega
    have h1 : ((l.drop lo).take (hi - lo))[0]? = (l.drop lo)[0]? := by
      rw [List.getElem?_take, ite_eq_left h0]
    rw [hx] at h1
    rw [List.getElem?_drop, Nat.add_zero] at h1
    simpa using h1.symm
  · have h1 : ((l.drop lo).take (hi - lo)).drop 1 = xs := by rw [hx]; rfl
    rw [drop_take', List.drop_drop] at h1
    have e : hi - lo - 1 = hi - (lo + 1) := by omega
    rwa [e] at h1

namespace Bfprt

variable {α : Type u}

theorem swapAt_length (l : List α) (i j : Nat) : (swapAt l i j).length = l.length :=
  (swapAt_perm l i j).length_eq

theorem swapAt_self (l : List α) (i : Nat) : swapAt l i i = l := by
  unfold swapAt
  split
  · rename_i h
    rw [List.set_set, List.set_getElem_self h.1]
  · rfl

theorem swapAt_take_of_le {l : List α} {i j k : Nat} (hi : k ≤ i) (hj : k ≤ j) :
    (swapAt l i j).take k = l.take k := by
  unfold swapAt
  split
  · have h1 : ((l.take k).set i l[j]).length ≤ j := by
      rw [List.length_set, List.length_take]
      exact Nat.le_trans (Nat.min_le_left k l.length) hj
    have h2 : (l.take k).length ≤ i := by
      rw [List.length_take]
      exact Nat.le_trans (Nat.min_le_left k l.length) hi
    rw [List.take_set, List.take_set, List.set_eq_of_length_le (h := h1),
      List.set_eq_of_length_le (h := h2)]
  · rfl

theorem swapAt_drop_of_lt {l : List α} {i j k : Nat} (hi : i < k) (hj : j < k) :
    (swapAt l i j).drop k = l.drop k := by
  unfold swapAt
  split
  · rw [List.drop_set, ite_eq_left hj, List.drop_set, ite_eq_left hi]
  · rfl

theorem swapAt_take_succ_of_le {l : List α} {i j : Nat} (hij : i ≤ j) (hj : j < l.length) :
    (swapAt l i j).take (i + 1) = l.take i ++ [l[j]] := by
  rcases Nat.eq_or_lt_of_le hij with rfl | hlt
  · rw [swapAt_self, ← List.take_concat_get hj, List.concat_eq_append]
  · have hi : i < l.length := Nat.lt_trans hlt hj
    have hset : swapAt l i j = (l.set i l[j]).set j l[i] := by
      unfold swapAt
      rw [dite_eq_left (show i < l.length ∧ j < l.length from ⟨hi, hj⟩)]
    have hlt1 : i < (l.take (i + 1)).length := by
      rw [List.length_take]; omega
    have h1 : ((l.take (i + 1)).set i l[j]).length ≤ j := by
      rw [List.length_set, List.length_take]
      exact Nat.le_trans (Nat.min_le_left (i + 1) l.length) (by omega)
    rw [hset, List.take_set, List.take_set, List.set_eq_of_length_le (h := h1),
      List.set_eq_take_append_cons_drop (l := l.take (i + 1)) (i := i) (a := l[j]),
      ite_eq_left hlt1, List.take_take, Nat.min_eq_left (Nat.le_succ i),
      List.drop_eq_nil_of_le (by rw [List.length_take]; exact Nat.min_le_left _ _)]

/-- The finalized output prefix grows by exactly the swapped-in element. -/
theorem swapAt_drop_take_succ {l : List α} {o i j : Nat} (ho : o ≤ i) (hij : i ≤ j)
    (hj : j < l.length) :
    ((swapAt l i j).drop o).take (i + 1 - o) = (l.drop o).take (i - o) ++ [l[j]] := by
  have htake := swapAt_take_succ_of_le hij hj
  have hlen : o ≤ (l.take i).length := by
    rw [List.length_take]
    exact Nat.le_min.mpr ⟨ho, by omega⟩
  calc ((swapAt l i j).drop o).take (i + 1 - o)
      = ((swapAt l i j).take (i + 1)).drop o := by rw [drop_take']
    _ = (l.take i ++ [l[j]]).drop o := by rw [htake]
    _ = ((l.take i).drop o) ++ [l[j]] := by
          rw [List.drop_append_of_le_length (l₁ := l.take i) (l₂ := [l[j]]) (i := o) (h := hlen)]
    _ = (l.drop o).take (i - o) ++ [l[j]] := by rw [drop_take']

/-- A swap at a position `i < lo` with the other position beyond `[lo, lo + m)`
does not change that sub-range. -/
theorem swapAt_drop_take_of_lt_of_le {l : List α} {i j lo m : Nat} (hi : i < lo)
    (hj : lo + m ≤ j) : ((swapAt l i j).drop lo).take m = (l.drop lo).take m := by
  unfold swapAt
  split
  · have h1 : ((l.drop lo).take m).length ≤ j - lo := by
      rw [List.length_take]
      exact Nat.le_trans (Nat.min_le_left m (l.drop lo).length) (by omega)
    rw [List.drop_set, ite_eq_right (by omega), List.drop_set_of_lt hi, List.take_set,
      List.set_eq_of_length_le (h := h1)]
  · rfl

end Bfprt

variable {α : Type u} {β : Type v} [Cmp β]

/-! ## `merge_with_swap` -/

/-- The pure merge, given as an equation when the left run head is taken. -/
theorem mergeTwo_drop_left {proj : α → β} {Ar Br : List α} {x : α} {xs : List α}
    (hA : Ar = x :: xs)
    (hBr : Br = [] ∨ ∃ y ys, Br = y :: ys ∧ Cmp.ble (proj x) (proj y) = true) :
    mergeTwo proj Ar Br = x :: mergeTwo proj xs Br := by
  rcases hBr with rfl | ⟨y, ys, rfl, hble⟩
  · rw [hA, mergeTwo_nil_right, mergeTwo_nil_right]
  · rw [hA, mergeTwo_cons_cons_of_ble hble]

/-- The pure merge, given as an equation when the right run head is taken. -/
theorem mergeTwo_drop_right {proj : α → β} {Ar Br : List α} {y : α} {ys : List α}
    (hB : Br = y :: ys)
    (hAr : Ar = [] ∨ ∃ x xs, Ar = x :: xs ∧ Cmp.ble (proj x) (proj y) = false) :
    mergeTwo proj Ar Br = y :: mergeTwo proj Ar ys := by
  rcases hAr with rfl | ⟨x, xs, rfl, hble⟩
  · rw [hB, mergeTwo_nil_left, mergeTwo_nil_left]
  · rw [hB, mergeTwo_cons_cons_of_not_ble hble]

/-- C++'s `merge_with_swap`. The write pointer `out` starts at `output` and both
run cursors start at `first` and `mid`; every step moves one run cursor and `out`
by one, so `last - first` fuel is exactly enough. -/
def mergeSwapLoop (proj : α → β) : Nat → List α → Nat → Nat → Nat → Nat → Nat → List α
  | 0, l, _, _, _, _, _ => l
  | fuel + 1, l, out, left, mid, right, last =>
      if _ : left < mid ∨ right < last then
        if _ : right = last then
          if hl : left < l.length then
            mergeSwapLoop proj fuel (Bfprt.swapAt l out left) (out + 1) (left + 1) mid right last
          else l
        else
          if hl : left < l.length then
            if hr : right < l.length then
              if _ : left < mid ∧ Cmp.ble (proj l[left]) (proj l[right]) then
                mergeSwapLoop proj fuel (Bfprt.swapAt l out left) (out + 1) (left + 1) mid right last
              else
                mergeSwapLoop proj fuel (Bfprt.swapAt l out right) (out + 1) left mid (right + 1) last
            else l
          else l
      else l

/-- C++'s `merge_with_swap` on the whole list. -/
def mergeWithSwap (proj : α → β) (l : List α) (output first mid last : Nat) : List α :=
  mergeSwapLoop proj (last - first) l output first mid mid last

/-- Loop invariant of `merge_with_swap`. `A0`/`B0` are the two runs of the initial
list, `M = mergeTwo proj A0 B0` the pure merge. After `out - output` steps the
finalized output is `[output, out)`, the unconsumed runs sit at `[left, mid)` and
`[right, last)`, and the displaced elements fill the rest of the buffer. -/
structure MergeInv (proj : α → β) (l0 : List α) (output first mid last : Nat) (A0 B0 : List α)
    (l : List α) (out left right : Nat) : Prop where
  hbuffer : output + (last - mid) ≤ first
  hA0 : A0 = (l0.drop first).take (mid - first)
  hB0 : B0 = (l0.drop mid).take (last - mid)
  merge : (l.drop output).take (out - output) ++
      mergeTwo proj (A0.drop (left - first)) (B0.drop (right - mid)) = mergeTwo proj A0 B0
  left_run : (l.drop left).take (mid - left) = A0.drop (left - first)
  right_run : (l.drop right).take (last - right) = B0.drop (right - mid)
  perm : List.Perm ((l.drop output).take (last - output)) ((l0.drop output).take (last - output))
  pre : l.take output = l0.take output
  post : l.drop last = l0.drop last
  len : l.length = l0.length
  count : out - output = (left - first) + (right - mid)
  hout : output ≤ out
  houtleft : out ≤ left
  hfirst : first ≤ left
  hleftmid : left ≤ mid
  hmidright : mid ≤ right
  hrightlast : right ≤ last
  hlast : last ≤ l.length

end Tcs
namespace Tcs

variable {α : Type u} {β : Type v} [Cmp β]

theorem exists_cons_drop_take' {l : List α} {lo hi : Nat} (h : lo < hi) (hlen : hi ≤ l.length) :
    ∃ xs, (l.drop lo).take (hi - lo) = l[lo]'(by omega) :: xs ∧
      (l.drop (lo + 1)).take (hi - (lo + 1)) = xs := by
  obtain ⟨x, xs, hx, hxl, htail⟩ := exists_cons_drop_take h hlen
  have hval : l[lo] = x := (List.getElem?_eq_some_iff.mp hxl).2
  refine ⟨xs, ?_, htail⟩
  rw [hval]
  exact hx

theorem getElem?_eq_of_take_eq {l₁ l₂ : List α} {n i : Nat} (h : l₁.take n = l₂.take n)
    (hi : i < n) : l₁[i]? = l₂[i]? := by
  have h' := congrArg (fun l => l[i]?) h
  rw [List.getElem?_take, ite_eq_left hi, List.getElem?_take, ite_eq_left hi] at h'
  exact h'

theorem getElem?_eq_of_drop_eq {l₁ l₂ : List α} {n i : Nat} (h : l₁.drop n = l₂.drop n)
    (hi : n ≤ i) : l₁[i]? = l₂[i]? := by
  have h' := congrArg (fun l => l[i - n]?) h
  rw [List.getElem?_drop, List.getElem?_drop] at h'
  rwa [Nat.add_sub_of_le hi] at h'

/-! ### Correctness of `merge_with_swap` -/

theorem mergeSwapLoop_inv (proj : α → β) (l0 : List α) (output first mid last : Nat)
    (A0 B0 : List α) :
    ∀ fuel l out left right, (mid - left) + (last - right) ≤ fuel →
      MergeInv proj l0 output first mid last A0 B0 l out left right →
      ∃ l' out' left' right', mergeSwapLoop proj fuel l out left mid right last = l' ∧
        MergeInv proj l0 output first mid last A0 B0 l' out' left' right' ∧
        ¬(left' < mid ∨ right' < last) := by
  intro fuel
  induction fuel with
  | zero =>
    intro l out left right hfuel hinv
    refine ⟨l, out, left, right, mergeSwapLoop.eq_1 proj l out left mid right last, hinv, ?_⟩
    have hl : left ≤ mid := hinv.hleftmid
    have hr : right ≤ last := hinv.hrightlast
    rintro (h | h) <;> omega
  | succ fuel ih =>
    intro l out left right hfuel hinv
    have houtle : output ≤ out := hinv.hout
    have houtsq : out ≤ left := hinv.houtleft
    have hfirstle : first ≤ left := hinv.hfirst
    have hleftmidle : left ≤ mid := hinv.hleftmid
    have hmidrightle : mid ≤ right := hinv.hmidright
    have hrightlastle : right ≤ last := hinv.hrightlast
    have hlastlen : last ≤ l.length := hinv.hlast
    have hcounteq : out - output = (left - first) + (right - mid) := hinv.count
    have hbufeq : output + (last - mid) ≤ first := hinv.hbuffer
    have houtleftle : output ≤ left := Nat.le_trans houtle houtsq
    have houtmidle : output ≤ mid := Nat.le_trans houtleftle hleftmidle
    have houtrightle : output ≤ right := Nat.le_trans houtmidle hmidrightle
    have houtlastle : output ≤ last := Nat.le_trans houtrightle hrightlastle
    have hleftrightle : left ≤ right := Nat.le_trans hleftmidle hmidrightle
    have hleftlastle : left ≤ last := Nat.le_trans hleftrightle hrightlastle
    have hmidlastle : mid ≤ last := Nat.le_trans hmidrightle hrightlastle
    rw [mergeSwapLoop.eq_2]
    by_cases hguard : left < mid ∨ right < last
    · rw [dite_eq_left hguard]
      by_cases hre : right = last
      · rw [dite_eq_left hre]
        have hleft : left < mid := by
          rcases hguard with h | h
          · exact h
          · omega
        have hmidlen : mid ≤ l.length := by omega
        have hleftlen : left < l.length := by omega
        rw [dite_eq_left hleftlen]
        obtain ⟨xs, hA, htailA⟩ := exists_cons_drop_take' (l := l) hleft hmidlen
        have hA0 : A0.drop (left - first) = l[left] :: xs := hinv.left_run.symm.trans hA
        have hdropA : A0.drop (left - first + 1) = xs := by
          rw [← List.drop_drop (i := 1) (j := left - first), hA0]
          simp
        have hBnil : B0.drop (right - mid) = [] := by
          rw [hre]
          have h := hinv.right_run
          rw [hre, Nat.sub_self, List.take_zero] at h
          exact h.symm
        have hmerge' : mergeTwo proj (A0.drop (left - first)) (B0.drop (right - mid)) =
            l[left] :: mergeTwo proj (A0.drop (left - first + 1)) (B0.drop (right - mid)) := by
          rw [hA0, hdropA, hBnil, mergeTwo_nil_right, mergeTwo_nil_right]
        have hfuel' : (mid - (left + 1)) + (last - right) ≤ fuel := by
          have hle1 : 1 ≤ mid - left := Nat.succ_le_of_lt (Nat.sub_pos_of_lt hleft)
          rw [show mid - (left + 1) = mid - left - 1 from (Nat.sub_sub mid left 1).symm]
          have hgoal : (mid - left - 1) + (last - right) + 1 ≤ fuel + 1 := by
            rw [Nat.add_right_comm, Nat.sub_add_cancel hle1]
            exact hfuel
          exact Nat.add_le_add_iff_right.mp hgoal
        have hinv'' : MergeInv proj l0 output first mid last A0 B0 (Bfprt.swapAt l out left)
            (out + 1) (left + 1) right :=
          { hbuffer := hinv.hbuffer
            hA0 := hinv.hA0
            hB0 := hinv.hB0
            merge := by
              rw [Bfprt.swapAt_drop_take_succ (l := l) (o := output) (i := out) (j := left)
                houtle houtsq (by omega)]
              rw [show left + 1 - first = left - first + 1 by omega, List.append_assoc,
                List.singleton_append, ← hmerge']
              exact hinv.merge
            left_run := by
              rw [Bfprt.swapAt_drop_of_lt (l := l) (i := out) (j := left) (k := left + 1)
                  (by omega) (by omega),
                show left + 1 - first = left - first + 1 by omega, htailA, hdropA]
            right_run := by
              rw [Bfprt.swapAt_drop_of_lt (l := l) (i := out) (j := left) (k := right)
                (by omega) (by omega)]
              exact hinv.right_run
            perm := by
              refine (perm_range_of_perm (l := l) (l' := Bfprt.swapAt l out left) (lo := output)
                (hi := last) (hperm := Bfprt.swapAt_perm l out left) ?_ ?_ (by omega)).trans hinv.perm
              · exact Bfprt.swapAt_take_of_le houtle houtleftle
              · exact Bfprt.swapAt_drop_of_lt (by omega) (by omega)
            pre := (Bfprt.swapAt_take_of_le houtle houtleftle).trans hinv.pre
            post := (Bfprt.swapAt_drop_of_lt (by omega) (by omega)).trans hinv.post
            len := by rw [Bfprt.swapAt_length]; exact hinv.len
            count := by omega
            hout := by omega
            houtleft := by omega
            hfirst := by omega
            hleftmid := by omega
            hmidright := by omega
            hrightlast := by omega
            hlast := by rw [Bfprt.swapAt_length]; exact hinv.hlast }
        obtain ⟨l', out', left', right', hstep, hinv', hdone⟩ :=
          ih (Bfprt.swapAt l out left) (out + 1) (left + 1) right hfuel' hinv''
        exact ⟨l', out', left', right', hstep, hinv', hdone⟩
      · rw [dite_eq_right hre]
        have hright : right < last := Nat.lt_of_le_of_ne hrightlastle hre
        have hmidlen : mid ≤ l.length := by omega
        have hrightlen : right < l.length := by omega
        have hleftlen : left < l.length := by omega
        rw [dite_eq_left hleftlen, dite_eq_left hrightlen]
        by_cases hb : left < mid ∧ Cmp.ble (proj l[left]) (proj l[right]) = true
        · rw [dite_eq_left hb]
          have hleft : left < mid := hb.1
          obtain ⟨xs, hA, htailA⟩ := exists_cons_drop_take' (l := l) hleft hmidlen
          have hA0 : A0.drop (left - first) = l[left] :: xs := hinv.left_run.symm.trans hA
          have hdropA : A0.drop (left - first + 1) = xs := by
            rw [← List.drop_drop (i := 1) (j := left - first), hA0]
            simp
          have hB0 : B0.drop (right - mid) = l[right] :: B0.drop (right - mid + 1) := by
            obtain ⟨ys, hB, _⟩ := exists_cons_drop_take' (l := l) hright hlastlen
            have hBeq : B0.drop (right - mid) = l[right] :: ys := hinv.right_run.symm.trans hB
            have hys : B0.drop (right - mid + 1) = ys := by
              rw [← List.drop_drop (i := 1) (j := right - mid), hBeq]
              simp
            rw [hys]
            exact hBeq
          have hA0' : A0.drop (left - first) = l[left] :: A0.drop (left - first + 1) := by
            rw [hA0, hdropA]
          have hBr : B0.drop (right - mid) = [] ∨
              ∃ y ys, B0.drop (right - mid) = y :: ys ∧
                Cmp.ble (proj (l[left])) (proj y) = true :=
            Or.inr ⟨l[right], B0.drop (right - mid + 1), hB0, hb.2⟩
          have hmerge' : mergeTwo proj (A0.drop (left - first)) (B0.drop (right - mid)) =
              l[left] :: mergeTwo proj (A0.drop (left - first + 1)) (B0.drop (right - mid)) :=
            mergeTwo_drop_left (proj := proj) (Ar := A0.drop (left - first))
              (Br := B0.drop (right - mid)) (x := l[left]'(by omega))
              (xs := A0.drop (left - first + 1)) hA0' hBr
          have hfuel' : (mid - (left + 1)) + (last - right) ≤ fuel := by
            have hle1 : 1 ≤ mid - left := Nat.succ_le_of_lt (Nat.sub_pos_of_lt hb.1)
            rw [show mid - (left + 1) = mid - left - 1 from (Nat.sub_sub mid left 1).symm]
            have hgoal : (mid - left - 1) + (last - right) + 1 ≤ fuel + 1 := by
              rw [Nat.add_right_comm, Nat.sub_add_cancel hle1]
              exact hfuel
            exact Nat.add_le_add_iff_right.mp hgoal
          have hinv'' : MergeInv proj l0 output first mid last A0 B0 (Bfprt.swapAt l out left)
              (out + 1) (left + 1) right :=
            { hbuffer := hinv.hbuffer
              hA0 := hinv.hA0
              hB0 := hinv.hB0
              merge := by
                rw [Bfprt.swapAt_drop_take_succ (l := l) (o := output) (i := out) (j := left)
                  houtle houtsq (by omega)]
                rw [show left + 1 - first = left - first + 1 by omega, List.append_assoc,
                  List.singleton_append, ← hmerge']
                exact hinv.merge
              left_run := by
                rw [Bfprt.swapAt_drop_of_lt (l := l) (i := out) (j := left) (k := left + 1)
                    (by omega) (by omega),
                  show left + 1 - first = left - first + 1 by omega, htailA, hdropA]
              right_run := by
                rw [Bfprt.swapAt_drop_of_lt (l := l) (i := out) (j := left) (k := right)
                  (by omega) (by omega)]
                exact hinv.right_run
              perm := by
                refine (perm_range_of_perm (l := l) (l' := Bfprt.swapAt l out left) (lo := output)
                  (hi := last) (hperm := Bfprt.swapAt_perm l out left) ?_ ?_ (by omega)).trans hinv.perm
                · exact Bfprt.swapAt_take_of_le houtle houtleftle
                · exact Bfprt.swapAt_drop_of_lt (by omega) (by omega)
              pre := (Bfprt.swapAt_take_of_le houtle houtleftle).trans hinv.pre
              post := (Bfprt.swapAt_drop_of_lt (by omega) (by omega)).trans hinv.post
              len := by rw [Bfprt.swapAt_length]; exact hinv.len
              count := by omega
              hout := by omega
              houtleft := by omega
              hfirst := by omega
              hleftmid := by omega
              hmidright := by omega
              hrightlast := by omega
              hlast := by rw [Bfprt.swapAt_length]; exact hinv.hlast }
          obtain ⟨l', out', left', right', hstep, hinv', hdone⟩ :=
            ih (Bfprt.swapAt l out left) (out + 1) (left + 1) right hfuel' hinv''
          exact ⟨l', out', left', right', hstep, hinv', hdone⟩
        · rw [dite_eq_right hb]
          have hrightlt : right < l.length := hrightlen
          obtain ⟨ys, hB, htailB⟩ := exists_cons_drop_take' (l := l) hright hlastlen
          have hB0 : B0.drop (right - mid) = l[right] :: ys := hinv.right_run.symm.trans hB
          have hdropB : B0.drop (right - mid + 1) = ys := by
            rw [← List.drop_drop (i := 1) (j := right - mid), hB0]
            simp
          have hmerge' : mergeTwo proj (A0.drop (left - first)) (B0.drop (right - mid)) =
              l[right] :: mergeTwo proj (A0.drop (left - first)) (B0.drop (right - mid + 1)) := by
            have hAr : A0.drop (left - first) = [] ∨
                ∃ x xs, A0.drop (left - first) = x :: xs ∧
                  Cmp.ble (proj x) (proj l[right]) = false := by
              by_cases hlm : left < mid
              · obtain ⟨xs', hA', _⟩ := exists_cons_drop_take' (l := l) hlm hmidlen
                have hb2 : Cmp.ble (proj l[left]) (proj l[right]) = false := by
                  cases hbc : Cmp.ble (proj l[left]) (proj l[right]) with
                  | false => rfl
                  | true => exact absurd ⟨hlm, hbc⟩ hb
                exact Or.inr ⟨l[left], xs', hinv.left_run.symm.trans hA', hb2⟩
              · refine Or.inl ?_
                have hlm' : left = mid := Nat.le_antisymm hleftmidle (Nat.le_of_not_lt hlm)
                rw [← hinv.left_run, hlm', Nat.sub_self, List.take_zero]
            rw [mergeTwo_drop_right (y := l[right]) (ys := ys) hB0 hAr, ← hdropB]
          have hfuel' : (mid - left) + (last - (right + 1)) ≤ fuel := by
            have hle1 : 1 ≤ last - right := Nat.succ_le_of_lt (Nat.sub_pos_of_lt hright)
            rw [show last - (right + 1) = last - right - 1 from (Nat.sub_sub last right 1).symm]
            have hgoal : (mid - left) + (last - right - 1) + 1 ≤ fuel + 1 := by
              rw [Nat.add_assoc, Nat.sub_add_cancel hle1]
              exact hfuel
            exact Nat.add_le_add_iff_right.mp hgoal
          have houtlt : out < left := by
            rcases Nat.lt_or_ge out left with h | h
            · exact h
            · exfalso
              have hout : out = left := Nat.le_antisymm houtsq h
              have ho : output ≤ left := Nat.le_trans houtle (Nat.le_of_eq hout)
              have hc : left - output = (left - first) + (right - mid) := by
                have hh := hcounteq
                rwa [hout] at hh
              have hcancel : output + (right - mid) = first := by
                have h1 : output + ((left - first) + (right - mid)) = left := by
                  have hh := (Nat.sub_eq_iff_eq_add ho).mp hc
                  rw [Nat.add_comm] at hh
                  exact hh.symm
                have h2 : left = first + (left - first) := (Nat.add_sub_of_le hfirstle).symm
                have h3 : output + ((left - first) + (right - mid)) = first + (left - first) :=
                  h1.trans h2
                have h4 : (output + (right - mid)) + (left - first) = first + (left - first) := by
                  calc (output + (right - mid)) + (left - first)
                      = output + ((right - mid) + (left - first)) := Nat.add_assoc _ _ _
                    _ = output + ((left - first) + (right - mid)) := by
                          rw [Nat.add_comm (right - mid) (left - first)]
                    _ = first + (left - first) := h3
                exact Nat.add_right_cancel h4
              have hle : last - mid ≤ right - mid := by
                have hh : output + (last - mid) ≤ output + (right - mid) := by
                  rw [hcancel]
                  exact hbufeq
                exact Nat.add_le_add_iff_left.mp hh
              have hgt : right - mid < last - mid := by
                have h1 : (right - mid) + 1 ≤ last - mid := by
                  rw [← Nat.sub_add_comm hmidrightle]
                  exact Nat.sub_le_sub_right (Nat.succ_le_of_lt hright) mid
                exact Nat.lt_of_succ_le h1
              exact absurd hle (Nat.not_le.mpr hgt)
          have hleftrun : ((Bfprt.swapAt l out right).drop left).take (mid - left) =
              A0.drop (left - first) := by
            rw [Bfprt.swapAt_drop_take_of_lt_of_le (l := l) (i := out) (j := right)
              (lo := left) (m := mid - left) houtlt (by
                rw [Nat.add_sub_of_le hleftmidle]
                exact hmidrightle)]
            exact hinv.left_run
          have houtlt' : out < right + 1 :=
            Nat.lt_of_le_of_lt (Nat.le_trans houtsq hleftrightle) (Nat.lt_succ_self right)
          have hrightlt' : right < right + 1 := Nat.lt_succ_self right
          have houtlastlt : out < last :=
            Nat.lt_of_le_of_lt (Nat.le_trans houtsq hleftrightle) hright
          have hinv'' : MergeInv proj l0 output first mid last A0 B0 (Bfprt.swapAt l out right)
              (out + 1) left (right + 1) :=
            { hbuffer := hinv.hbuffer
              hA0 := hinv.hA0
              hB0 := hinv.hB0
              merge := by
                rw [Bfprt.swapAt_drop_take_succ (l := l) (o := output) (i := out) (j := right)
                  houtle (Nat.le_trans houtsq hleftrightle) hrightlen]
                rw [Nat.sub_add_comm hmidrightle, List.append_assoc,
                  List.singleton_append, ← hmerge']
                exact hinv.merge
              left_run := hleftrun
              right_run := by
                rw [Bfprt.swapAt_drop_of_lt (l := l) (i := out) (j := right) (k := right + 1)
                  houtlt' hrightlt',
                  Nat.sub_add_comm hmidrightle, htailB, hdropB]
              perm := by
                refine (perm_range_of_perm (l := l) (l' := Bfprt.swapAt l out right) (lo := output)
                  (hi := last) (hperm := Bfprt.swapAt_perm l out right) ?_ ?_
                  houtlastle).trans hinv.perm
                · exact Bfprt.swapAt_take_of_le houtle houtrightle
                · exact Bfprt.swapAt_drop_of_lt houtlastlt hright
              pre := (Bfprt.swapAt_take_of_le houtle houtrightle).trans hinv.pre
              post := (Bfprt.swapAt_drop_of_lt houtlastlt hright).trans hinv.post
              len := by rw [Bfprt.swapAt_length]; exact hinv.len
              count := by
                rw [Nat.sub_add_comm houtle, hcounteq, Nat.add_assoc,
                  Nat.sub_add_comm hmidrightle]
              hout := Nat.le_trans houtle (Nat.le_succ out)
              houtleft := Nat.succ_le_of_lt houtlt
              hfirst := hfirstle
              hleftmid := hleftmidle
              hmidright := Nat.le_trans hmidrightle (Nat.le_succ right)
              hrightlast := Nat.succ_le_of_lt hright
              hlast := by rw [Bfprt.swapAt_length]; exact hinv.hlast }
          obtain ⟨l', out', left', right', hstep, hinv', hdone⟩ :=
            ih (Bfprt.swapAt l out right) (out + 1) left (right + 1) hfuel' hinv''
          exact ⟨l', out', left', right', hstep, hinv', hdone⟩
    · rw [dite_eq_right hguard]
      exact ⟨l, out, left, right, rfl, hinv, hguard⟩

end Tcs

namespace Tcs

variable {α : Type u} {β : Type v} [Cmp β]

/-- The initial loop state of `merge_with_swap`, as a `MergeInv`. -/
theorem mergeSwapLoop_run (proj : α → β) {l : List α} {output first mid last : Nat}
    (hfm : first ≤ mid) (hml : mid ≤ last) (hlast : last ≤ l.length)
    (hbuffer : output + (last - mid) ≤ first) :
    ∃ l' out' left' right',
      mergeWithSwap proj l output first mid last = l' ∧
      MergeInv proj l output first mid last ((l.drop first).take (mid - first))
        ((l.drop mid).take (last - mid)) l' out' left' right' ∧
      ¬(left' < mid ∨ right' < last) := by
  have houtle : output ≤ first := by omega
  refine mergeSwapLoop_inv proj l output first mid last _ _ (last - first) l output first mid
    (by omega) ?_
  exact
    { hbuffer := hbuffer
      hA0 := rfl
      hB0 := rfl
      merge := by simp
      left_run := by simp
      right_run := by simp
      perm := List.Perm.refl _
      pre := rfl
      post := rfl
      len := rfl
      count := by simp
      hout := Nat.le_refl output
      houtleft := houtle
      hfirst := Nat.le_refl first
      hleftmid := hfm
      hmidright := Nat.le_refl mid
      hrightlast := hml
      hlast := hlast }

/-- **The full `merge_with_swap` contract**: positions outside `[output, last)` are
untouched, the buffer range is permuted, and the first `last - first` buffer slots
hold exactly the pure two-run merge. -/
theorem mergeWithSwap_final (proj : α → β) {l : List α} {output first mid last : Nat}
    (hfm : first ≤ mid) (hml : mid ≤ last) (hlast : last ≤ l.length)
    (hbuffer : output + (last - mid) ≤ first) :
    (mergeWithSwap proj l output first mid last).length = l.length ∧
    List.Perm (((mergeWithSwap proj l output first mid last).drop output).take
        (last - output)) ((l.drop output).take (last - output)) ∧
    (∀ i, i < output ∨ last ≤ i →
        (mergeWithSwap proj l output first mid last)[i]? = l[i]?) ∧
    ((mergeWithSwap proj l output first mid last).drop output).take (last - first) =
      mergeTwo proj ((l.drop first).take (mid - first)) ((l.drop mid).take (last - mid)) := by
  obtain ⟨l', out', left', right', hstep, hinv', hdone⟩ :=
    mergeSwapLoop_run proj hfm hml hlast hbuffer
  rw [hstep]
  have hleft' : left' = mid := by
    have h1 := hinv'.hleftmid
    have h2 : ¬(left' < mid) := fun h => hdone (Or.inl h)
    omega
  have hright' : right' = last := by
    have h1 := hinv'.hrightlast
    have h2 : ¬(right' < last) := fun h => hdone (Or.inr h)
    omega
  have hA0len : ((l.drop first).take (mid - first)).length = mid - first := by
    rw [List.length_take, List.length_drop]
    exact Nat.min_eq_left (by omega)
  have hB0len : ((l.drop mid).take (last - mid)).length = last - mid := by
    rw [List.length_take, List.length_drop]
    exact Nat.min_eq_left (by omega)
  have hA0 : ((l.drop first).take (mid - first)).drop (mid - first) = [] :=
    List.drop_eq_nil_of_le (by rw [hA0len]; exact Nat.le_refl _)
  have hB0 : ((l.drop mid).take (last - mid)).drop (last - mid) = [] :=
    List.drop_eq_nil_of_le (by rw [hB0len]; exact Nat.le_refl _)
  have hmerge := hinv'.merge
  rw [hinv'.hA0, hinv'.hB0, hleft', hright'] at hmerge
  rw [hA0, hB0] at hmerge
  have hout' : out' - output = last - first := by
    rw [hinv'.count, hleft', hright']
    omega
  rw [hout', mergeTwo_nil_left, List.append_nil] at hmerge
  exact ⟨hinv'.len, hinv'.perm, fun i hi =>
    hi.elim (fun h => getElem?_eq_of_take_eq hinv'.pre h)
      (fun h => getElem?_eq_of_drop_eq hinv'.post h), hmerge⟩

theorem mergeWithSwap_length (proj : α → β) {l : List α} {output first mid last : Nat}
    (hfm : first ≤ mid) (hml : mid ≤ last) (hlast : last ≤ l.length)
    (hbuffer : output + (last - mid) ≤ first) :
    (mergeWithSwap proj l output first mid last).length = l.length :=
  (mergeWithSwap_final proj hfm hml hlast hbuffer).1

theorem mergeWithSwap_range_perm (proj : α → β) {l : List α} {output first mid last : Nat}
    (hfm : first ≤ mid) (hml : mid ≤ last) (hlast : last ≤ l.length)
    (hbuffer : output + (last - mid) ≤ first) :
    List.Perm (((mergeWithSwap proj l output first mid last).drop output).take
        (last - output)) ((l.drop output).take (last - output)) :=
  (mergeWithSwap_final proj hfm hml hlast hbuffer).2.1

theorem mergeWithSwap_outside (proj : α → β) {l : List α} {output first mid last : Nat}
    (hfm : first ≤ mid) (hml : mid ≤ last) (hlast : last ≤ l.length)
    (hbuffer : output + (last - mid) ≤ first) :
    ∀ i, i < output ∨ last ≤ i →
      (mergeWithSwap proj l output first mid last)[i]? = l[i]? :=
  (mergeWithSwap_final proj hfm hml hlast hbuffer).2.2.1

/-- The merge buffer holds exactly the pure merge of the two runs, which pins the
tie-breaking of the C++ loop: the left run is taken on equal keys. -/
theorem mergeWithSwap_eq_mergeTwo (proj : α → β) {l : List α} {output first mid last : Nat}
    (hfm : first ≤ mid) (hml : mid ≤ last) (hlast : last ≤ l.length)
    (hbuffer : output + (last - mid) ≤ first) :
    ((mergeWithSwap proj l output first mid last).drop output).take (last - first) =
      mergeTwo proj ((l.drop first).take (mid - first)) ((l.drop mid).take (last - mid)) :=
  (mergeWithSwap_final proj hfm hml hlast hbuffer).2.2.2

/-- The merged prefix is sorted, because it is the pure merge of two sorted runs. -/
theorem mergeWithSwap_sorted (proj : α → β) {l : List α} {output first mid last : Nat}
    (hfm : first ≤ mid) (hml : mid ≤ last) (hlast : last ≤ l.length)
    (hbuffer : output + (last - mid) ≤ first)
    (hsortedA : SortedOn proj l first mid) (hsortedB : SortedOn proj l mid last) :
    Sorted (KeyLe proj)
      (((mergeWithSwap proj l output first mid last).drop output).take (last - first)) := by
  rw [mergeWithSwap_eq_mergeTwo proj hfm hml hlast hbuffer]
  exact mergeTwo_sorted proj _ _ hsortedA hsortedB

/-- Sortedness as a range predicate, the form the later block phase consumes. -/
theorem mergeWithSwap_sortedOn (proj : α → β) {l : List α} {output first mid last : Nat}
    (hfm : first ≤ mid) (hml : mid ≤ last) (hlast : last ≤ l.length)
    (hbuffer : output + (last - mid) ≤ first)
    (hsortedA : SortedOn proj l first mid) (hsortedB : SortedOn proj l mid last) :
    SortedOn proj (mergeWithSwap proj l output first mid last) output
      (output + (last - first)) := by
  unfold SortedOn
  rw [show output + (last - first) - output = last - first by omega]
  exact mergeWithSwap_sorted proj hfm hml hlast hbuffer hsortedA hsortedB

end Tcs
namespace Tcs

variable {α : Type u} {β : Type v} [Cmp β]

/-! ## The inner scans of `inplace_merge_with_rotation` -/

/-- The forward scan of the left-turning branch: from `sp = mid` it advances while
`l[sp] < x`, i.e. while the right run has run ahead of the current left element. -/
def scanRight (proj : α → β) (x : α) : Nat → List α → Nat → Nat → Nat
  | 0, _, sp, _ => sp
  | fuel + 1, l, sp, last =>
      if _ : sp < last then
        if hl : sp < l.length then
          if Cmp.blt (proj l[sp]) (proj x) then scanRight proj x fuel l (sp + 1) last else sp
        else sp
      else sp

/-- The backward scan of the right-turning branch: from `sp = mid` it retreats
while `y < l[sp - 1]`, i.e. while the left run ends above the last right element. -/
def scanLeft (proj : α → β) (y : α) : Nat → List α → Nat → Nat → Nat
  | 0, _, sp, _ => sp
  | fuel + 1, l, sp, first =>
      if _ : first < sp then
        if hl : sp - 1 < l.length then
          if Cmp.blt (proj y) (proj l[sp - 1]) then scanLeft proj y fuel l (sp - 1) first else sp
        else sp
      else sp

theorem scanRight_spec (proj : α → β) (x : α) :
    ∀ fuel l sp last, (hsp : sp + fuel = last) → (hlen : last ≤ l.length) →
      sp ≤ scanRight proj x fuel l sp last ∧ scanRight proj x fuel l sp last ≤ last ∧
      (∀ k (hk : k < l.length), sp ≤ k → k < scanRight proj x fuel l sp last →
          Cmp.blt (proj (l[k]'hk)) (proj x) = true) ∧
      (∀ (_hlt : scanRight proj x fuel l sp last < last) (b : α),
          l[scanRight proj x fuel l sp last]? = some b → Cmp.blt (proj b) (proj x) = false) := by
  intro fuel
  induction fuel with
  | zero =>
    intro l sp last hsp hlen
    rw [scanRight.eq_1]
    refine ⟨Nat.le_refl _, ?_, ?_, ?_⟩
    · omega
    · intro k hk hk1 hk2
      omega
    · intro _hlt b hb
      omega
  | succ fuel ih =>
    intro l sp last hsp hlen
    rw [scanRight.eq_2]
    by_cases h1 : sp < last
    · rw [dite_eq_left h1]
      by_cases h2 : sp < l.length
      · rw [dite_eq_left h2]
        by_cases h3 : Cmp.blt (proj l[sp]) (proj x) = true
        · rw [ite_eq_left h3]
          have hsp1 : sp + 1 + fuel = last := by omega
          obtain ⟨ih1, ih2, ih3, ih4⟩ := ih l (sp + 1) last hsp1 hlen
          refine ⟨by omega, ih2, ?_, ?_⟩
          · intro k hklen hk hk'
            rcases Nat.eq_or_lt_of_le hk with rfl | hk''
            · exact h3
            · exact ih3 k hklen (by omega) hk'
          · intro hlt b hb
            exact ih4 hlt b hb
        · rw [ite_eq_right h3]
          refine ⟨Nat.le_refl _, by omega, ?_, ?_⟩
          · intro k hklen hk hk'
            omega
          · intro hlt b hb
            have hb' : b = l[sp] := ((List.getElem?_eq_some_iff.mp hb).2).symm
            have h3' : Cmp.blt (proj l[sp]) (proj x) = false := by
              cases hb3 : Cmp.blt (proj l[sp]) (proj x) <;> simp_all
            rw [hb', h3']
      · rw [dite_eq_right h2]
        exfalso
        omega
    · rw [dite_eq_right h1]
      refine ⟨Nat.le_refl _, by omega, ?_, ?_⟩
      · intro k hklen hk hk'
        omega
      · intro hlt b hb
        exact absurd hlt (by omega)

theorem scanLeft_spec (proj : α → β) (y : α) :
    ∀ fuel l sp first, (hsp : sp = first + fuel) → (hlen : sp ≤ l.length) →
      first ≤ scanLeft proj y fuel l sp first ∧ scanLeft proj y fuel l sp first ≤ sp ∧
      (∀ k (hk : k < l.length), scanLeft proj y fuel l sp first ≤ k → k < sp →
          Cmp.blt (proj y) (proj (l[k]'hk)) = true) ∧
      (∀ (_hlt : first < scanLeft proj y fuel l sp first) (b : α),
          l[scanLeft proj y fuel l sp first - 1]? = some b → Cmp.blt (proj y) (proj b) = false) := by
  intro fuel
  induction fuel with
  | zero =>
    intro l sp first hsp hlen
    rw [scanLeft.eq_1]
    refine ⟨?_, Nat.le_refl _, ?_, ?_⟩
    · omega
    · intro k hk hk1 hk2
      omega
    · intro _hlt b hb
      omega
  | succ fuel ih =>
    intro l sp first hsp hlen
    rw [scanLeft.eq_2]
    by_cases h1 : first < sp
    · rw [dite_eq_left h1]
      by_cases h2 : sp - 1 < l.length
      · rw [dite_eq_left h2]
        by_cases h3 : Cmp.blt (proj y) (proj l[sp - 1]) = true
        · rw [ite_eq_left h3]
          have hsp1 : sp - 1 = first + fuel := by omega
          have hlen1 : sp - 1 ≤ l.length := by omega
          obtain ⟨ih1, ih2, ih3, ih4⟩ := ih l (sp - 1) first hsp1 hlen1
          refine ⟨ih1, by omega, ?_, ?_⟩
          · intro k hklen hk hk'
            rcases Nat.eq_or_lt_of_le hk' with rfl | hk''
            · exact h3
            · exact ih3 k hklen (by omega) (by omega)
          · intro hlt b hb
            exact ih4 hlt b hb
        · rw [ite_eq_right h3]
          refine ⟨by omega, Nat.le_refl _, ?_, ?_⟩
          · intro k hklen hk hk'
            omega
          · intro hlt b hb
            have hb' : b = l[sp - 1] := ((List.getElem?_eq_some_iff.mp hb).2).symm
            have h3' : Cmp.blt (proj y) (proj l[sp - 1]) = false := by
              cases hb3 : Cmp.blt (proj y) (proj l[sp - 1]) <;> simp_all
            rw [hb', h3']
      · rw [dite_eq_right h2]
        exfalso
        omega
    · rw [dite_eq_right h1]
      refine ⟨by omega, Nat.le_refl _, ?_, ?_⟩
      · intro k hklen hk hk'
        omega
      · intro hlt b hb
        exact absurd hlt (by omega)

end Tcs
namespace Tcs

variable {α : Type u} {β : Type v} [Cmp β]

/-! ## Block helpers for the rotation merge -/

/-- From `not (a < b)` conclude `b ≤ a`. The scan of the right-turning branch
stops on this form. -/
theorem ble_of_not_blt {a b : β} (h : Cmp.blt a b = false) : Cmp.ble b a = true := by
  rcases Cmp.ble_total a b with hab | hba
  · by_cases hba' : Cmp.ble b a = true
    · exact hba'
    · have hba'' : Cmp.ble b a = false := by
        cases hb : Cmp.ble b a <;> simp_all
      exact absurd (Cmp.blt_of_ble_of_not_ble hab hba'') (by rw [h]; exact Bool.false_ne_true)
  · exact hba

/-- Extracting a block from a three-part decomposition. -/
theorem drop_take_of_append {X S Y : List α} {lo hi : Nat} (hX : X.length = lo)
    (hS : S.length = hi - lo) : ((X ++ S ++ Y).drop lo).take (hi - lo) = S := by
  have h1 : (X ++ S ++ Y).drop lo = S ++ Y := by
    rw [List.append_assoc, List.drop_append_of_le_length (l₁ := X) (l₂ := S ++ Y) (i := lo)
      (Nat.le_of_eq hX.symm), List.drop_eq_nil_of_le (Nat.le_of_eq hX), List.nil_append]
  rw [h1, ← hS, List.take_append_length]

theorem take_append_of_len {X Y : List α} {n : Nat} (h : X.length = n) : (X ++ Y).take n = X := by
  rw [← h, List.take_append_length]

theorem drop_append_of_len {X Y : List α} {n : Nat} (h : X.length = n) : (X ++ Y).drop n = Y := by
  rw [← h, List.drop_append_length]

theorem sorted_take {R : α → α → Prop} {l : List α} {n : Nat} (h : Sorted R l) :
    Sorted R (l.take n) :=
  List.Pairwise.sublist (List.take_sublist n l) h

theorem sorted_drop {R : α → α → Prop} {l : List α} {n : Nat} (h : Sorted R l) :
    Sorted R (l.drop n) :=
  List.Pairwise.sublist (List.drop_sublist n l) h

theorem mem_of_mem_drop {a : α} {l : List α} {n : Nat} (h : a ∈ l.drop n) : a ∈ l :=
  List.Sublist.subset (List.drop_sublist n l) h

theorem allLe_take_right {R : α → α → Prop} {X Y : List α} {n : Nat} (h : AllLe R X Y) :
    AllLe R X (Y.take n) :=
  fun x hx z hz => h x hx z (List.mem_of_mem_take hz)

theorem allLe_take_left {R : α → α → Prop} {X Y : List α} {n : Nat} (h : AllLe R X Y) :
    AllLe R (X.take n) Y :=
  fun x hx z hz => h x (List.mem_of_mem_take hx) z hz

theorem allLe_drop_right {R : α → α → Prop} {X Y : List α} {n : Nat} (h : AllLe R X Y) :
    AllLe R X (Y.drop n) :=
  fun x hx z hz => h x hx z (mem_of_mem_drop hz)

theorem allLe_drop_left {R : α → α → Prop} {X Y : List α} {n : Nat} (h : AllLe R X Y) :
    AllLe R (X.drop n) Y :=
  fun x hx z hz => h x (mem_of_mem_drop hx) z hz

/-- The scan of the left-turning branch, in block form: every element of the first
`m` elements of the right run is strictly below the pivot. -/
theorem blt_of_mem_drop_take {proj : α → β} {x : α} {l : List α} {lo m : Nat}
    (h : ∀ k (hk : k < l.length), lo ≤ k → k < lo + m → Cmp.blt (proj (l[k]'hk)) (proj x) = true) :
    ∀ b ∈ (l.drop lo).take m, Cmp.blt (proj b) (proj x) = true := by
  intro b hb
  obtain ⟨j, hj, hjb⟩ := List.mem_iff_getElem.mp hb
  have hjlen : j < m := by
    rw [List.length_take] at hj
    omega
  have h1 : ((l.drop lo).take m)[j]? = some b := by
    rw [List.getElem?_eq_getElem hj, hjb]
  have h2 : l[lo + j]? = some b := by
    rw [List.getElem?_take, ite_eq_left hjlen, List.getElem?_drop] at h1
    exact h1
  have hlt : lo + j < l.length := (List.getElem?_eq_some_iff.mp h2).1
  have hval : l[lo + j] = b := (List.getElem?_eq_some_iff.mp h2).2
  have := h (lo + j) hlt (by omega) (by omega)
  simpa [hval] using this

/-- The scan of the right-turning branch, in block form: the pivot is strictly
below every element of the suffix selected by the scan. -/
theorem blt_of_mem_drop_take_left {proj : α → β} {y : α} {l : List α} {lo m : Nat}
    (h : ∀ k (hk : k < l.length), lo ≤ k → k < lo + m → Cmp.blt (proj y) (proj (l[k]'hk)) = true) :
    ∀ b ∈ (l.drop lo).take m, Cmp.blt (proj y) (proj b) = true := by
  intro b hb
  obtain ⟨j, hj, hjb⟩ := List.mem_iff_getElem.mp hb
  have hjlen : j < m := by
    rw [List.length_take] at hj
    omega
  have h1 : ((l.drop lo).take m)[j]? = some b := by
    rw [List.getElem?_eq_getElem hj, hjb]
  have h2 : l[lo + j]? = some b := by
    rw [List.getElem?_take, ite_eq_left hjlen, List.getElem?_drop] at h1
    exact h1
  have hlt : lo + j < l.length := (List.getElem?_eq_some_iff.mp h2).1
  have hval : l[lo + j] = b := (List.getElem?_eq_some_iff.mp h2).2
  have := h (lo + j) hlt (by omega) (by omega)
  simpa [hval] using this

/-- A pivot below the head of a sorted suffix is below the whole suffix. -/
theorem allLe_head_drop {proj : α → β} {B : List α} {m : Nat} {a : α}
    (hs : Sorted (KeyLe proj) B) (hm : m < B.length) (h : KeyLe proj a (B[m]'hm)) :
    AllLe (KeyLe proj) [a] (B.drop m) := by
  intro z hz w hw
  rw [List.mem_singleton] at hz
  subst hz
  obtain ⟨j, hj, hjw⟩ := List.mem_iff_getElem.mp hw
  have hjlen : m + j < B.length := by
    rw [List.length_drop] at hj
    omega
  have hw' : B[m + j] = w := by
    rw [← hjw, List.getElem_drop]
  cases j with
  | zero =>
    have h1 : (B.drop m)[0]? = some w := by
      rw [List.getElem?_eq_getElem hj, hjw]
    have h2 : B[m]? = some w := by
      rw [List.getElem?_drop, Nat.add_zero] at h1
      exact h1
    have hw0 : B[m]'(by omega) = w := (List.getElem?_eq_some_iff.mp h2).2
    rw [← hw0]
    exact h
  | succ j' =>
    have hrel : KeyLe proj (B[m]'hm) (B[m + (j' + 1)]'(by omega)) :=
      List.Pairwise.rel_getElem_of_lt hm (by omega) hs (by omega)
    have hw'' : KeyLe proj (B[m]'hm) w := by simpa [hw'] using hrel
    exact Cmp.ble_trans h hw''

/-- A sorted prefix is below `y` as soon as its last element is. -/
theorem allLe_take_last_le {proj : α → β} {B : List α} {m : Nat} {y : α}
    (hs : Sorted (KeyLe proj) B) (hm0 : 0 < m) (hm : m ≤ B.length)
    (h : KeyLe proj (B[m - 1]'(by omega)) y) : AllLe (KeyLe proj) (B.take m) [y] := by
  intro z hz w hw
  rw [List.mem_singleton] at hw
  subst hw
  obtain ⟨j, hj, hjz⟩ := List.mem_iff_getElem.mp hz
  have hjlen : j < m := by
    rw [List.length_take] at hj
    omega
  have hz1 : (B.take m)[j]? = some z := by
    rw [List.getElem?_eq_getElem hj, hjz]
  have hz2 : B[j]? = some z := by
    rw [List.getElem?_take, ite_eq_left hjlen] at hz1
    exact hz1
  have hzval : B[j] = z := (List.getElem?_eq_some_iff.mp hz2).2
  have hrel : KeyLe proj (B[j]'(by omega)) (B[m - 1]'(by omega)) := by
    rcases Nat.lt_or_eq_of_le (by omega : j ≤ m - 1) with hlt | heq
    · exact List.Pairwise.rel_getElem_of_lt (by omega) (by omega) hs hlt
    · cases heq
      exact Cmp.ble_refl _
  exact Cmp.ble_trans (by rwa [hzval] at hrel) h

/-- Rotating three blocks: `B ++ a :: A` is `a :: (A ++ B)` up to permutation. -/
theorem perm_rotate_cons (a : α) (A B : List α) : List.Perm (B ++ a :: A) (a :: (A ++ B)) := by
  have h : List.Perm ((B ++ [a]) ++ A) ([a] ++ (A ++ B)) :=
    (List.perm_append_comm (l₁ := B ++ [a]) (l₂ := A)).trans
      ((List.Perm.of_eq (List.append_assoc A B [a]).symm).trans
        (List.perm_append_comm (l₁ := A ++ B) (l₂ := [a])))
  rwa [List.append_assoc, List.singleton_append, List.singleton_append] at h

theorem allLe_of_subset_right {R : α → α → Prop} {X Y Z : List α} (h : AllLe R X Z)
    (hYZ : ∀ y ∈ Y, y ∈ Z) : AllLe R X Y :=
  fun x hx y hy => h x hx y (hYZ y hy)

theorem allLe_of_subset_left {R : α → α → Prop} {X Y Z : List α} (h : AllLe R X Z)
    (hYX : ∀ y ∈ Y, y ∈ X) : AllLe R Y Z :=
  fun y hy z hz => h y (hYX y hy) z hz

/-- In a sorted list the first `m` elements are below the rest. -/
theorem allLe_take_drop_of_sorted {R : α → α → Prop} {B : List α} {m : Nat}
    (hs : Sorted R B) : AllLe R (B.take m) (B.drop m) := by
  intro x hx y hy
  obtain ⟨j, hj, hjx⟩ := List.mem_iff_getElem.mp hx
  obtain ⟨i, hi, hiy⟩ := List.mem_iff_getElem.mp hy
  have hjlen : j < m := by
    rw [List.length_take] at hj
    omega
  have hlen : m + i < B.length := by
    rw [List.length_drop] at hi
    omega
  have hx' : B[j] = x := by
    have h1 : (B.take m)[j]? = some x := by rw [List.getElem?_eq_getElem hj, hjx]
    have h2 : B[j]? = some x := by rwa [List.getElem?_take, ite_eq_left hjlen] at h1
    exact (List.getElem?_eq_some_iff.mp h2).2
  have hy' : B[m + i] = y := by
    have h1 : (B.drop m)[i]? = some y := by rw [List.getElem?_eq_getElem hi, hiy]
    have h2 : B[m + i]? = some y := by rwa [List.getElem?_drop] at h1
    exact (List.getElem?_eq_some_iff.mp h2).2
  have hrel : R (B[j]'(by omega)) (B[m + i]'(by omega)) :=
    List.Pairwise.rel_getElem_of_lt (by omega) (by omega) hs (by omega)
  rwa [hx', hy'] at hrel

/-- Extracting a block with one trailing block. -/
theorem drop_take_of_append1 {X S Y1 : List α} {lo hi : Nat} (hX : X.length = lo)
    (hS : S.length = hi - lo) : (((X ++ S) ++ Y1).drop lo).take (hi - lo) = S :=
  drop_take_of_append (X := X) (S := S) (Y := Y1) (lo := lo) (hi := hi) hX hS

/-- Extracting a block with two trailing blocks. -/
theorem drop_take_of_append2 {X S Y1 Y2 : List α} {lo hi : Nat} (hX : X.length = lo)
    (hS : S.length = hi - lo) : ((((X ++ S) ++ Y1) ++ Y2).drop lo).take (hi - lo) = S := by
  have h := drop_take_of_append (X := X) (S := S) (Y := Y1 ++ Y2) (lo := lo) (hi := hi) hX hS
  rwa [← List.append_assoc] at h

/-- Extracting a block with three trailing blocks. -/
theorem drop_take_of_append3 {X S Y1 Y2 Y3 : List α} {lo hi : Nat} (hX : X.length = lo)
    (hS : S.length = hi - lo) : (((((X ++ S) ++ Y1) ++ Y2) ++ Y3).drop lo).take (hi - lo) = S := by
  have h := drop_take_of_append (X := X) (S := S) (Y := (Y1 ++ Y2) ++ Y3) (lo := lo) (hi := hi) hX hS
  rwa [← List.append_assoc, ← List.append_assoc] at h

end Tcs
namespace Tcs

variable {α : Type u} {β : Type v} [Cmp β]

/-! ## The block-rotation loop -/

/-- Loop invariant of `inplace_merge_with_rotation`, as a `Prop` so that it can be
eliminated while building the next invariant. The list is the old prefix, the
finalized prefix `P`, the two live runs `A` and `B`, the finalized suffix `Q` and
the old suffix; every element of `P` is below all of `A ++ B ++ Q`, and every
element of `P ++ A ++ B` is below all of `Q`. -/
def RotInv (proj : α → β) (l0 : List α) (first0 last0 : Nat) (l : List α)
    (first mid last : Nat) : Prop :=
  ∃ P A B Q : List α,
    l = l0.take first0 ++ P ++ A ++ B ++ Q ++ l0.drop last0 ∧
    A = (l.drop first).take (mid - first) ∧
    B = (l.drop mid).take (last - mid) ∧
    first = first0 + P.length ∧
    mid = first + A.length ∧
    last = mid + B.length ∧
    last0 = last + Q.length ∧
    last ≤ l.length ∧
    Sorted (KeyLe proj) P ∧ Sorted (KeyLe proj) A ∧ Sorted (KeyLe proj) B ∧
    Sorted (KeyLe proj) Q ∧
    AllLe (KeyLe proj) P (A ++ B ++ Q) ∧
    AllLe (KeyLe proj) (P ++ A ++ B) Q ∧
    List.Perm (P ++ A ++ B ++ Q) ((l0.drop first0).take (last0 - first0)) ∧
    first ≤ mid ∧ mid ≤ last

/-- C++'s `inplace_merge_with_rotation` loop. Each turn rotates the block of the
"other" run that must cross the current element in front of it, then advances the
finalized boundary past that block and one more element. -/
def mergeLoop (proj : α → β) : Nat → List α → Nat → Nat → Nat → List α
  | 0, l, _, _, _ => l
  | fuel + 1, l, first, mid, last =>
      if _ : first < mid ∧ mid < last then
        if _ : mid - first < last - mid then
          if hf : first < l.length then
            let sp := scanRight proj l[first] (last - mid) l mid last
            mergeLoop proj fuel (rotRange l first mid sp) (first + (sp - mid) + 1) sp last
          else l
        else
          if hl : last - 1 < l.length then
            let sp := scanLeft proj l[last - 1] (mid - first) l mid first
            mergeLoop proj fuel (rotRange l sp mid last) first sp (last - (mid - sp) - 1)
          else l
      else l

/-- C++'s `inplace_merge_with_rotation` on the whole list. -/
def mergeByRotation (proj : α → β) (l : List α) (first mid last : Nat) : List α :=
  mergeLoop proj (last - first) l first mid last

/-- One turn of the left-turning branch: rotate the block of the right run that
lies below the current left element in front of the left run, then move the
finalized boundary past that block and that element. -/
theorem rotInv_step_left {proj : α → β} {l0 l : List α} {first0 last0 first mid last sp : Nat}
    (hl0 : last0 ≤ l0.length) (hinv : RotInv proj l0 first0 last0 l first mid last)
    (hlastle : last ≤ l.length)
    (hfm : first < mid) (hsp1 : mid ≤ sp) (hsp2 : sp ≤ last)
    (hblt : ∀ b ∈ (l.drop mid).take (sp - mid),
      Cmp.blt (proj b) (proj (l[first]'(by omega))) = true)
    (hstop : ∀ (_hsp : sp < last),
      Cmp.blt (proj (l[sp]'(by omega))) (proj (l[first]'(by omega))) = false) :
    RotInv proj l0 first0 last0 (rotRange l first mid sp) (first + (sp - mid) + 1) sp last := by
  obtain ⟨P, A, B, Q, hdecomp, hA, hB, hfirst, hmid, hlast, hlast0, hlastle', hsortP, hsortA,
    hsortB, hsortQ, hleP, hleQ, hperm, hflm, hhml⟩ := hinv
  have hfirst0le : first0 ≤ l0.length := by omega
  have hmB : sp - mid ≤ B.length := by omega
  have hAne : A ≠ [] := by
    intro hnil
    rw [hnil] at hmid
    simp at hmid
    omega
  obtain ⟨a, A', hAcons⟩ := List.exists_cons_of_ne_nil hAne
  have haA : a ∈ A := by rw [hAcons]; exact List.mem_cons_self
  have hlfirst : l[first]? = some a := by
    have h1 : ((l.drop first).take (mid - first))[0]? = (l.drop first)[0]? := by
      rw [List.getElem?_take, ite_eq_left (by omega : 0 < mid - first)]
    have h2 : ((l.drop first).take (mid - first))[0]? = some a := by
      rw [← hA, hAcons]
      rfl
    rw [List.getElem?_drop, Nat.add_zero] at h1
    exact h1.symm.trans h2
  have haeq : a = l[first]'(by omega) := ((List.getElem?_eq_some_iff.mp hlfirst).2).symm
  have hB'take : B.take (sp - mid) = (l.drop mid).take (sp - mid) := by
    rw [hB, List.take_take, Nat.min_eq_left (by omega : sp - mid ≤ last - mid)]
  have hblt' : ∀ b ∈ B.take (sp - mid), Cmp.blt (proj b) (proj a) = true := by
    intro b hb
    have hb' : b ∈ (l.drop mid).take (sp - mid) := by rwa [hB'take] at hb
    have hh := hblt b hb'
    rwa [← haeq] at hh
  have hXlen : (l0.take first0 ++ P).length = first := by
    rw [List.length_append, List.length_take, Nat.min_eq_left hfirst0le, hfirst]
  have hA'len : A'.length + 1 = A.length := by rw [hAcons]; rfl
  have hXlen2 : (l0.take first0 ++ P).length + (a :: A').length = mid := by
    rw [hXlen, ← hAcons, hmid]
  have hXlen3 : (l0.take first0 ++ P).length + (a :: A').length + (B.take (sp - mid)).length
      = sp := by
    rw [hXlen2, List.length_take, Nat.min_eq_left hmB]
    omega
  have hl'mid : l = (l0.take first0 ++ P) ++ (a :: A') ++
      (B.take (sp - mid) ++ B.drop (sp - mid)) ++ (Q ++ l0.drop last0) := by
    rw [hdecomp, hAcons]
    rw [List.take_append_drop]
    simp only [List.append_assoc]
  have hl' : l = (l0.take first0 ++ P) ++ (a :: A') ++ (B.take (sp - mid)) ++
      (B.drop (sp - mid) ++ Q ++ l0.drop last0) := by
    rw [hl'mid]
    simp only [List.append_assoc]
  have hdecomp' : rotRange l first mid sp =
      l0.take first0 ++ (P ++ B.take (sp - mid) ++ [a]) ++ A' ++
        B.drop (sp - mid) ++ Q ++ l0.drop last0 := by
    have hrot := rotRange_append (l0.take first0 ++ P) (a :: A') (B.take (sp - mid))
      (B.drop (sp - mid) ++ Q ++ l0.drop last0)
    rw [← hl', hXlen3, hXlen2, hXlen] at hrot
    rw [hrot]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  have hnewA : A' = ((rotRange l first mid sp).drop (first + (sp - mid) + 1)).take
      (sp - (first + (sp - mid) + 1)) := by
    have hXA : (l0.take first0 ++ (P ++ B.take (sp - mid) ++ [a])).length
        = first + (sp - mid) + 1 := by
      simp only [List.length_append, List.length_take, List.length_singleton,
        Nat.min_eq_left hfirst0le, Nat.min_eq_left hmB]
      omega
    have hSA : A'.length = sp - (first + (sp - mid) + 1) := by omega
    have hthis := drop_take_of_append3
      (X := l0.take first0 ++ (P ++ B.take (sp - mid) ++ [a])) (S := A')
      (Y1 := B.drop (sp - mid)) (Y2 := Q) (Y3 := l0.drop last0)
      (lo := first + (sp - mid) + 1) (hi := sp) hXA hSA
    rw [hdecomp']
    exact hthis.symm
  have hnewB : B.drop (sp - mid) = ((rotRange l first mid sp).drop sp).take (last - sp) := by
    have hXB : ((l0.take first0 ++ (P ++ B.take (sp - mid) ++ [a])) ++ A').length = sp := by
      simp only [List.length_append, List.length_take, List.length_singleton,
        Nat.min_eq_left hfirst0le, Nat.min_eq_left hmB]
      omega
    have hSB : (B.drop (sp - mid)).length = last - sp := by
      rw [List.length_drop, hlast]
      omega
    have hthis := drop_take_of_append2
      (X := (l0.take first0 ++ (P ++ B.take (sp - mid) ++ [a])) ++ A')
      (S := B.drop (sp - mid)) (Y1 := Q) (Y2 := l0.drop last0) (lo := sp) (hi := last) hXB hSB
    rw [hdecomp']
    exact hthis.symm
  have hlen' : (rotRange l first mid sp).length = l.length :=
    rotRange_length (by omega) (by omega) (by omega)
  have hmidperm : List.Perm ((P ++ B.take (sp - mid) ++ [a]) ++ A' ++ B.drop (sp - mid))
      (P ++ A ++ B) := by
    have hrot : List.Perm (P ++ (B.take (sp - mid) ++ a :: A') ++ B.drop (sp - mid))
        (P ++ (a :: A') ++ B.take (sp - mid) ++ B.drop (sp - mid)) := by
      have h1 : List.Perm (B.take (sp - mid) ++ a :: A') (a :: (A' ++ B.take (sp - mid))) :=
        perm_rotate_cons a A' (B.take (sp - mid))
      have h3 := List.Perm.append_right (B.drop (sp - mid)) (List.Perm.append_left P h1)
      simp only [List.append_assoc, List.cons_append] at h3 ⊢
      exact h3
    have heq1 : (P ++ B.take (sp - mid) ++ [a]) ++ A' ++ B.drop (sp - mid)
        = P ++ (B.take (sp - mid) ++ a :: A') ++ B.drop (sp - mid) := by
      simp only [List.append_assoc, List.cons_append, List.nil_append]
    have heq2 : P ++ (a :: A') ++ B.take (sp - mid) ++ B.drop (sp - mid) = P ++ A ++ B := by
      rw [hAcons]
      simp only [List.append_assoc, List.cons_append]
      rw [List.take_append_drop]
    exact (List.Perm.of_eq heq1).trans (hrot.trans (List.Perm.of_eq heq2))
  have hlePQ : AllLe (KeyLe proj) P Q :=
    allLe_of_subset_left hleQ (fun z hz => List.mem_append_left _ (List.mem_append_left _ hz))
  have hleBQ : AllLe (KeyLe proj) B Q :=
    allLe_of_subset_left hleQ (fun z hz => List.mem_append_right _ hz)
  have hlePA : AllLe (KeyLe proj) P A :=
    allLe_of_subset_right hleP (fun z hz => List.mem_append_left _ (List.mem_append_left _ hz))
  have hlePB : AllLe (KeyLe proj) P B :=
    allLe_of_subset_right hleP (fun z hz => List.mem_append_left _ (List.mem_append_right _ hz))
  have hsortedAcons : Sorted (KeyLe proj) (a :: A') := by rwa [← hAcons]
  have haA' : ∀ z ∈ A', KeyLe proj a z := (List.pairwise_cons.mp hsortedAcons).1
  have hA'drop : A' = A.drop 1 := by rw [hAcons]; rfl
  have hB''ok : ∀ z ∈ B.drop (sp - mid), KeyLe proj a z := by
    by_cases hsp : sp < last
    · have hBm : B[sp - mid]'(by omega) = l[sp]'(by omega) := by
        have h1 : B[sp - mid]? = some (B[sp - mid]'(by omega)) :=
          List.getElem?_eq_getElem (by omega)
        have h2 : B[sp - mid]? = l[sp]? := by
          rw [hB, List.getElem?_take, ite_eq_left (by omega), List.getElem?_drop,
            show mid + (sp - mid) = sp by omega]
        rw [h2, List.getElem?_eq_getElem (by omega : sp < l.length)] at h1
        exact (Option.some.inj h1).symm
      have hle : KeyLe proj a (l[sp]'(by omega)) := by
        rw [haeq]
        exact ble_of_not_blt (hstop hsp)
      intro z hz
      have hle' : KeyLe proj a (B[sp - mid]'(by omega)) := by rw [← hBm] at hle; exact hle
      exact allLe_head_drop hsortB (by omega) hle' a (List.mem_singleton_self a) z hz
    · have hnil : B.drop (sp - mid) = [] := List.drop_eq_nil_of_le (by omega)
      intro z hz
      rw [hnil] at hz
      exact absurd hz (List.not_mem_nil)
  exact
    ⟨P ++ B.take (sp - mid) ++ [a], A', B.drop (sp - mid), Q, hdecomp', hnewA, hnewB,
      by
        simp only [List.length_append, List.length_take, List.length_singleton, Nat.min_eq_left hmB]
        omega,
      by omega,
      by
        rw [List.length_drop, hlast]
        omega,
      hlast0,
      by rw [hlen']; exact hlastle',
      by
        have hPB : AllLe (KeyLe proj) P (B.take (sp - mid)) := allLe_take_right hlePB
        have hPa : AllLe (KeyLe proj) P [a] := by
          intro p hp z hz
          rw [List.mem_singleton] at hz
          rw [hz]
          exact hleP p hp a (List.mem_append_left _ (List.mem_append_left _ haA))
        have hB'a : AllLe (KeyLe proj) (B.take (sp - mid)) [a] := by
          intro z hz w hw
          rw [List.mem_singleton] at hw
          rw [hw]
          exact Cmp.ble_of_blt (hblt' z hz)
        refine sorted_append ?_ (sorted_singleton _ _) ?_
        · exact sorted_append hsortP (sorted_take hsortB) hPB
        · rw [allLe_append_left]
          exact ⟨hPa, hB'a⟩,
      by
        rw [hA'drop]
        exact sorted_drop hsortA,
      sorted_drop hsortB,
      hsortQ,
      by
        intro p hp z hz
        rcases List.mem_append.mp hp with hp | hpa
        · rcases List.mem_append.mp hp with hpP | hpB
          · rcases List.mem_append.mp hz with hz' | hzQ
            · rcases List.mem_append.mp hz' with hzA | hzB
              · exact hleP p hpP z (List.mem_append_left _ (List.mem_append_left _
                  (mem_of_mem_drop (l := A) (n := 1) (by rwa [hA'drop] at hzA))))
              · exact hleP p hpP z
                  (List.mem_append_left _ (List.mem_append_right _
                    (mem_of_mem_drop (l := B) (n := sp - mid) hzB)))
            · exact hleP p hpP z (List.mem_append_right _ hzQ)
          · rcases List.mem_append.mp hz with hz' | hzQ
            · rcases List.mem_append.mp hz' with hzA | hzB
              · exact Cmp.ble_trans (Cmp.ble_of_blt (hblt' p hpB)) (haA' z hzA)
              · exact allLe_take_drop_of_sorted hsortB p hpB z hzB
            · exact hleBQ p (List.mem_of_mem_take hpB) z hzQ
        · rw [List.mem_singleton] at hpa
          rw [hpa]
          rcases List.mem_append.mp hz with hz' | hzQ
          · rcases List.mem_append.mp hz' with hzA | hzB
            · exact haA' z hzA
            · exact hB''ok z hzB
          · exact hleQ a (List.mem_append_left _ (List.mem_append_right _ haA)) z hzQ,
      by
        intro p hp z hz
        rcases List.mem_append.mp hp with hp | hpB''
        · rcases List.mem_append.mp hp with hp' | hpA
          · rcases List.mem_append.mp hp' with hpPB | hpa
            · rcases List.mem_append.mp hpPB with hpP | hpB
              · exact hlePQ p hpP z hz
              · exact hleBQ p (List.mem_of_mem_take hpB) z hz
            · rw [List.mem_singleton] at hpa
              rw [hpa]
              exact hleQ a (List.mem_append_left _ (List.mem_append_right _ haA)) z hz
          · exact hleQ p (List.mem_append_left _ (List.mem_append_right _
              (mem_of_mem_drop (l := A) (n := 1) (by rwa [hA'drop] at hpA)))) z hz
        · exact hleBQ p (mem_of_mem_drop (l := B) (n := sp - mid) hpB'') z hz,
      (List.Perm.append_right Q hmidperm).trans hperm,
      by omega,
      hsp2⟩

end Tcs

namespace Tcs

variable {α : Type u} {β : Type v} [Cmp β]

/-- Arithmetic bookkeeping for the rotation invariants.  These are kept as
separate lemmas with purely `Nat` hypotheses so that `omega` never sees the
surrounding list hypotheses (which would make it fall back on classical
decidability). -/
theorem arith_sp {first sp : Nat} (h : first ≤ sp) : first + (sp - first) = sp :=
  Nat.add_sub_of_le h

theorem arith_hXlen {first0 Plen first sp : Nat} (h : first = first0 + Plen)
    (hsp : first ≤ sp) : first0 + Plen + (sp - first) = sp := by
  rw [← h, Nat.add_sub_of_le hsp]

theorem arith_Xlen2 {first sp mid Alen : Nat} (h1 : first ≤ sp) (h2 : sp ≤ mid)
    (hA : mid - first = Alen) : sp + (Alen - (sp - first)) = mid := by omega

theorem arith_hlast {mid sp last Blen : Nat} (h : sp ≤ mid) (hl : mid ≤ last) (hb : 1 ≤ Blen)
    (hB : last - mid = Blen) : last - (mid - sp) - 1 = sp + (Blen - 1) := by omega

theorem arith_hlast0 {last0 last mid sp Qlen Alen Blen first : Nat}
    (h0 : last0 = last + Qlen) (hB : last - mid = Blen) (hA : mid - first = Alen)
    (h1 : first ≤ sp) (h2 : sp ≤ mid) (hb : 1 ≤ Blen) :
    last0 = last - (mid - sp) - 1 +
      (Blen - (Blen - 1) + (Alen - (sp - first)) + Qlen) := by omega

theorem arith_sp_last {sp mid last : Nat} (h : sp ≤ mid) (hl : mid < last) :
    sp ≤ last - (mid - sp) - 1 := by omega

theorem arith_hlt_last {mid sp last : Nat} (h : mid < last) : last - (mid - sp) - 1 < last := by
  omega

theorem arith_Slen {f0 l0 Plen Alen Blen Qlen first mid last : Nat}
    (h1 : first = f0 + Plen) (h2 : mid = first + Alen) (h3 : last = mid + Blen)
    (h4 : l0 = last + Qlen) : Plen + Alen + Blen + Qlen = l0 - f0 := by omega

theorem arith_prelen {f0 l0 Plen Alen Blen Qlen first mid last : Nat}
    (h1 : first = f0 + Plen) (h2 : mid = first + Alen) (h3 : last = mid + Blen)
    (h4 : l0 = last + Qlen) : f0 + (Plen + Alen + Blen + Qlen) = l0 := by omega

theorem fuel_left {first last fuel nf : Nat} (h : last - first ≤ fuel + 1) (hlt : first < nf) :
    last - nf ≤ fuel := by omega

theorem fuel_right {first last fuel nl : Nat} (h : last - first ≤ fuel + 1) (hlt : nl < last) :
    nl - first ≤ fuel := by omega

/-- Swapping two adjacent blocks of a concatenation. -/
theorem perm_blocks_swap (P A' A'' B' Y Q : List α) :
    List.Perm (P ++ A' ++ B' ++ (Y ++ A'' ++ Q)) (P ++ (A' ++ A'') ++ (B' ++ Y) ++ Q) := by
  have h : List.Perm (B' ++ (Y ++ (A'' ++ Q))) (A'' ++ ((B' ++ Y) ++ Q)) := by
    have e1 : B' ++ (Y ++ (A'' ++ Q)) = (B' ++ Y) ++ (A'' ++ Q) :=
      (List.append_assoc B' Y (A'' ++ Q)).symm
    have e2 : (B' ++ Y) ++ (A'' ++ Q) = ((B' ++ Y) ++ A'') ++ Q :=
      (List.append_assoc (B' ++ Y) A'' Q).symm
    have e4 : (A'' ++ (B' ++ Y)) ++ Q = A'' ++ ((B' ++ Y) ++ Q) :=
      List.append_assoc A'' (B' ++ Y) Q
    exact ((List.Perm.of_eq e1).trans (List.Perm.of_eq e2)).trans
      ((List.Perm.append_right Q (List.perm_append_comm (l₁ := B' ++ Y) (l₂ := A''))).trans
        (List.Perm.of_eq e4))
  have h2 : List.Perm ((P ++ A') ++ (B' ++ (Y ++ (A'' ++ Q))))
      ((P ++ A') ++ (A'' ++ ((B' ++ Y) ++ Q))) :=
    List.Perm.append_left (P ++ A') h
  simp only [List.append_assoc] at h2 ⊢
  exact h2

/-- One turn of the right-turning branch: rotate the suffix of the left run that
lies above the last right element behind the right run, then move the finalized
boundary back past that suffix and that element. -/
theorem rotInv_step_right {proj : α → β} {l0 l : List α} {first0 last0 first mid last sp : Nat}
    (hl0 : last0 ≤ l0.length) (hinv : RotInv proj l0 first0 last0 l first mid last)
    (hlastle : last ≤ l.length)
    (hfm : first < mid) (hml : mid < last) (hsp1 : first ≤ sp) (hsp2 : sp ≤ mid)
    (hblt : ∀ b ∈ (l.drop sp).take (mid - sp),
      Cmp.blt (proj (l[last - 1]'(by omega))) (proj b) = true)
    (hstop : ∀ (_hsp : first < sp),
      Cmp.blt (proj (l[last - 1]'(by omega))) (proj (l[sp - 1]'(by omega))) = false) :
    RotInv proj l0 first0 last0 (rotRange l sp mid last) first sp (last - (mid - sp) - 1) := by
  obtain ⟨P, A, B, Q, hdecomp, hA, hB, hfirst, hmid, hlast, hlast0, hlastle', hsortP, hsortA,
    hsortB, hsortQ, hleP, hleQ, hperm, hflm, hhml⟩ := hinv
  have hfirst0le : first0 ≤ l0.length := by omega
  have hsubB : last - mid = B.length := by rw [hlast, Nat.add_sub_cancel_left]
  have hsubA : mid - first = A.length := by rw [hmid, Nat.add_sub_cancel_left]
  have hsubQ : last0 - last = Q.length := by rw [hlast0, Nat.add_sub_cancel_left]
  have hmA : sp - first ≤ A.length := by omega
  have hBne : B ≠ [] := by
    intro hnil
    rw [hnil] at hlast
    simp at hlast
    omega
  have hbB : 1 ≤ B.length := by
    cases B with
    | nil => exact absurd rfl hBne
    | cons _ _ => simp
  have hyeq : B[B.length - 1]'(by omega) = l[last - 1]'(by omega) := by
    have hbmid : B.length - 1 < last - mid := by rw [hsubB]; omega
    have h3 : B[B.length - 1]? = ((l.drop mid).take (last - mid))[B.length - 1]? := by rw [hB]
    have h4 : ((l.drop mid).take (last - mid))[B.length - 1]? = l[last - 1]? := by
      rw [List.getElem?_take, ite_eq_left hbmid, List.getElem?_drop,
        show mid + (B.length - 1) = last - 1 by rw [hlast]; omega]
    have h5 : B[B.length - 1]? = some (B[B.length - 1]'(by omega)) :=
      List.getElem?_eq_getElem (by omega)
    have h6 : l[last - 1]? = some (l[last - 1]'(by omega)) :=
      List.getElem?_eq_getElem (by omega)
    rw [h3, h4, h6] at h5
    exact (Option.some.inj h5).symm
  have hAdrop : A.drop (sp - first) = (l.drop sp).take (mid - sp) := by
    rw [hA, drop_take', List.drop_drop, show first + (sp - first) = sp by omega,
      show mid - first - (sp - first) = mid - sp by omega]
  have hblt' : ∀ b ∈ A.drop (sp - first),
      Cmp.blt (proj (l[last - 1]'(by omega))) (proj b) = true := by
    intro b hb
    have hb' : b ∈ (l.drop sp).take (mid - sp) := by rwa [hAdrop] at hb
    exact hblt b hb'
  have hAeq : first < sp → A[sp - first - 1]'(by omega) = l[sp - 1]'(by omega) := by
    intro hsp
    have hcond : sp - first - 1 < mid - first := by rw [hsubA]; omega
    have h3 : A[sp - first - 1]? = ((l.drop first).take (mid - first))[sp - first - 1]? := by
      rw [hA]
    have h4 : ((l.drop first).take (mid - first))[sp - first - 1]? = l[sp - 1]? := by
      rw [List.getElem?_take, ite_eq_left hcond, List.getElem?_drop,
        show first + (sp - first - 1) = sp - 1 by omega]
    have h5 : A[sp - first - 1]? = some (A[sp - first - 1]'(by omega)) :=
      List.getElem?_eq_getElem (by omega)
    have h6 : l[sp - 1]? = some (l[sp - 1]'(by omega)) :=
      List.getElem?_eq_getElem (by omega)
    rw [h3, h4, h6] at h5
    exact (Option.some.inj h5).symm
  have hYeq : B.drop (B.length - 1) = [l[last - 1]'(by omega)] := by
    have hlen : (B.drop (B.length - 1)).length = 1 := by
      rw [List.length_drop, Nat.sub_sub_self hbB]
    obtain ⟨c, hc⟩ := List.length_eq_one_iff.mp hlen
    have hmem : B[B.length - 1]'(by omega) ∈ B.drop (B.length - 1) := by
      rw [List.mem_iff_getElem?]
      refine ⟨0, ?_⟩
      rw [List.getElem?_drop, Nat.add_zero]
      exact List.getElem?_eq_getElem (by omega)
    rw [hc, List.mem_singleton] at hmem
    rw [hc, ← hmem, hyeq]
  have hYA'' : AllLe (KeyLe proj) (B.drop (B.length - 1)) (A.drop (sp - first)) := by
    intro z hz w hw
    rw [hYeq, List.mem_singleton] at hz
    rw [hz]
    exact Cmp.ble_of_blt (hblt' w hw)
  have hA'Y : AllLe (KeyLe proj) (A.take (sp - first)) (B.drop (B.length - 1)) := by
    intro z hz w hw
    rw [hYeq, List.mem_singleton] at hw
    rw [hw]
    by_cases hsp : first < sp
    · have hle : KeyLe proj (A[sp - first - 1]'(by omega)) (l[last - 1]'(by omega)) := by
        rw [hAeq hsp]
        exact ble_of_not_blt (hstop hsp)
      exact allLe_take_last_le hsortA (Nat.sub_pos_of_lt hsp) hmA hle z hz
        (l[last - 1]'(by omega)) (List.mem_singleton_self _)
    · have hsp_eq : sp = first := Nat.le_antisymm (Nat.le_of_not_lt hsp) hsp1
      rw [hsp_eq, Nat.sub_self, List.take_zero] at hz
      exact absurd hz (List.not_mem_nil)
  -- the rotated list, split at the run boundary
  have hXlen : ((l0.take first0 ++ P) ++ A.take (sp - first)).length = sp := by
    simp only [List.length_append, List.length_take, Nat.min_eq_left hfirst0le,
      Nat.min_eq_left hmA]
    exact arith_hXlen hfirst hsp1
  have hXlen2 : ((l0.take first0 ++ P) ++ A.take (sp - first)).length
      + (A.drop (sp - first)).length = mid := by
    rw [hXlen]
    simp only [List.length_drop]
    exact arith_Xlen2 hsp1 hsp2 hsubA
  have hXlen3 : ((l0.take first0 ++ P) ++ A.take (sp - first)).length
      + (A.drop (sp - first)).length + B.length = last := by
    rw [hXlen2]
    exact hlast.symm
  have hl'mid : ((l0.take first0 ++ P) ++ (A.take (sp - first) ++ A.drop (sp - first))) ++
      B ++ (Q ++ l0.drop last0) = l := by
    rw [List.take_append_drop]
    simp only [List.append_assoc]
    rw [show l0.take first0 ++ (P ++ (A ++ (B ++ (Q ++ l0.drop last0))))
        = l0.take first0 ++ P ++ A ++ B ++ Q ++ l0.drop last0 by simp only [List.append_assoc]]
    exact hdecomp.symm
  have hl' : l = ((l0.take first0 ++ P) ++ A.take (sp - first)) ++ A.drop (sp - first) ++ B ++
      (Q ++ l0.drop last0) := by
    rw [← hl'mid]
    simp only [List.append_assoc]
  have hrot := rotRange_append ((l0.take first0 ++ P) ++ A.take (sp - first))
    (A.drop (sp - first)) B (Q ++ l0.drop last0)
  rw [← hl', hXlen3, hXlen2, hXlen] at hrot
  have hdecomp' : rotRange l sp mid last =
      l0.take first0 ++ P ++ A.take (sp - first) ++ B.take (B.length - 1) ++
        (B.drop (B.length - 1) ++ A.drop (sp - first) ++ Q) ++ l0.drop last0 := by
    have hsplit : ((l0.take first0 ++ P) ++ A.take (sp - first)) ++
        (B.take (B.length - 1) ++ B.drop (B.length - 1)) ++ A.drop (sp - first) ++
          (Q ++ l0.drop last0)
        = ((l0.take first0 ++ P) ++ A.take (sp - first)) ++ B ++ A.drop (sp - first) ++
          (Q ++ l0.drop last0) := by
      rw [List.take_append_drop]
    rw [hrot, ← hsplit]
    simp only [List.append_assoc]
  have hnewA : A.take (sp - first) =
      ((rotRange l sp mid last).drop first).take (sp - first) := by
    have hXA : (l0.take first0 ++ P).length = first := by
      simp only [List.length_append, List.length_take, Nat.min_eq_left hfirst0le]
      exact hfirst.symm
    have hSA : (A.take (sp - first)).length = sp - first := by
      rw [List.length_take]
      exact Nat.min_eq_left hmA
    have hthis := drop_take_of_append3 (X := l0.take first0 ++ P) (S := A.take (sp - first))
      (Y1 := B.take (B.length - 1)) (Y2 := B.drop (B.length - 1) ++ A.drop (sp - first) ++ Q)
      (Y3 := l0.drop last0) (lo := first) (hi := sp) hXA hSA
    rw [hdecomp']
    exact hthis.symm
  have hnewB : B.take (B.length - 1) =
      ((rotRange l sp mid last).drop sp).take (last - (mid - sp) - 1 - sp) := by
    have hXB : ((l0.take first0 ++ P) ++ A.take (sp - first)).length = sp := hXlen
    have hSB : (B.take (B.length - 1)).length = last - (mid - sp) - 1 - sp := by
      rw [List.length_take]
      have : B.length - 1 ≤ B.length := by omega
      rw [Nat.min_eq_left (by omega)]
      omega
    have hthis := drop_take_of_append2
      (X := (l0.take first0 ++ P) ++ A.take (sp - first)) (S := B.take (B.length - 1))
      (Y1 := B.drop (B.length - 1) ++ A.drop (sp - first) ++ Q) (Y2 := l0.drop last0)
      (lo := sp) (hi := last - (mid - sp) - 1) hXB hSB
    rw [hdecomp']
    exact hthis.symm
  have hlen' : (rotRange l sp mid last).length = l.length :=
    rotRange_length (by omega) (by omega) (by omega)
  have hyY : l[last - 1]'(by omega) ∈ B.drop (B.length - 1) := by
    rw [hYeq]
    exact List.mem_singleton_self _
  have hleP1 : AllLe (KeyLe proj) P
      (A.take (sp - first) ++ B.take (B.length - 1) ++
        (B.drop (B.length - 1) ++ A.drop (sp - first) ++ Q)) := by
    intro p hp z hz
    rcases List.mem_append.mp hz with hz1 | hzQ
    · rcases List.mem_append.mp hz1 with hzA | hzB
      · exact hleP p hp z (List.mem_append_left _ (List.mem_append_left _
          (List.mem_of_mem_take hzA)))
      · exact hleP p hp z (List.mem_append_left _ (List.mem_append_right _
          (List.mem_of_mem_take hzB)))
    · rcases List.mem_append.mp hzQ with hzYA | hzQ''
      · rcases List.mem_append.mp hzYA with hzY | hzA''
        · exact hleP p hp z (List.mem_append_left _ (List.mem_append_right _
            (mem_of_mem_drop (l := B) (n := B.length - 1) hzY)))
        · exact hleP p hp z (List.mem_append_left _ (List.mem_append_left _
            (mem_of_mem_drop (l := A) (n := sp - first) hzA'')))
      · exact hleP p hp z (List.mem_append_right _ hzQ'')
  have hleQ1 : AllLe (KeyLe proj)
      (P ++ A.take (sp - first) ++ B.take (B.length - 1))
      (B.drop (B.length - 1) ++ A.drop (sp - first) ++ Q) := by
    intro p hp z hz
    have hTA : p ∈ A -> KeyLe proj p z -> KeyLe proj p z := fun _ h => h
    rcases List.mem_append.mp hz with hz1 | hzQ
    · rcases List.mem_append.mp hz1 with hzY | hzA''
      · rcases List.mem_append.mp hp with hp' | hpB'
        · rcases List.mem_append.mp hp' with hpP | hpA'
          · exact hleP p hpP z (List.mem_append_left _ (List.mem_append_right _
              (mem_of_mem_drop (l := B) (n := B.length - 1) hzY)))
          · exact hA'Y p hpA' z hzY
        · exact allLe_take_drop_of_sorted hsortB p hpB' z hzY
      · rcases List.mem_append.mp hp with hp' | hpB'
        · rcases List.mem_append.mp hp' with hpP | hpA'
          · exact hleP p hpP z (List.mem_append_left _ (List.mem_append_left _
              (mem_of_mem_drop (l := A) (n := sp - first) hzA'')))
          · exact allLe_take_drop_of_sorted hsortA p hpA' z hzA''
        · exact Cmp.ble_trans (allLe_take_drop_of_sorted hsortB p hpB' (l[last - 1]'(by omega)) hyY)
            (hYA'' (l[last - 1]'(by omega)) hyY z hzA'')
    · rcases List.mem_append.mp hp with hp' | hpB'
      · rcases List.mem_append.mp hp' with hpP | hpA'
        · exact hleP p hpP z (List.mem_append_right _ hzQ)
        · exact hleQ p (List.mem_append_left _ (List.mem_append_right _
            (List.mem_of_mem_take hpA'))) z hzQ
      · exact hleQ p (List.mem_append_right _ (List.mem_of_mem_take hpB')) z hzQ
  exact
    ⟨P, A.take (sp - first), B.take (B.length - 1),
      B.drop (B.length - 1) ++ A.drop (sp - first) ++ Q, hdecomp', hnewA, hnewB,
      hfirst,
      by
        simp only [List.length_take, Nat.min_eq_left hmA]
        exact (arith_sp hsp1).symm,
      by
        simp only [List.length_take]
        rw [Nat.min_eq_left (Nat.sub_le _ _)]
        exact arith_hlast hsp2 (Nat.le_of_lt hml) hbB hsubB,
      by
        rw [List.length_append, List.length_append, List.length_drop, List.length_drop]
        exact arith_hlast0 hlast0 hsubB hsubA hsp1 hsp2 hbB,
      by rw [hlen']; exact Nat.le_trans (Nat.sub_le _ _) (Nat.le_trans (Nat.sub_le _ _) hlastle'),
      hsortP,
      sorted_take hsortA,
      sorted_take hsortB,
      by
        have h1 : Sorted (KeyLe proj) ([l[last - 1]'(by omega)] ++ A.drop (sp - first)) :=
          sorted_append (sorted_singleton _ _) (sorted_drop hsortA) (by
            rw [← hYeq]
            exact hYA'')
        have h2 : AllLe (KeyLe proj) ([l[last - 1]'(by omega)] ++ A.drop (sp - first)) Q :=
          allLe_append_left.mpr
            ⟨allLe_of_subset_left hleQ (fun z hz =>
                List.mem_append_right (as := P ++ A)
                  (mem_of_mem_drop (l := B) (n := B.length - 1) (by rwa [← hYeq] at hz))),
             allLe_of_subset_left hleQ (fun z hz =>
                List.mem_append_left (bs := B)
                  (List.mem_append_right (as := P)
                    (mem_of_mem_drop (l := A) (n := sp - first) hz)))⟩
        rw [hYeq]
        exact sorted_append h1 hsortQ h2,
      hleP1,
      hleQ1,
      by
        have hsplit : P ++ (A.take (sp - first) ++ A.drop (sp - first)) ++
            (B.take (B.length - 1) ++ B.drop (B.length - 1)) ++ Q = P ++ A ++ B ++ Q := by
          rw [List.take_append_drop, List.take_append_drop]
        exact (perm_blocks_swap P (A.take (sp - first)) (A.drop (sp - first))
          (B.take (B.length - 1)) (B.drop (B.length - 1)) Q).trans
          ((List.Perm.of_eq hsplit).trans hperm),
      hsp1,
      arith_sp_last hsp2 hml⟩

/-! ### Correctness of `inplace_merge_with_rotation` -/

theorem mergeLoop_spec (proj : α → β) (l0 : List α) {first0 last0 : Nat}
    (hl0 : last0 ≤ l0.length) :
    ∀ fuel l first mid last, last - first ≤ fuel →
      RotInv proj l0 first0 last0 l first mid last →
      ∃ l' first' mid' last', mergeLoop proj fuel l first mid last = l' ∧
        RotInv proj l0 first0 last0 l' first' mid' last' ∧
        ¬(first' < mid' ∧ mid' < last') := by
  intro fuel
  induction fuel with
  | zero =>
    intro l first mid last hfuel hinv
    refine ⟨l, first, mid, last, mergeLoop.eq_1 proj l first mid last, hinv, ?_⟩
    rintro ⟨h1, h2⟩
    omega
  | succ fuel ih =>
    intro l first mid last hfuel hinv
    obtain ⟨P, A, B, Q, hdecomp, hA, hB, hfirst, hmid, hlast, hlast0, hlastle, hsortP, hsortA,
      hsortB, hsortQ, hleP, hleQ, hperm, hflm, hhml⟩ := hinv
    have hinit : RotInv proj l0 first0 last0 l first mid last :=
      ⟨P, A, B, Q, hdecomp, hA, hB, hfirst, hmid, hlast, hlast0, hlastle, hsortP, hsortA,
        hsortB, hsortQ, hleP, hleQ, hperm, hflm, hhml⟩
    rw [mergeLoop.eq_2]
    by_cases hg : first < mid ∧ mid < last
    · rw [dite_eq_left hg]
      have hfirstlen : first < l.length := by omega
      by_cases hlr : mid - first < last - mid
      · rw [dite_eq_left hlr, dite_eq_left hfirstlen]
        obtain ⟨hs1, hs2, hs3, hs4⟩ :=
          scanRight_spec proj (l[first]) (last - mid) l mid last (by omega) (by omega)
        have hblt : ∀ b ∈ (l.drop mid).take
            (scanRight proj (l[first]) (last - mid) l mid last - mid),
            Cmp.blt (proj b) (proj (l[first]'(by omega))) = true :=
          blt_of_mem_drop_take (lo := mid)
            (fun k hk hk1 hk2 => hs3 k hk hk1 (by
              rw [Nat.add_sub_of_le hs1] at hk2
              exact hk2))
        have hstop : ∀ (_hsp : scanRight proj (l[first]) (last - mid) l mid last < last),
            Cmp.blt (proj (l[scanRight proj (l[first]) (last - mid) l mid last]'(by omega)))
              (proj (l[first]'(by omega))) = false := by
          intro hsp
          exact hs4 hsp (l[scanRight proj (l[first]) (last - mid) l mid last]'(by omega))
            (List.getElem?_eq_getElem (by omega))
        have hfuel' : last - (first + (scanRight proj (l[first]) (last - mid) l mid last - mid) + 1)
            ≤ fuel :=
          fuel_left hfuel (Nat.lt_succ_of_le (Nat.le.intro rfl))
        have hinv' : RotInv proj l0 first0 last0
            (rotRange l first mid (scanRight proj (l[first]) (last - mid) l mid last))
            (first + (scanRight proj (l[first]) (last - mid) l mid last - mid) + 1)
            (scanRight proj (l[first]) (last - mid) l mid last) last :=
          rotInv_step_left hl0 hinit hlastle hg.1 hs1 hs2 hblt hstop
        obtain ⟨l', f', m', la', hstep, hinv'', hdone⟩ := ih _ _ _ _ hfuel' hinv'
        exact ⟨l', f', m', la', hstep, hinv'', hdone⟩
      · rw [dite_eq_right hlr]
        have hll : last - 1 < l.length := by omega
        rw [dite_eq_left hll]
        obtain ⟨hs1, hs2, hs3, hs4⟩ :=
          scanLeft_spec proj (l[last - 1]) (mid - first) l mid first (by omega) (by omega)
        have hblt : ∀ b ∈ (l.drop (scanLeft proj (l[last - 1]) (mid - first) l mid first)).take
            (mid - scanLeft proj (l[last - 1]) (mid - first) l mid first),
            Cmp.blt (proj (l[last - 1]'(by omega))) (proj b) = true :=
          blt_of_mem_drop_take_left (lo := scanLeft proj (l[last - 1]) (mid - first) l mid first)
            (fun k hk hk1 hk2 => hs3 k hk hk1 (by
              rw [Nat.add_sub_of_le hs2] at hk2
              exact hk2))
        have hstop : ∀ (_hsp : first < scanLeft proj (l[last - 1]) (mid - first) l mid first),
            Cmp.blt (proj (l[last - 1]'(by omega)))
              (proj (l[scanLeft proj (l[last - 1]) (mid - first) l mid first - 1]'(by omega))) = false := by
          intro hsp
          exact hs4 hsp
            (l[scanLeft proj (l[last - 1]) (mid - first) l mid first - 1]'(by omega))
            (List.getElem?_eq_getElem (by omega))
        have hfuel' : last - (mid - scanLeft proj (l[last - 1]) (mid - first) l mid first) - 1
            - first ≤ fuel :=
          fuel_right hfuel (arith_hlt_last hg.2)
        have hinv' : RotInv proj l0 first0 last0
            (rotRange l (scanLeft proj (l[last - 1]) (mid - first) l mid first) mid last)
            first (scanLeft proj (l[last - 1]) (mid - first) l mid first)
            (last - (mid - scanLeft proj (l[last - 1]) (mid - first) l mid first) - 1) :=
          rotInv_step_right hl0 hinit hlastle hg.1 hg.2 hs1 hs2 hblt hstop
        obtain ⟨l', f', m', la', hstep, hinv'', hdone⟩ := ih _ _ _ _ hfuel' hinv'
        exact ⟨l', f', m', la', hstep, hinv'', hdone⟩
    · rw [dite_eq_right hg]
      exact ⟨l, first, mid, last, rfl, hinit, hg⟩

/-- The range `[first0, last0)` of a loop state, once the loop has stopped, is
sorted, permuted, and glued between the same prefix and suffix. -/
theorem rotInv_final {proj : α → β} {l0 l : List α} {first0 last0 first mid last : Nat}
    (hl0 : last0 ≤ l0.length) (hinv : RotInv proj l0 first0 last0 l first mid last)
    (hdone : ¬(first < mid ∧ mid < last)) :
    Sorted (KeyLe proj) ((l.drop first0).take (last0 - first0)) ∧
    List.Perm ((l.drop first0).take (last0 - first0)) ((l0.drop first0).take (last0 - first0)) ∧
    l.take first0 = l0.take first0 ∧ l.drop last0 = l0.drop last0 := by
  obtain ⟨P, A, B, Q, hdecomp, hA, hB, hfirst, hmid, hlast, hlast0, hlastle, hsortP, hsortA,
    hsortB, hsortQ, hleP, hleQ, hperm, hflm, hhml⟩ := hinv
  have hff : first0 ≤ l0.length :=
    Nat.le_trans (Nat.le_trans (Nat.le_trans (Nat.le.intro hfirst.symm) hflm) hhml)
      (Nat.le_trans (Nat.le.intro hlast0.symm) hl0)
  have hl : l = l0.take first0 ++ (P ++ A ++ B ++ Q) ++ l0.drop last0 := by
    rw [hdecomp]
    simp only [List.append_assoc]
  have hXlen : (l0.take first0).length = first0 := by
    rw [List.length_take, Nat.min_eq_left hff]
  have hSlen : (P ++ A ++ B ++ Q).length = last0 - first0 := by
    simp only [List.length_append]
    exact arith_Slen hfirst hmid hlast hlast0
  have htake : (l.drop first0).take (last0 - first0) = P ++ A ++ B ++ Q := by
    rw [hl]
    exact drop_take_of_append (X := l0.take first0) (S := P ++ A ++ B ++ Q)
      (Y := l0.drop last0) (lo := first0) (hi := last0) hXlen hSlen
  have hpre : l.take first0 = l0.take first0 := by
    rw [hl, List.append_assoc]
    exact take_append_of_len hXlen
  have hpost : l.drop last0 = l0.drop last0 := by
    rw [hl]
    exact drop_append_of_len (by
      simp only [List.length_append]
      rw [hXlen]
      exact arith_prelen hfirst hmid hlast hlast0)
  refine ⟨?_, ?_, hpre, hpost⟩
  · rw [htake]
    rcases Nat.lt_or_ge first mid with hlt | hge
    · have hmidlast : mid = last :=
        Nat.le_antisymm hhml (Nat.le_of_not_lt (fun h => hdone ⟨hlt, h⟩))
      have hBnil : B = [] := by
        have h0 : B.length = 0 := by omega
        exact List.length_eq_zero_iff.mp h0
      have hleP' : AllLe (KeyLe proj) P (A ++ Q) := by
        have h := hleP
        rw [hBnil, List.append_nil] at h
        exact h
      have hleQ' : AllLe (KeyLe proj) (P ++ A) Q := by
        have h := hleQ
        rw [hBnil, List.append_nil] at h
        exact h
      rw [hBnil, List.append_nil]
      exact sorted_append
        (sorted_append hsortP hsortA (allLe_of_subset_right hleP' (fun z hz => List.mem_append_left _ hz)))
        hsortQ
        hleQ'
    · have hfmeq : first = mid := Nat.le_antisymm hflm hge
      have hAnil : A = [] := by
        have h0 : A.length = 0 := by omega
        exact List.length_eq_zero_iff.mp h0
      have hleP' : AllLe (KeyLe proj) P (B ++ Q) := by
        have h := hleP
        rw [hAnil, List.nil_append] at h
        exact h
      have hleQ' : AllLe (KeyLe proj) (P ++ B) Q := by
        have h := hleQ
        rw [hAnil, List.append_nil] at h
        exact h
      rw [hAnil, List.append_nil]
      exact sorted_append
        (sorted_append hsortP hsortB (allLe_of_subset_right hleP' (fun z hz => List.mem_append_left _ hz)))
        hsortQ hleQ'
  · rw [htake]
    exact hperm

theorem mergeByRotation_rotInv (proj : α → β) {l : List α} {first mid last : Nat}
    (hfm : first ≤ mid) (hml : mid ≤ last) (hlast : last ≤ l.length)
    (hsortedA : SortedOn proj l first mid) (hsortedB : SortedOn proj l mid last) :
    ∃ l' first' mid' last', mergeByRotation proj l first mid last = l' ∧
      RotInv proj l first last l' first' mid' last' ∧ ¬(first' < mid' ∧ mid' < last') := by
  have hinit : RotInv proj l first last l first mid last :=
    ⟨[], (l.drop first).take (mid - first), (l.drop mid).take (last - mid), [],
      by
        have h : l.take first ++ ((l.drop first).take (mid - first) ++
            (l.drop mid).take (last - mid)) ++ l.drop last = l := by
          rw [← take_range_split (l := l) hfm hml]
          exact (take_drop_splice (l := l) (lo := first) (hi := last) (by omega)).symm
        refine h.symm.trans ?_
        simp only [List.append_assoc, List.nil_append],
      rfl, rfl,
      by simp,
      by
        have h : mid - first ≤ (l.drop first).length := by
          rw [List.length_drop]
          omega
        rw [List.length_take, Nat.min_eq_left h]
        omega,
      by
        have h : last - mid ≤ (l.drop mid).length := by
          rw [List.length_drop]
          omega
        rw [List.length_take, Nat.min_eq_left h]
        omega,
      by simp,
      hlast,
      sorted_nil _, hsortedA, hsortedB, sorted_nil _, allLe_nil_left,
      allLe_nil_right,
      List.Perm.of_eq (by
        rw [List.nil_append, List.append_nil]
        exact (take_range_split (l := l) hfm hml).symm),
      hfm, hml⟩
  obtain ⟨l', f', m', la', hstep, hinv', hdone⟩ :=
    mergeLoop_spec proj l hlast (last - first) l first mid last (by omega) hinit
  exact ⟨l', f', m', la', by rw [mergeByRotation]; exact hstep, hinv', hdone⟩

/-- **`inplace_merge_with_rotation` sorts the range `[first, last)`.** -/
theorem mergeByRotation_sorted (proj : α → β) {l : List α} {first mid last : Nat}
    (hfm : first ≤ mid) (hml : mid ≤ last) (hlast : last ≤ l.length)
    (hsortedA : SortedOn proj l first mid) (hsortedB : SortedOn proj l mid last) :
    SortedOn proj (mergeByRotation proj l first mid last) first last := by
  obtain ⟨l', f', m', la', hstep, hinv', hdone⟩ :=
    mergeByRotation_rotInv proj hfm hml hlast hsortedA hsortedB
  rw [hstep]
  exact (rotInv_final hlast hinv' hdone).1

/-- The range is permuted by the rotation merge. -/
theorem mergeByRotation_range_perm (proj : α → β) {l : List α} {first mid last : Nat}
    (hfm : first ≤ mid) (hml : mid ≤ last) (hlast : last ≤ l.length)
    (hsortedA : SortedOn proj l first mid) (hsortedB : SortedOn proj l mid last) :
    List.Perm (((mergeByRotation proj l first mid last).drop first).take (last - first))
      ((l.drop first).take (last - first)) := by
  obtain ⟨l', f', m', la', hstep, hinv', hdone⟩ :=
    mergeByRotation_rotInv proj hfm hml hlast hsortedA hsortedB
  rw [hstep]
  exact (rotInv_final hlast hinv' hdone).2.1

/-- The whole output list is a permutation of the input. -/
theorem mergeByRotation_perm (proj : α → β) {l : List α} {first mid last : Nat}
    (hfm : first ≤ mid) (hml : mid ≤ last) (hlast : last ≤ l.length)
    (hsortedA : SortedOn proj l first mid) (hsortedB : SortedOn proj l mid last) :
    (mergeByRotation proj l first mid last).Perm l := by
  obtain ⟨l', f', m', la', hstep, hinv', hdone⟩ :=
    mergeByRotation_rotInv proj hfm hml hlast hsortedA hsortedB
  have hres := rotInv_final hlast hinv' hdone
  rw [hstep]
  have h1 : l' = l'.take first ++ (l'.drop first).take (last - first) ++ l'.drop last :=
    take_drop_splice (l := l') (lo := first) (hi := last) (by omega)
  have h2 : l = l.take first ++ (l.drop first).take (last - first) ++ l.drop last :=
    take_drop_splice (l := l) (lo := first) (hi := last) (by omega)
  rw [h1, h2, hres.2.2.1, hres.2.2.2]
  have hperm := List.Perm.append_left (l.take first)
    (List.Perm.append_right (l.drop last) hres.2.1)
  simpa only [List.append_assoc] using hperm

/-- Positions outside `[first, last)` are untouched. -/
theorem mergeByRotation_outside (proj : α → β) {l : List α} {first mid last : Nat}
    (hfm : first ≤ mid) (hml : mid ≤ last) (hlast : last ≤ l.length)
    (hsortedA : SortedOn proj l first mid) (hsortedB : SortedOn proj l mid last) :
    ∀ i, i < first ∨ last ≤ i → (mergeByRotation proj l first mid last)[i]? = l[i]? := by
  obtain ⟨l', f', m', la', hstep, hinv', hdone⟩ :=
    mergeByRotation_rotInv proj hfm hml hlast hsortedA hsortedB
  have hres := rotInv_final hlast hinv' hdone
  rw [hstep]
  intro i hi
  rcases hi with hi | hi
  · exact getElem?_eq_of_take_eq hres.2.2.1 hi
  · exact getElem?_eq_of_drop_eq hres.2.2.2 hi

end Tcs
