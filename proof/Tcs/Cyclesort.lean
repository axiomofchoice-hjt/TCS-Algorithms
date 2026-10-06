/-
  Cycle sort (`include/tcs/cyclesort.hpp`), modelled on `Array` and proved correct.

  The C++ routine is modelled closely: `destination_range` becomes the block of a
  key (see `InBlock`), `std::swap` becomes `Array.swap`, and the `while (true)`
  inner loop becomes a recursion fuelled by the number of unsettled positions.

  The result is `IsSort`: a permutation of the input, sorted by `proj`.
-/
import Tcs.Spec
import Tcs.Perm
import Tcs.Count

namespace Tcs
namespace Cyclesort


/-! ## Destination blocks -/

variable {α : Type u} {β : Type v} [Cmp β]

/-- Number of keys strictly below `k`: the first position of `k`'s block. -/
def ltCount (proj : α → β) (a : Array α) (k : β) : Nat :=
  a.toList.countP (fun x => Cmp.blt (proj x) k)

/-- Number of keys equal to `k`: the width of `k`'s block. -/
def eqCount (proj : α → β) (a : Array α) (k : β) : Nat :=
  a.toList.countP (fun x => Cmp.beq (proj x) k)

/-- Number of keys at most `k`. -/
def leCount (proj : α → β) (a : Array α) (k : β) : Nat :=
  a.toList.countP (fun x => Cmp.ble (proj x) k)

/-- `p` lies in `k`'s destination block `[ltCount k, ltCount k + eqCount k)`, which
is exactly C++'s `destination_range`. -/
abbrev InBlock (proj : α → β) (a : Array α) (p : Nat) (k : β) : Prop :=
  ltCount proj a k ≤ p ∧ p < ltCount proj a k + eqCount proj a k

theorem leCount_eq (proj : α → β) (a : Array α) (k : β) :
    leCount proj a k = ltCount proj a k + eqCount proj a k := by
  unfold leCount ltCount eqCount
  rw [countP_congr (fun x => Cmp.ble_eq_blt_or_beq (proj x) k)]
  exact countP_or (fun x => Cmp.not_blt_and_beq (proj x) k) _

theorem ltCount_add_eqCount_le_ltCount {proj : α → β} {a : Array α} {k k' : β}
    (h : Cmp.blt k' k = true) : ltCount proj a k' + eqCount proj a k' ≤ ltCount proj a k := by
  rw [← leCount_eq]
  unfold leCount ltCount
  refine countP_le_of_imp (fun x hx => ?_) _
  refine Cmp.blt_of_ble_of_not_ble (Cmp.ble_trans hx (Cmp.ble_of_blt h)) ?_
  cases hkx : Cmp.ble k (proj x) with
  | false => rfl
  | true =>
    exact absurd (Cmp.ble_trans hkx hx) (by rw [Cmp.not_ble_of_blt h]; exact Bool.false_ne_true)

theorem ltCount_add_eqCount_le_size (proj : α → β) (a : Array α) (k : β) :
    ltCount proj a k + eqCount proj a k ≤ a.size := by
  rw [← leCount_eq]
  unfold leCount
  rw [List.countP_eq_length_filter, ← Array.length_toList]
  exact List.length_filter_le _ _

theorem inBlock_unique {proj : α → β} {a : Array α} {p : Nat} {k k' : β}
    (h₁ : InBlock proj a p k) (h₂ : InBlock proj a p k') : Cmp.beq k k' = true := by
  have key := fun {x y : β} (hx : Cmp.blt x y = true) =>
    ltCount_add_eqCount_le_ltCount (proj := proj) (a := a) hx
  have h₁a : ltCount proj a k ≤ p := h₁.1
  have h₁b : p < ltCount proj a k + eqCount proj a k := h₁.2
  have h₂a : ltCount proj a k' ≤ p := h₂.1
  have h₂b : p < ltCount proj a k' + eqCount proj a k' := h₂.2
  rcases Cmp.ble_total k k' with h | h
  · by_cases h' : Cmp.ble k' k = true
    · simp [Cmp.beq, h, h']
    · have hbf : Cmp.ble k' k = false := Bool.eq_false_iff.mpr h'
      have := key (Cmp.blt_of_ble_of_not_ble h hbf)
      omega
  · by_cases h' : Cmp.ble k k' = true
    · simp [Cmp.beq, h, h']
    · have hbf : Cmp.ble k k' = false := Bool.eq_false_iff.mpr h'
      have := key (Cmp.blt_of_ble_of_not_ble h hbf)
      omega

/-! ## Swaps do not change the counts -/

theorem ltCount_swap (proj : α → β) (a : Array α) (i j : Nat) (hi : i < a.size)
    (hj : j < a.size) (k : β) : ltCount proj (a.swap i j hi hj) k = ltCount proj a k :=
  countP_eq_of_perm (Array.swap_perm a i j hi hj)

theorem eqCount_swap (proj : α → β) (a : Array α) (i j : Nat) (hi : i < a.size)
    (hj : j < a.size) (k : β) : eqCount proj (a.swap i j hi hj) k = eqCount proj a k :=
  countP_eq_of_perm (Array.swap_perm a i j hi hj)

theorem inBlock_swap_iff {proj : α → β} {a : Array α} {i j : Nat} (hi : i < a.size)
    (hj : j < a.size) {q : Nat} (k : β) :
    InBlock proj (a.swap i j hi hj) q k ↔ InBlock proj a q k := by
  unfold InBlock
  rw [ltCount_swap, eqCount_swap]

/-! ## Settled positions and the inner loop's fuel -/

/-- Propositional settledness: `p` sits in the block of its own key. -/
def SettledAt (proj : α → β) (a : Array α) (p : Nat) (hp : p < a.size) : Prop :=
  InBlock proj a p (proj (a[p]'hp))

/-- Computable settledness, written with `Nat.ble` so that it rewrites cleanly under
`Array.swap` (no `decide` instance to fight). -/
def settledBool (proj : α → β) (a : Array α) (p : Nat) : Bool :=
  ((a[p]?).map (fun x =>
    Nat.ble (ltCount proj a (proj x)) p
      && Nat.ble (p + 1) (ltCount proj a (proj x) + eqCount proj a (proj x)))).getD false

/-- Number of unsettled positions: the fuel of the inner loop. -/
def unsettledCount (proj : α → β) (a : Array α) : Nat :=
  ((List.range a.size).filter (fun p => !settledBool proj a p)).length

theorem settledBool_eq_true_iff {proj : α → β} {a : Array α} {p : Nat} (hp : p < a.size) :
    settledBool proj a p = true ↔ SettledAt proj a p hp := by
  unfold settledBool SettledAt InBlock
  rw [Array.getElem?_eq_getElem hp]
  simp only [Option.map_some, Option.getD_some, Bool.and_eq_true]
  rw [Nat.ble_eq, Nat.ble_eq]
  exact ⟨fun h => ⟨h.1, by omega⟩, fun h => ⟨h.1, by omega⟩⟩

theorem settledBool_eq_false_iff {proj : α → β} {a : Array α} {p : Nat} (hp : p < a.size) :
    settledBool proj a p = false ↔ ¬SettledAt proj a p hp := by
  constructor
  · intro h hs
    have ht := (settledBool_eq_true_iff hp).mpr hs
    rw [h] at ht
    exact Bool.false_ne_true ht
  · intro h
    cases hb : settledBool proj a p with
    | false => rfl
    | true => exact absurd ((settledBool_eq_true_iff hp).mp hb) h

theorem settledBool_of_unsettledCount_eq_zero {proj : α → β} {a : Array α}
    (h : unsettledCount proj a = 0) {p : Nat} (hp : p < a.size) :
    settledBool proj a p = true := by
  cases hb : settledBool proj a p with
  | true => rfl
  | false =>
    have hmem : p ∈ (List.range a.size).filter (fun q => !settledBool proj a q) :=
      List.mem_filter.mpr ⟨List.mem_range.mpr hp, by rw [hb]; rfl⟩
    have hpos : 0 < ((List.range a.size).filter (fun q => !settledBool proj a q)).length :=
      List.length_pos_iff_exists_mem.mpr ⟨p, hmem⟩
    unfold unsettledCount at h
    omega

/-! ## The partner search (`std::find_if`) -/

/-- The condition tested at `p`: the key at `p` differs from `k`. -/
def neKey (proj : α → β) (a : Array α) (k : β) (p : Nat) : Bool :=
  ((a[p]?).map (fun x => !Cmp.beq (proj x) k)).getD false

/-- First position in `[lo, lo + n)` with a key other than `k`. Recursion is
structural in the width `n`, which keeps the lemmas simple. -/
def firstNe (proj : α → β) (a : Array α) (k : β) : Nat → Nat → Option Nat
  | _, 0 => none
  | lo, n + 1 =>
    if neKey proj a k lo then some lo else firstNe proj a k (lo + 1) n

theorem neKey_eq_true {proj : α → β} {a : Array α} {k : β} {p : Nat}
    (h : neKey proj a k p = true) : ∃ x, a[p]? = some x ∧ Cmp.beq (proj x) k = false := by
  unfold neKey at h
  cases hx : a[p]? with
  | none => simp [hx] at h
  | some x =>
    refine ⟨x, rfl, ?_⟩
    have hb : (!Cmp.beq (proj x) k) = true := by simpa [hx] using h
    cases hbb : Cmp.beq (proj x) k with
    | false => rfl
    | true => simp [hbb] at hb

theorem beq_eq_true_of_neKey_eq_false {proj : α → β} {a : Array α} {k : β} {p : Nat} {x : α}
    (h : neKey proj a k p = false) (hx : a[p]? = some x) : Cmp.beq (proj x) k = true := by
  unfold neKey at h
  have hb : (!Cmp.beq (proj x) k) = false := by simpa [hx] using h
  cases hbb : Cmp.beq (proj x) k with
  | false => simp [hbb] at hb
  | true => rfl

theorem firstNe_some {proj : α → β} {a : Array α} {k : β} {lo n p : Nat}
    (h : firstNe proj a k lo n = some p) :
    lo ≤ p ∧ p < lo + n ∧ ∃ x, a[p]? = some x ∧ Cmp.beq (proj x) k = false := by
  induction n generalizing lo with
  | zero => simp [firstNe] at h
  | succ n ih =>
    unfold firstNe at h
    split at h
    · rename_i hcond
      have hlp : lo = p := Option.some.inj h
      subst hlp
      exact ⟨by omega, by omega, neKey_eq_true hcond⟩
    · obtain ⟨h1, h2, h3⟩ := ih h
      exact ⟨by omega, by omega, h3⟩

theorem firstNe_none {proj : α → β} {a : Array α} {k : β} {lo n : Nat}
    (h : firstNe proj a k lo n = none) :
    ∀ p x, lo ≤ p → p < lo + n → a[p]? = some x → Cmp.beq (proj x) k = true := by
  induction n generalizing lo with
  | zero => intro p x hp1 hp2; omega
  | succ n ih =>
    unfold firstNe at h
    split at h
    · simp at h
    · rename_i hcond
      intro p x hp1 hp2 hx
      rcases Nat.lt_or_ge p (lo + 1) with hlt | hge
      · have hplo : p = lo := by omega
        have hc : neKey proj a k p = false := by
          rw [hplo]
          cases hb : neKey proj a k lo with
          | false => rfl
          | true => exact absurd hb hcond
        exact beq_eq_true_of_neKey_eq_false hc hx
      · exact ih h p x hge (by omega) hx

/-! ## The partner always exists (pigeonhole) -/

/-- If the `w` consecutive positions `[lo, lo + w)` all carry key `k`, then all
`k`-elements sit inside that block: the segments outside it contain none. -/
theorem countP_take_drop_eq_zero {l : List α} {P : α → Bool} {lo w : Nat}
    (hhi : lo + w ≤ l.length) (hcount : l.countP P = w)
    (hmid : ∀ y ∈ (l.drop lo).take w, P y = true) :
    (l.take lo).countP P = 0 ∧ (l.drop (lo + w)).countP P = 0 := by
  have hdrop : (l.drop lo).drop w = l.drop (lo + w) := by
    rw [List.drop_drop]
  have hdecomp : l = l.take lo ++ ((l.drop lo).take w ++ l.drop (lo + w)) := by
    calc l = l.take lo ++ l.drop lo := (List.take_append_drop lo l).symm
      _ = l.take lo ++ ((l.drop lo).take w ++ (l.drop lo).drop w) := by
            rw [List.take_append_drop w (l.drop lo)]
      _ = l.take lo ++ ((l.drop lo).take w ++ l.drop (lo + w)) := by rw [hdrop]
  have hmidlen : ((l.drop lo).take w).length = w := by
    rw [List.length_take, List.length_drop]
    exact Nat.min_eq_left (by omega)
  have hmidcount : ((l.drop lo).take w).countP P = w := by
    rw [countP_eq_length_of_all hmid, hmidlen]
  have hsum0 : (l.take lo ++ ((l.drop lo).take w ++ l.drop (lo + w))).countP P
      = (l.take lo).countP P + (w + (l.drop (lo + w)).countP P) := by
    rw [List.countP_append, List.countP_append, hmidcount]
  have hsum : l.countP P = (l.take lo).countP P + (w + (l.drop (lo + w)).countP P) :=
    (congrArg (fun x => x.countP P) hdecomp).trans hsum0
  have ht : (l.take lo).countP P = 0 := by omega
  have hd : (l.drop (lo + w)).countP P = 0 := by omega
  exact ⟨ht, hd⟩

/-- C++'s `find_if` can never run off the end: whenever position `it` sits outside
its own block, the block contains an element with a different key. -/
theorem exists_partner {proj : α → β} {a : Array α} {it : Nat} (hit : it < a.size)
    (h : ¬InBlock proj a it (proj (a[it]'hit))) :
    ∃ p, ltCount proj a (proj (a[it]'hit)) ≤ p
      ∧ p < ltCount proj a (proj (a[it]'hit)) + eqCount proj a (proj (a[it]'hit))
      ∧ ∃ x, a[p]? = some x ∧ Cmp.beq (proj x) (proj (a[it]'hit)) = false := by
  cases hfn : firstNe proj a (proj (a[it]'hit))
      (ltCount proj a (proj (a[it]'hit))) (eqCount proj a (proj (a[it]'hit))) with
  | some p => exact ⟨p, firstNe_some hfn⟩
  | none =>
    exfalso
    have hnotin : it < ltCount proj a (proj (a[it]'hit))
        ∨ ltCount proj a (proj (a[it]'hit)) + eqCount proj a (proj (a[it]'hit)) ≤ it := by
      rcases Nat.lt_or_ge it (ltCount proj a (proj (a[it]'hit))) with hlt | hge
      · exact Or.inl hlt
      · by_cases hlt2 : it < ltCount proj a (proj (a[it]'hit))
            + eqCount proj a (proj (a[it]'hit))
        · exact absurd ⟨hge, hlt2⟩ h
        · exact Or.inr (by omega)
    have hhi : ltCount proj a (proj (a[it]'hit)) + eqCount proj a (proj (a[it]'hit))
        ≤ a.toList.length := by
      rw [Array.length_toList]
      exact ltCount_add_eqCount_le_size proj a _
    have hcount : a.toList.countP (fun x => Cmp.beq (proj x) (proj (a[it]'hit)))
        = eqCount proj a (proj (a[it]'hit)) := rfl
    have hmid : ∀ y ∈ (a.toList.drop (ltCount proj a (proj (a[it]'hit)))).take
        (eqCount proj a (proj (a[it]'hit))), Cmp.beq (proj y) (proj (a[it]'hit)) = true := by
      intro y hy
      rcases List.mem_iff_getElem.mp hy with ⟨i, hi_lt, hyi⟩
      have hmidlen : ((a.toList.drop (ltCount proj a (proj (a[it]'hit)))).take
          (eqCount proj a (proj (a[it]'hit)))).length = eqCount proj a (proj (a[it]'hit)) := by
        rw [List.length_take, List.length_drop]
        exact Nat.min_eq_left (by omega)
      have hbound : ltCount proj a (proj (a[it]'hit)) + i < a.toList.length := by omega
      have helem : y = a.toList[ltCount proj a (proj (a[it]'hit)) + i]'hbound := by
        rw [← hyi, List.getElem_take, List.getElem_drop]
      have hopt : a[ltCount proj a (proj (a[it]'hit)) + i]? = some y := by
        rw [helem, ← Array.getElem?_toList, List.getElem?_eq_getElem hbound]
      exact firstNe_none hfn _ y (by omega) (by omega) hopt
    have hzero := countP_take_drop_eq_zero (l := a.toList)
      (P := fun x => Cmp.beq (proj x) (proj (a[it]'hit)))
      (lo := ltCount proj a (proj (a[it]'hit))) (w := eqCount proj a (proj (a[it]'hit)))
      hhi hcount hmid
    have hitbound : it < a.toList.length := by rw [Array.length_toList]; exact hit
    have hitP : Cmp.beq (proj (a.toList[it]'hitbound)) (proj (a[it]'hit)) = true := by
      have heq : a.toList[it]'hitbound = a[it]'hit := Array.getElem_toList hitbound
      rw [heq]
      exact Cmp.beq_iff.mpr ⟨Cmp.ble_refl _, Cmp.ble_refl _⟩
    rcases hnotin with hlt | hge
    · have hmem : a.toList[it]'hitbound ∈ a.toList.take (ltCount proj a (proj (a[it]'hit))) := by
        refine List.mem_iff_getElem.mpr ⟨it, ?_, ?_⟩
        · rw [List.length_take]
          exact Nat.lt_min.mpr ⟨hlt, hitbound⟩
        · rw [List.getElem_take]
      have hpos : 0 < (a.toList.take (ltCount proj a (proj (a[it]'hit)))).countP
          (fun x => Cmp.beq (proj x) (proj (a[it]'hit))) :=
        countP_pos_of_mem hmem hitP
      omega
    · have hdropmem : a.toList[it]'hitbound ∈ a.toList.drop
          (ltCount proj a (proj (a[it]'hit)) + eqCount proj a (proj (a[it]'hit))) := by
        refine List.mem_iff_getElem.mpr
          ⟨it - (ltCount proj a (proj (a[it]'hit)) + eqCount proj a (proj (a[it]'hit))), ?_, ?_⟩
        · rw [List.length_drop]
          omega
        · rw [List.getElem_drop]
          congr 1
          omega
      have hpos : 0 < (a.toList.drop (ltCount proj a (proj (a[it]'hit))
          + eqCount proj a (proj (a[it]'hit)))).countP
          (fun x => Cmp.beq (proj x) (proj (a[it]'hit))) :=
        countP_pos_of_mem hdropmem hitP
      omega

/-! ## Settledness under a single swap -/

theorem settledBool_swap_of_ne {proj : α → β} {a : Array α} {i j q : Nat} (hi : i < a.size)
    (hj : j < a.size) (hqi : q ≠ i) (hqj : q ≠ j) :
    settledBool proj (a.swap i j hi hj) q = settledBool proj a q := by
  unfold settledBool
  rw [Array.getElem?_swap, ite_eq_right (fun h : j = q => hqj h.symm),
    ite_eq_right (fun h : i = q => hqi h.symm)]
  simp only [ltCount_swap, eqCount_swap]

/-- A swap that only moves *unsettled* elements around cannot unsettle anything. -/
theorem settledBool_swap_mono {proj : α → β} {a : Array α} {i j : Nat} (hi : i < a.size)
    (hj : j < a.size) (hiU : settledBool proj a i = false) (hjU : settledBool proj a j = false) :
    ∀ q, settledBool proj a q = true → settledBool proj (a.swap i j hi hj) q = true := by
  intro q hq
  by_cases hqi : q = i
  · subst hqi
    rw [hiU] at hq
    exact absurd hq Bool.false_ne_true
  · by_cases hqj : q = j
    · subst hqj
      rw [hjU] at hq
      exact absurd hq Bool.false_ne_true
    · rw [settledBool_swap_of_ne (proj := proj) hi hj hqi hqj]
      exact hq

/-- The measure really decreases: the swap settles position `j` and unsettles nothing. -/
theorem unsettledCount_swap_lt {proj : α → β} {a : Array α} {i j : Nat} (hi : i < a.size)
    (hj : j < a.size) (hiU : settledBool proj a i = false) (hjU : settledBool proj a j = false)
    (hjS : settledBool proj (a.swap i j hi hj) j = true) :
    unsettledCount proj (a.swap i j hi hj) < unsettledCount proj a := by
  have hmono := settledBool_swap_mono (proj := proj) hi hj hiU hjU
  have hsize : (a.swap i j hi hj).size = a.size := Array.size_swap
  have key := countP_lt_of_imp_of_witness
    (p := fun q => !settledBool proj a q)
    (q := fun q => !settledBool proj (a.swap i j hi hj) q)
    (fun x hx => by
      cases ha : settledBool proj a x with
      | false => rfl
      | true =>
        rw [hmono x ha] at hx
        exact hx)
    (List.mem_range.mpr hj)
    (by rw [hjU]; rfl)
    (by rw [hjS]; rfl)
  unfold unsettledCount
  rw [hsize, ← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  exact key

theorem firstNe_some_beq_false {proj : α → β} {a : Array α} {k : β} {lo n p : Nat}
    (h : firstNe proj a k lo n = some p) (hp : p < a.size) :
    Cmp.beq (proj (a[p]'hp)) k = false := by
  obtain ⟨x, hx, hbeq⟩ := (firstNe_some h).2.2
  have hx' : a[p]'hp = x := by
    rw [Array.getElem?_eq_getElem hp] at hx
    exact Option.some.inj hx
  rw [← hx'] at hbeq
  exact hbeq

/-- If `p` is the partner `firstNe` returns for the unsettled position `it`, then
swapping the two settles `p` and drops the unsettled count, while every settled
position stays settled.  This is the one step of the inner loop, shared by the
correctness invariant below and by the cost module's potential argument. -/
theorem swap_partner_spec {proj : α → β} {a : Array α} {it p : Nat}
    (hit : it < a.size) (hIn : ¬InBlock proj a it (proj (a[it]'hit))) (hp : p < a.size)
    (hfn : firstNe proj a (proj (a[it]'hit)) (ltCount proj a (proj (a[it]'hit)))
        (eqCount proj a (proj (a[it]'hit))) = some p) :
    unsettledCount proj (a.swap it p hit hp) < unsettledCount proj a
    ∧ (∀ q, settledBool proj a q = true → settledBool proj (a.swap it p hit hp) q = true) := by
  have hbeqf : Cmp.beq (proj (a[p]'hp)) (proj (a[it]'hit)) = false :=
    firstNe_some_beq_false hfn hp
  have hpblock : InBlock proj a p (proj (a[it]'hit)) :=
    ⟨(firstNe_some hfn).1, (firstNe_some hfn).2.1⟩
  have hnp : ¬(p = it) := by
    intro hpit
    exact hIn (hpit ▸ hpblock)
  have hUit : settledBool proj a it = false := (settledBool_eq_false_iff hit).mpr hIn
  have hUp : settledBool proj a p = false := by
    rw [settledBool_eq_false_iff hp]
    intro hs
    have hb := inBlock_unique hpblock hs
    rw [Cmp.beq_comm (proj (a[it]'hit)) (proj (a[p]'hp))] at hb
    rw [hbeqf] at hb
    exact Bool.false_ne_true hb
  have hp' : p < (a.swap it p hit hp).size := by rw [Array.size_swap]; exact hp
  have hSp : settledBool proj (a.swap it p hit hp) p = true := by
    rw [settledBool_eq_true_iff hp']
    unfold SettledAt
    have hpe : (a.swap it p hit hp)[p]'hp' = a[it]'hit := by
      rw [Array.getElem_swap, ite_eq_right hnp, ite_eq_left rfl]
    rw [hpe]
    exact (inBlock_swap_iff hit hp (q := p) (proj (a[it]'hit))).mpr hpblock
  exact ⟨unsettledCount_swap_lt (proj := proj) hit hp hUit hUp hSp,
    settledBool_swap_mono (proj := proj) hit hp hUit hUp⟩


/-- The C++ inner loop: keep swapping until position `it` falls into the block of its
own key.  The fuel is the number of unsettled positions. -/
def innerAux (proj : α → β) : Nat → (a : Array α) → (it : Nat) → it < a.size → Array α
  | 0, a, _, _ => a
  | n + 1, a, it, hit =>
    if _ : InBlock proj a it (proj (a[it]'hit)) then a
    else
      match hfn : firstNe proj a (proj (a[it]'hit)) (ltCount proj a (proj (a[it]'hit)))
          (eqCount proj a (proj (a[it]'hit))) with
      | none => a
      | some p =>
        innerAux proj n (a.swap it p hit (by
            have h1 := (firstNe_some hfn).2.1
            have h2 := ltCount_add_eqCount_le_size proj a (proj (a[it]'hit))
            omega)) it (by rw [Array.size_swap]; exact hit)

theorem innerAux_size (proj : α → β) (n : Nat) (a : Array α) (it : Nat) (hit : it < a.size) :
    (innerAux proj n a it hit).size = a.size := by
  induction n generalizing a it hit with
  | zero => rfl
  | succ n ih =>
    simp only [innerAux]
    split
    · rfl
    · split
      · rfl
      · rename_i p hfn
        rw [ih, Array.size_swap]

/-- Every invariant of the inner loop, proved by one induction. -/
theorem innerAux_spec (proj : α → β) (n : Nat) (a : Array α) (it : Nat) (hit : it < a.size)
    (hn : unsettledCount proj a ≤ n) :
    (innerAux proj n a it hit).size = a.size
    ∧ (innerAux proj n a it hit).toList.Perm a.toList
    ∧ (∀ k, ltCount proj (innerAux proj n a it hit) k = ltCount proj a k)
    ∧ (∀ k, eqCount proj (innerAux proj n a it hit) k = eqCount proj a k)
    ∧ (∀ q, settledBool proj a q = true → settledBool proj (innerAux proj n a it hit) q = true)
    ∧ settledBool proj (innerAux proj n a it hit) it = true := by
  induction n generalizing a it hit with
  | zero =>
    have h0 : unsettledCount proj a = 0 := by omega
    exact ⟨rfl, List.Perm.refl _, fun k => rfl, fun k => rfl, fun q hq => hq,
      settledBool_of_unsettledCount_eq_zero h0 hit⟩
  | succ n ih =>
    simp only [innerAux]
    split
    · rename_i hIn
      exact ⟨rfl, List.Perm.refl _, fun k => rfl, fun k => rfl, fun q hq => hq,
        (settledBool_eq_true_iff hit).mpr hIn⟩
    · rename_i hnot
      split
      · rename_i hfn
        exfalso
        obtain ⟨p, hp1, hp2, x, hx, hbeq⟩ := exists_partner hit hnot
        have hc := firstNe_none hfn p x hp1 hp2 hx
        rw [hc] at hbeq
        exact Bool.false_ne_true hbeq.symm
      · rename_i p hfn
        have hsp := firstNe_some hfn
        have hp1 : ltCount proj a (proj (a[it]'hit)) ≤ p := hsp.1
        have hp2 : p < ltCount proj a (proj (a[it]'hit)) + eqCount proj a (proj (a[it]'hit)) :=
          hsp.2.1
        have hpblock : InBlock proj a p (proj (a[it]'hit)) := ⟨hp1, hp2⟩
        have hltp : p < a.size := by
          have h2 := ltCount_add_eqCount_le_size proj a (proj (a[it]'hit))
          omega
        obtain ⟨hdec, hmono⟩ := swap_partner_spec hit hnot hltp hfn
        have hn' : unsettledCount proj (a.swap it p hit hltp) ≤ n := by omega
        have hit' : it < (a.swap it p hit hltp).size := by rw [Array.size_swap]; exact hit
        obtain ⟨ihsz, ihperm, ihlt, iheq, ihmono, ihit⟩ := ih (a.swap it p hit hltp) it hit' hn'
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · exact ihsz.trans Array.size_swap
        · exact ihperm.trans (Array.swap_perm a it p hit hltp)
        · intro k
          exact (ihlt k).trans (ltCount_swap proj a it p hit hltp k)
        · intro k
          exact (iheq k).trans (eqCount_swap proj a it p hit hltp k)
        · intro q hq
          exact ihmono q (hmono q hq)
        · exact ihit

def inner (proj : α → β) (a : Array α) (it : Nat) (hit : it < a.size) : Array α :=
  innerAux proj (unsettledCount proj a) a it hit

theorem inner_size (proj : α → β) (a : Array α) (it : Nat) (hit : it < a.size) :
    (inner proj a it hit).size = a.size :=
  (innerAux_spec proj (unsettledCount proj a) a it hit (Nat.le_refl _)).1

theorem inner_settled (proj : α → β) (a : Array α) (it : Nat) (hit : it < a.size) :
    settledBool proj (inner proj a it hit) it = true :=
  (innerAux_spec proj (unsettledCount proj a) a it hit (Nat.le_refl _)).2.2.2.2.2

theorem inner_settled_mono (proj : α → β) (a : Array α) (it : Nat) (hit : it < a.size) :
    ∀ q, settledBool proj a q = true → settledBool proj (inner proj a it hit) q = true :=
  (innerAux_spec proj (unsettledCount proj a) a it hit (Nat.le_refl _)).2.2.2.2.1

theorem inner_perm (proj : α → β) (a : Array α) (it : Nat) (hit : it < a.size) :
    (inner proj a it hit).toList.Perm a.toList :=
  (innerAux_spec proj (unsettledCount proj a) a it hit (Nat.le_refl _)).2.1

/-! ## The outer loop -/

/-- The C++ outer loop. -/
def outerAux (proj : α → β) : Nat → (a : Array α) → (it : Nat) → it ≤ a.size → Array α
  | 0, a, _, _ => a
  | n + 1, a, it, hle =>
    if h : it < a.size then
      outerAux proj n (inner proj a it h) (it + 1) (by rw [inner_size]; omega)
    else a

/-- The outer loop: after visiting every position, **every position is settled**. -/
theorem outerAux_spec (proj : α → β) (n : Nat) (a : Array α) (it : Nat) (hle : it ≤ a.size)
    (hn : a.size - it ≤ n) (hinv : ∀ q, q < it → settledBool proj a q = true) :
    (outerAux proj n a it hle).size = a.size
    ∧ (outerAux proj n a it hle).toList.Perm a.toList
    ∧ (∀ q, q < a.size → settledBool proj (outerAux proj n a it hle) q = true) := by
  induction n generalizing a it hle with
  | zero =>
    have hsz : it = a.size := by omega
    exact ⟨rfl, List.Perm.refl _, fun q hq => hinv q (by omega)⟩
  | succ n ih =>
    simp only [outerAux]
    split
    · rename_i h
      have hle' : it + 1 ≤ (inner proj a it h).size := by rw [inner_size]; omega
      have hn' : (inner proj a it h).size - (it + 1) ≤ n := by rw [inner_size]; omega
      have hinv' : ∀ q, q < it + 1 → settledBool proj (inner proj a it h) q = true := by
        intro q hq
        by_cases hqi : q < it
        · exact inner_settled_mono proj a it h q (hinv q hqi)
        · have hqe : q = it := by omega
          rw [hqe]
          exact inner_settled proj a it h
      obtain ⟨ihsz, ihperm, ihall⟩ := ih (inner proj a it h) (it + 1) hle' hn' hinv'
      exact ⟨ihsz.trans (inner_size proj a it h),
        ihperm.trans (inner_perm proj a it h),
        fun q hq => ihall q (by rw [inner_size]; exact hq)⟩
    · rename_i h
      exact ⟨rfl, List.Perm.refl _, fun q hq => hinv q (by omega)⟩

def cyclesort (proj : α → β) (a : Array α) : Array α :=
  outerAux proj a.size a 0 (Nat.zero_le _)

theorem cyclesort_size (proj : α → β) (a : Array α) : (cyclesort proj a).size = a.size :=
  (outerAux_spec proj a.size a 0 (Nat.zero_le _) (by omega) (by intro q hq; omega)).1

theorem cyclesort_perm (proj : α → β) (a : Array α) :
    (cyclesort proj a).toList.Perm a.toList :=
  (outerAux_spec proj a.size a 0 (Nat.zero_le _) (by omega) (by intro q hq; omega)).2.1

theorem cyclesort_settled (proj : α → β) (a : Array α) :
    ∀ q, q < a.size → settledBool proj (cyclesort proj a) q = true :=
  (outerAux_spec proj a.size a 0 (Nat.zero_le _) (by omega) (by intro q hq; omega)).2.2

/-! ## All settled implies sorted -/

theorem sorted_of_all_settled {proj : α → β} {a : Array α}
    (h : ∀ q (hq : q < a.size), SettledAt proj a q hq) :
    Sorted (fun x y => Cmp.ble (proj x) (proj y) = true) a.toList := by
  refine List.pairwise_iff_getElem.mpr (fun i j hi hj hij => ?_)
  have hi' : i < a.size := by rwa [Array.length_toList] at hi
  have hj' : j < a.size := by rwa [Array.length_toList] at hj
  have hge : Cmp.ble (proj (a[i]'hi')) (proj (a[j]'hj')) = true := by
    by_cases hb : Cmp.ble (proj (a[i]'hi')) (proj (a[j]'hj')) = true
    · exact hb
    · exfalso
      have hbf : Cmp.ble (proj (a[i]'hi')) (proj (a[j]'hj')) = false := Bool.eq_false_iff.mpr hb
      have htot : Cmp.ble (proj (a[j]'hj')) (proj (a[i]'hi')) = true := by
        rcases Cmp.ble_total (proj (a[j]'hj')) (proj (a[i]'hi')) with hh | hh
        · exact hh
        · exact absurd hh hb
      have hblt : Cmp.blt (proj (a[j]'hj')) (proj (a[i]'hi')) = true :=
        Cmp.blt_of_ble_of_not_ble htot hbf
      have hmono := ltCount_add_eqCount_le_ltCount (proj := proj) (a := a)
        (k := proj (a[i]'hi')) (k' := proj (a[j]'hj')) hblt
      have hJ : j < ltCount proj a (proj (a[j]'hj')) + eqCount proj a (proj (a[j]'hj')) :=
        (h j hj').2
      have hI : ltCount proj a (proj (a[i]'hi')) ≤ i := (h i hi').1
      omega
  rw [Array.getElem_toList hi, Array.getElem_toList hj]
  exact hge

/-! ## The main theorem -/

theorem cyclesort_sorted (proj : α → β) (a : Array α) :
    Sorted (fun x y => Cmp.ble (proj x) (proj y) = true) (cyclesort proj a).toList := by
  refine sorted_of_all_settled (fun q hq => ?_)
  have hq' : q < a.size := by rw [cyclesort_size proj a] at hq; exact hq
  exact (settledBool_eq_true_iff hq).mp (cyclesort_settled proj a q hq')

theorem cyclesort_isSort (proj : α → β) :
    IsSort (fun x y => Cmp.ble (proj x) (proj y) = true) (cyclesort proj) :=
  ⟨fun a => cyclesort_sorted proj a, fun a => cyclesort_perm proj a⟩

/-! ## Non-vacuity checks (concrete values) -/

example : (cyclesort (α := Nat) (β := Nat) id #[]).toList = [] := rfl

example : (cyclesort (α := Nat) (β := Nat) id #[7]).toList = [7] := rfl

example : (cyclesort (α := Nat) (β := Nat) id #[2, 5, 9]).toList = [2, 5, 9] := rfl

example : (cyclesort (α := Nat) (β := Nat) id #[3, 1, 2]).toList = [1, 2, 3] := rfl

example : (cyclesort (α := Nat) (β := Nat) id #[4, 3, 2, 1]).toList = [1, 2, 3, 4] := rfl

example : (cyclesort (α := Nat) (β := Nat) id #[2, 1, 2, 1]).toList = [1, 1, 2, 2] := rfl

example : (cyclesort (α := Nat) (β := Nat) id #[5, 4, 3, 2, 1]).toList = [1, 2, 3, 4, 5] := rfl

example : (cyclesort (α := Nat) (β := Nat) id #[3, 5, 1, 6, 2, 4]).toList = [1, 2, 3, 4, 5, 6] := rfl

example : (cyclesort (α := Nat) (β := Nat) id #[7, 6, 5, 4, 3, 2, 1]).toList = [1, 2, 3, 4, 5, 6, 7] := rfl

example : (cyclesort (α := Nat) (β := Nat) id #[4, 8, 1, 7, 3, 6, 2, 5]).toList
    = [1, 2, 3, 4, 5, 6, 7, 8] := rfl

example : (cyclesort (α := Nat) (β := Nat) id #[3, 3, 1, 2, 3, 1, 2]).toList
    = [1, 1, 2, 2, 3, 3, 3] := rfl

example : (cyclesort (α := Nat) (β := Nat) id #[2, 2, 2, 2]).toList = [2, 2, 2, 2] := rfl

example : (cyclesort (α := Nat) (β := Nat) id #[1, 2, 3, 4, 5, 6, 7, 8]).toList
    = [1, 2, 3, 4, 5, 6, 7, 8] := rfl

example : (cyclesort (α := Nat) (β := Nat) id #[5, 1, 8, 3, 8, 2, 1, 7]).toList
    = [1, 1, 2, 3, 5, 7, 8, 8] := rfl

end Cyclesort
end Tcs
