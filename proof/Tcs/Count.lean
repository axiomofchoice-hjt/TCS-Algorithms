/-
  Counting lemmas for `List.countP`, used by every algorithm proof to reason
  about keys below / equal to / at most a pivot. All lemmas here are generic in
  the element type and the predicate; the order-aware corollaries live next to
  the algorithms that need them.
-/
import Tcs.Order

namespace Tcs

/-! ## Generic `countP` lemmas -/

theorem countP_congr {γ : Type w} {p q : γ → Bool} (h : ∀ x, p x = q x) (l : List γ) :
    l.countP p = l.countP q := by
  induction l with
  | nil => simp
  | cons x xs ih => rw [List.countP_cons, List.countP_cons, h x, ih]

theorem countP_or {γ : Type w} {p q : γ → Bool} (h : ∀ x, ¬(p x = true ∧ q x = true))
    (l : List γ) : l.countP (fun x => p x || q x) = l.countP p + l.countP q := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.countP_cons, List.countP_cons, List.countP_cons, ih]
    by_cases hp : p x = true
    · have hq : q x = false := by
        cases hqx : q x with
        | false => rfl
        | true => exact absurd ⟨hp, hqx⟩ (h x)
      rw [hp, hq]
      simp <;> omega
    · have hp' : p x = false := by
        cases hpx : p x with
        | false => rfl
        | true => exact absurd hpx hp
      by_cases hq : q x = true
      · rw [hp', hq]
        simp <;> omega
      · have hq' : q x = false := by
          cases hqx : q x with
          | false => rfl
          | true => exact absurd hqx hq
        rw [hp', hq']
        simp <;> omega

theorem countP_le_of_imp {γ : Type w} {p q : γ → Bool} (h : ∀ x, p x = true → q x = true)
    (l : List γ) : l.countP p ≤ l.countP q := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.countP_cons, List.countP_cons]
    by_cases hp : p x = true
    · have hq : q x = true := h x hp
      rw [hp, hq]
      simp <;> omega
    · have hp' : p x = false := by
        cases hpx : p x with
        | false => rfl
        | true => exact absurd hpx hp
      by_cases hq : q x = true
      · rw [hp', hq]
        simp <;> omega
      · have hq' : q x = false := by
          cases hqx : q x with
          | false => rfl
          | true => exact absurd hqx hq
        rw [hp', hq']
        simp <;> omega

theorem countP_eq_of_perm {γ : Type w} {p : γ → Bool} {l₁ l₂ : List γ} (h : l₁.Perm l₂) :
    l₁.countP p = l₂.countP p := by
  rw [List.countP_eq_length_filter, List.countP_eq_length_filter]
  exact (h.filter p).length_eq

theorem countP_eq_length_of_all {γ : Type w} {p : γ → Bool} {l : List γ}
    (h : ∀ x ∈ l, p x = true) : l.countP p = l.length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.countP_cons, h x (List.mem_cons_self),
      ih (fun y hy => h y (List.mem_cons_of_mem x hy))]
    simp

theorem countP_pos_of_mem {γ : Type w} {p : γ → Bool} {x : γ} {l : List γ} (hx : x ∈ l)
    (hp : p x = true) : 0 < l.countP p := by
  induction l with
  | nil => simp at hx
  | cons y ys ih =>
    rw [List.countP_cons]
    rcases List.mem_cons.mp hx with rfl | hx'
    · rw [hp]
      simp
    · have hys : 0 < ys.countP p := ih hx'
      by_cases hy : p y = true
      · rw [hy]
        simp <;> omega
      · have hy' : p y = false := by
          cases hpy : p y with
          | false => rfl
          | true => exact absurd hpy hy
        have h0 : (if p y = true then 1 else 0) = 0 := by
          rw [hy']
          simp
        rw [h0]
        omega

theorem countP_lt_of_imp_of_witness {γ : Type w} {p q : γ → Bool}
    (h : ∀ x, q x = true → p x = true) {l : List γ} {y : γ} (hy : y ∈ l) (hp : p y = true)
    (hq : q y = false) : l.countP q < l.countP p := by
  induction l with
  | nil => simp at hy
  | cons x xs ih =>
    rw [List.countP_cons, List.countP_cons]
    rcases List.mem_cons.mp hy with rfl | hy'
    · have hm : xs.countP q ≤ xs.countP p := countP_le_of_imp h xs
      rw [hp, hq]
      simp <;> omega
    · have hxs := ih hy'
      by_cases hpx : p x = true
      · by_cases hqx : q x = true
        · rw [hqx, hpx]
          simp <;> omega
        · have hqx' : q x = false := by
            cases hqx'' : q x with
            | false => rfl
            | true => exact absurd hqx'' hqx
          rw [hqx', hpx]
          simp <;> omega
      · have hpx' : p x = false := by
          cases hpx'' : p x with
          | false => rfl
          | true => exact absurd hpx'' hpx
        have hqx' : q x = false := by
          cases hqx'' : q x with
          | false => rfl
          | true => exact absurd (h x hqx'') hpx
        rw [hqx', hpx']
        simp <;> omega

/-- A predicate that fails somewhere counts fewer elements than the list is long.
This is what makes a partition strictly shrink its input. -/
theorem countP_lt_length_of_mem_false {γ : Type w} {p : γ → Bool} {l : List γ} {y : γ}
    (hy : y ∈ l) (hp : p y = false) : l.countP p < l.length := by
  induction l with
  | nil => simp at hy
  | cons x xs ih =>
    rw [List.countP_cons]
    rcases List.mem_cons.mp hy with rfl | hy'
    · have := List.countP_le_length (l := xs) (p := p)
      rw [hp]
      simp
      omega
    · have h₁ := ih hy'
      have h₂ := List.countP_le_length (l := xs) (p := p)
      have h₃ : (if p x then 1 else 0) ≤ 1 := by split <;> omega
      simp only [List.length_cons]
      omega

/-- A predicate that fails everywhere counts nothing. Constructive counterpart of
core's `List.countP_eq_zero`, whose proof pulls in `Classical.choice`. -/
theorem countP_eq_zero_of_all {γ : Type w} {p : γ → Bool} {l : List γ}
    (h : ∀ x ∈ l, p x = false) : l.countP p = 0 := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.countP_cons, h x (List.mem_cons_self),
      ih (fun y hy => h y (List.mem_cons_of_mem x hy))]
    simp

end Tcs
