/-
  A decidable total order on keys.

  Lean core and Std ship no order classes (`LinearOrder` belongs to Mathlib), so
  keys carry their own total order as `Cmp` data, mirroring what the C++
  comparison operators compute. `Nat` is the only instance needed here, for the
  non-vacuity checks; a user of a proof supplies the instance for their key type.
-/
namespace Tcs

/-! ## A decidable total order on keys -/

/-- Decidable total order given as a Bool-valued `≤`, matching what the C++
comparison operators compute. -/
class Cmp (β : Type v) where
  ble : β → β → Bool
  ble_refl : ∀ a, ble a a = true
  ble_total : ∀ a b, ble a b = true ∨ ble b a = true
  ble_trans : ∀ {a b c : β}, ble a b = true → ble b c = true → ble a c = true
  ble_antisymm : ∀ {a b : β}, ble a b = true → ble b a = true → a = b

namespace Cmp

variable {β : Type v} [Cmp β]

/-- Strict comparison `a < b`. -/
def blt (a b : β) : Bool := ble a b && !ble b a

/-- Key equality decided by the order (exact, by antisymmetry). -/
def beq (a b : β) : Bool := ble a b && ble b a

theorem blt_iff {a b : β} : blt a b = true ↔ ble a b = true ∧ ble b a = false := by
  simp [blt, Bool.and_eq_true]

theorem beq_iff {a b : β} : beq a b = true ↔ ble a b = true ∧ ble b a = true := by
  simp [beq, Bool.and_eq_true]

theorem beq_eq {a b : β} (h : beq a b = true) : a = b :=
  ble_antisymm (beq_iff.mp h).1 (beq_iff.mp h).2

theorem ble_of_blt {a b : β} (h : blt a b = true) : ble a b = true :=
  (blt_iff.mp h).1

theorem not_ble_of_blt {a b : β} (h : blt a b = true) : ble b a = false :=
  (blt_iff.mp h).2

theorem not_blt_and_beq (a b : β) : ¬(blt a b = true ∧ beq a b = true) := by
  rintro ⟨h₁, h₂⟩
  have h := (blt_iff.mp h₁).2
  have h₃ : ble b a = true := (beq_iff.mp h₂).2
  rw [h] at h₃
  exact Bool.false_ne_true h₃

theorem ble_eq_blt_or_beq (a b : β) : ble a b = (blt a b || beq a b) := by
  cases hab : ble a b <;> cases hba : ble b a <;> simp [blt, beq, hab, hba]

theorem blt_of_ble_of_not_ble {a b : β} (h₁ : ble a b = true) (h₂ : ble b a = false) :
    blt a b = true := by
  simp [blt, h₁, h₂]

theorem blt_trans {a b c : β} (h₁ : blt a b = true) (h₂ : blt b c = true) : blt a c = true := by
  have h1 := blt_iff.mp h₁
  have h2 := blt_iff.mp h₂
  refine blt_iff.mpr ⟨ble_trans h1.1 h2.1, ?_⟩
  cases hca : ble c a with
  | false => rfl
  | true => exact absurd (ble_trans hca h1.1) (by rw [h2.2]; exact Bool.false_ne_true)

theorem beq_comm (a b : β) : beq a b = beq b a := by
  simp [beq, Bool.and_comm]

/-- Totality in the form the strict order needs it: a failed `<` means `≥`. -/
theorem blt_eq_false_iff {a b : β} : blt a b = false ↔ ble b a = true := by
  rw [blt, Bool.and_eq_false_iff]
  constructor
  · rintro (h | h)
    · rcases ble_total a b with h₁ | h₁
      · exact absurd h₁ (by simp [h])
      · exact h₁
    · simpa using h
  · intro h
    exact Or.inr (by simpa using h)

theorem ble_of_not_blt {a b : β} (h : blt a b = false) : ble b a = true :=
  blt_eq_false_iff.mp h

end Cmp

/-! ### `Nat` instance, used by the non-vacuity checks -/

theorem nat_ble_refl (a : Nat) : Nat.ble a a = true := by
  rw [Nat.ble_eq]
  exact Nat.le_refl a

theorem nat_ble_total (a b : Nat) : Nat.ble a b = true ∨ Nat.ble b a = true := by
  rw [Nat.ble_eq, Nat.ble_eq]
  exact Nat.le_total a b

theorem nat_ble_trans {a b c : Nat} (h₁ : Nat.ble a b = true) (h₂ : Nat.ble b c = true) :
    Nat.ble a c = true := by
  rw [Nat.ble_eq] at h₁ h₂ ⊢
  exact Nat.le_trans h₁ h₂

theorem nat_ble_antisymm {a b : Nat} (h₁ : Nat.ble a b = true) (h₂ : Nat.ble b a = true) :
    a = b := by
  rw [Nat.ble_eq] at h₁ h₂
  exact Nat.le_antisymm h₁ h₂

instance : Cmp Nat where
  ble := Nat.ble
  ble_refl := nat_ble_refl
  ble_total := nat_ble_total
  ble_trans := nat_ble_trans
  ble_antisymm := nat_ble_antisymm

/-! ### Strict-order glue

`blt` and `beq` are mutually consistent with `ble`, which is what lets a rank
computed for one representative of a key block transfer to another. -/

namespace Cmp

variable {β : Type v} [Cmp β]

theorem blt_irrefl (a : β) : blt a a = false := by
  simp [blt, ble_refl]

theorem not_blt_of_blt {a b : β} (h : blt a b = true) : blt b a = false := by
  have h₁ := (blt_iff.mp h).1
  have h₂ := (blt_iff.mp h).2
  simp [blt, h₁, h₂]

theorem blt_of_ble_of_blt {a b c : β} (h₁ : ble a b = true) (h₂ : blt b c = true) :
    blt a c = true := by
  refine blt_of_ble_of_not_ble (ble_trans h₁ (ble_of_blt h₂)) ?_
  cases h : ble c a with
  | false => rfl
  | true =>
    exact absurd (ble_trans h h₁) (by rw [not_ble_of_blt h₂]; exact Bool.false_ne_true)

theorem blt_of_blt_of_ble {a b c : β} (h₁ : blt a b = true) (h₂ : ble b c = true) :
    blt a c = true := by
  refine blt_of_ble_of_not_ble (ble_trans (ble_of_blt h₁) h₂) ?_
  cases h : ble c a with
  | false => rfl
  | true =>
    exact absurd (ble_trans h₂ h) (by rw [not_ble_of_blt h₁]; exact Bool.false_ne_true)

theorem blt_of_beq_of_blt {a b c : β} (h₁ : beq a b = true) (h₂ : blt b c = true) :
    blt a c = true :=
  blt_of_ble_of_blt (beq_iff.mp h₁).1 h₂

theorem blt_of_blt_of_beq {a b c : β} (h₁ : blt a b = true) (h₂ : beq b c = true) :
    blt a c = true :=
  blt_of_blt_of_ble h₁ (beq_iff.mp h₂).1

theorem blt_congr_left {a b c : β} (h : beq a b = true) : blt a c = blt b c := by
  rw [beq_eq h]

theorem blt_congr_right {a b c : β} (h : beq b c = true) : blt a b = blt a c := by
  rw [beq_eq h]

theorem ble_congr_left {a b c : β} (h : beq a b = true) : ble a c = ble b c := by
  rw [beq_eq h]

theorem ble_congr_right {a b c : β} (h : beq b c = true) : ble a b = ble a c := by
  rw [beq_eq h]

end Cmp

end Tcs
