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

/-- A successful strict test excludes equality. -/
theorem not_beq_of_blt {a b : β} (h : blt a b = true) : beq a b = false := by
  simp [beq, (blt_iff.mp h).2]

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

instance : Cmp Nat where
  ble := Nat.ble
  ble_refl a := by rw [Nat.ble_eq]; exact Nat.le_refl a
  ble_total a b := by rw [Nat.ble_eq, Nat.ble_eq]; exact Nat.le_total a b
  ble_trans := by intro a b c h₁ h₂; rw [Nat.ble_eq] at h₁ h₂ ⊢; exact Nat.le_trans h₁ h₂
  ble_antisymm := by intro a b h₁ h₂; rw [Nat.ble_eq] at h₁ h₂; exact Nat.le_antisymm h₁ h₂

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

/-! ### Lexicographic order on key/tag pairs

The stable merge distinguishes equal keys by the label of the block an element came
from, which is exactly the lexicographic order below: compare keys first, break ties
with the tag. -/

/-- The lexicographic comparison used for tagged keys, as a test. -/
theorem prod_ble_iff {a b : β × Nat} :
    (blt a.1 b.1 || (beq a.1 b.1 && Nat.ble a.2 b.2)) = true ↔
      blt a.1 b.1 = true ∨ (a.1 = b.1 ∧ a.2 ≤ b.2) := by
  rw [Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq, beq_iff]
  constructor
  · rintro (h | ⟨⟨h₁, h₂⟩, h₃⟩)
    · exact Or.inl h
    · exact Or.inr ⟨ble_antisymm h₁ h₂, h₃⟩
  · rintro (h | ⟨h₁, h₃⟩)
    · exact Or.inl h
    · rw [h₁]
      exact Or.inr ⟨⟨ble_refl _, ble_refl _⟩, h₃⟩

theorem beq_refl (a : β) : beq a a = true := by rw [Cmp.beq, Cmp.ble_refl, Bool.and_self]

theorem of_eq {a b : β} (h : a = b) : ble a b = true := h ▸ ble_refl a

end Cmp

/-- Lexicographic order on `key × tag` pairs: keys first, tags break ties. This is the
order the C++ stable merge compares with inside the block phase, where the tag is the
label of the block an element came from. -/
instance instCmpProdNat [Cmp β] : Cmp (β × Nat) where
  ble a b := Cmp.blt a.1 b.1 || (Cmp.beq a.1 b.1 && Nat.ble a.2 b.2)
  ble_refl a := Cmp.prod_ble_iff.mpr (Or.inr ⟨rfl, Nat.le_refl a.2⟩)
  ble_total a b := by
    cases h : Cmp.blt a.1 b.1 with
    | true => left; simp
    | false =>
      cases h₂ : Cmp.blt b.1 a.1 with
      | true => right; simp
      | false =>
        have heq : Cmp.beq a.1 b.1 = true := by
          have h₁ : Cmp.ble b.1 a.1 = (Cmp.blt b.1 a.1 || Cmp.beq b.1 a.1) :=
            Cmp.ble_eq_blt_or_beq b.1 a.1
          have hba : Cmp.ble b.1 a.1 = true := Cmp.ble_of_not_blt h
          rw [h₁, h₂] at hba
          exact Cmp.beq_comm b.1 a.1 ▸ (by simpa using hba)
        have heq' : Cmp.beq b.1 a.1 = true := Cmp.beq_comm a.1 b.1 ▸ heq
        rcases Nat.le_total a.2 b.2 with h₃ | h₃
        · left; simpa [heq, Nat.ble_eq] using h₃
        · right; simpa [heq', Nat.ble_eq] using h₃
  ble_trans ha hb := by
    rcases Cmp.prod_ble_iff.mp ha with h₁ | ⟨h₁, h₂⟩
    · rcases Cmp.prod_ble_iff.mp hb with h₃ | ⟨h₃, _⟩
      · exact Cmp.prod_ble_iff.mpr (Or.inl (Cmp.blt_trans h₁ h₃))
      · exact Cmp.prod_ble_iff.mpr (Or.inl (h₃ ▸ h₁))
    · rcases Cmp.prod_ble_iff.mp hb with h₃ | ⟨h₃, h₄⟩
      · exact Cmp.prod_ble_iff.mpr (Or.inl (h₁ ▸ h₃))
      · exact Cmp.prod_ble_iff.mpr (Or.inr ⟨h₁.trans h₃, Nat.le_trans h₂ h₄⟩)
  ble_antisymm ha hb := by
    rcases Cmp.prod_ble_iff.mp ha with h₁ | ⟨h₁, h₂⟩
    · rcases Cmp.prod_ble_iff.mp hb with h₃ | ⟨h₃, _⟩
      · exact absurd h₃ (by rw [Cmp.not_blt_of_blt h₁]; exact Bool.false_ne_true)
      · exact absurd (h₃ ▸ h₁) (by simp [Cmp.blt_irrefl])
    · rcases Cmp.prod_ble_iff.mp hb with h₃ | ⟨h₃, h₄⟩
      · exact absurd (h₁ ▸ h₃) (by simp [Cmp.blt_irrefl])
      · exact Prod.ext h₁ (Nat.le_antisymm h₂ h₄)

end Tcs
