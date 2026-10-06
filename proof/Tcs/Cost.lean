/-
  Cost model and asymptotic notation.

  A computation's cost is the pair (key comparisons, element moves). Both units are
  charged the way the C++ operations pay for them:

  * a key comparison is one evaluation of a `proj a <= proj b` / `proj a < proj b`
    test, which is what `Cmp.ble` / `Cmp.blt` model;
  * a move is one element assignment. `std::swap` of two elements is charged 3 (one
    temporary copy plus two assignments, exactly how `std::swap` is written for a
    non-trivial value type); rotating a range of length `m` is charged `2 * m`, an
    upper bound valid for every linear `rotate` implementation (a cyclic rotate moves
    each element exactly once, a reversal-based one at most twice; libstdc++ uses the
    former). Charging an upper bound here keeps the constants below valid for the
    real C++ code.

  `IsBigO` is stated for an input family with an explicit `size` function. That avoids
  the "worst case over all inputs of size `n`" (a supremum, which would need choice)
  and lets the constant be exhibited directly: `IsBigOWith c size f g` says
  `f i <= c * g (size i)` for *every* input `i`. It is therefore stronger than the
  usual reading of `f = O(g)`: the constant works for every input, not only
  asymptotically.
-/

namespace Tcs

/-! ## The two cost units -/

/-- The cost of a computation: how many key comparisons it performs and how many
element moves it spends. -/
structure Cost where
  cmp : Nat
  mv : Nat
  deriving DecidableEq, Repr

namespace Cost

instance : Zero Cost := ⟨⟨0, 0⟩⟩
instance : Add Cost := ⟨fun a b => ⟨a.cmp + b.cmp, a.mv + b.mv⟩⟩

/-- Componentwise order: `a ≤ b` when `a` spends at most what `b` does in both
units. Every cost bound below is stated in this order. -/
def le (a b : Cost) : Prop := a.cmp ≤ b.cmp ∧ a.mv ≤ b.mv

instance : LE Cost := ⟨le⟩

theorem le_def {a b : Cost} : a ≤ b ↔ a.cmp ≤ b.cmp ∧ a.mv ≤ b.mv := Iff.rfl

theorem le_refl (a : Cost) : a ≤ a := ⟨Nat.le_refl _, Nat.le_refl _⟩

theorem le_trans {a b c : Cost} (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c :=
  ⟨Nat.le_trans h₁.1 h₂.1, Nat.le_trans h₁.2 h₂.2⟩

theorem zero_le (a : Cost) : (0 : Cost) ≤ a := ⟨Nat.zero_le _, Nat.zero_le _⟩

theorem add_assoc (a b c : Cost) : a + b + c = a + (b + c) := by
  cases a; cases b; cases c
  simp only [HAdd.hAdd, Add.add, Cost.mk.injEq]
  exact ⟨Nat.add_assoc .., Nat.add_assoc ..⟩

theorem add_comm (a b : Cost) : a + b = b + a := by
  cases a; cases b
  simp only [HAdd.hAdd, Add.add, Cost.mk.injEq]
  exact ⟨Nat.add_comm .., Nat.add_comm ..⟩

theorem zero_add (a : Cost) : 0 + a = a := by
  cases a
  simp only [HAdd.hAdd, Add.add, Cost.mk.injEq]
  exact ⟨Nat.zero_add .., Nat.zero_add ..⟩

theorem add_zero (a : Cost) : a + 0 = a := by
  cases a
  simp only [HAdd.hAdd, Add.add, Cost.mk.injEq]
  exact ⟨Nat.add_zero .., Nat.add_zero ..⟩

theorem add_le_add {a b c d : Cost} (h₁ : a ≤ b) (h₂ : c ≤ d) : a + c ≤ b + d :=
  ⟨Nat.add_le_add h₁.1 h₂.1, Nat.add_le_add h₁.2 h₂.2⟩

theorem add_le_add_left (a : Cost) {b c : Cost} (h : b ≤ c) : a + b ≤ a + c :=
  add_le_add (le_refl a) h

theorem add_le_add_right {b c : Cost} (h : b ≤ c) (a : Cost) : b + a ≤ c + a :=
  add_le_add h (le_refl a)

theorem le_add_left (a b : Cost) : a ≤ a + b :=
  ⟨Nat.le_add_right _ _, Nat.le_add_right _ _⟩

theorem le_add_right (a b : Cost) : b ≤ a + b :=
  ⟨Nat.le_add_left _ _, Nat.le_add_left _ _⟩

theorem cmp_le_of_le {a b : Cost} (h : a ≤ b) : a.cmp ≤ b.cmp := h.1

theorem mv_le_of_le {a b : Cost} (h : a ≤ b) : a.mv ≤ b.mv := h.2

/-- One key comparison. -/
def cmp1 : Cost := ⟨1, 0⟩

/-- One element move. -/
def mv1 : Cost := ⟨0, 1⟩

/-- `n` key comparisons. -/
def cmpN (n : Nat) : Cost := ⟨n, 0⟩

/-- `n` element moves. -/
def mvN (n : Nat) : Cost := ⟨0, n⟩

/-- The cost of a swap of two elements: a temporary copy and two assignments. -/
def swap : Cost := ⟨0, 3⟩

/-- The cost of rotating a range of length `m`. -/
def rot (m : Nat) : Cost := ⟨0, 2 * m⟩

/-- A uniform bound of `n` in both units, used to turn a componentwise estimate into
a `≤` in the cost order. -/
def const (n : Nat) : Cost := ⟨n, n⟩

/-- The projection lemmas are `simp` lemmas: they turn cost arithmetic into `Nat`
arithmetic, which `omega` and `simp` then finish. -/
@[simp] theorem cmp_add (a b : Cost) : (a + b).cmp = a.cmp + b.cmp := rfl

@[simp] theorem mv_add (a b : Cost) : (a + b).mv = a.mv + b.mv := rfl

@[simp] theorem cmp_zero : (0 : Cost).cmp = 0 := rfl

@[simp] theorem mv_zero : (0 : Cost).mv = 0 := rfl

@[simp] theorem cmp_cmp1 : cmp1.cmp = 1 := rfl

@[simp] theorem mv_cmp1 : cmp1.mv = 0 := rfl

@[simp] theorem cmp_mv1 : mv1.cmp = 0 := rfl

@[simp] theorem mv_mv1 : mv1.mv = 1 := rfl

@[simp] theorem cmp_swap : swap.cmp = 0 := rfl

@[simp] theorem mv_swap : swap.mv = 3 := rfl

@[simp] theorem cmp_rot (m : Nat) : (rot m).cmp = 0 := rfl

@[simp] theorem mv_rot (m : Nat) : (rot m).mv = 2 * m := rfl

@[simp] theorem cmp_const (n : Nat) : (const n).cmp = n := rfl

@[simp] theorem mv_const (n : Nat) : (const n).mv = n := rfl

@[simp] theorem cmp_cmpN (n : Nat) : (cmpN n).cmp = n := rfl

@[simp] theorem mv_cmpN (n : Nat) : (cmpN n).mv = 0 := rfl

@[simp] theorem cmp_mvN (n : Nat) : (mvN n).cmp = 0 := rfl

@[simp] theorem mv_mvN (n : Nat) : (mvN n).mv = n := rfl

theorem cmpN_add (m n : Nat) : cmpN (m + n) = cmpN m + cmpN n := rfl

theorem mvN_add (m n : Nat) : mvN (m + n) = mvN m + mvN n := rfl

theorem cmpN_le_cmpN {m n : Nat} (h : m ≤ n) : cmpN m ≤ cmpN n := ⟨h, Nat.zero_le _⟩

theorem mvN_le_mvN {m n : Nat} (h : m ≤ n) : mvN m ≤ mvN n := ⟨Nat.zero_le _, h⟩

theorem const_le_const {m n : Nat} (h : m ≤ n) : const m ≤ const n := ⟨h, h⟩

theorem le_const {a : Cost} {n : Nat} (h₁ : a.cmp ≤ n) (h₂ : a.mv ≤ n) : a ≤ const n :=
  ⟨h₁, h₂⟩

end Cost

/-! ## Triangular numbers

Loop nests that scan a shrinking suffix are counted by `tri`, which avoids division
in every exact statement. -/

/-- `tri n = n + (n - 1) + ... + 1`, the number of pairs among `n` elements. -/
def tri : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) + tri n

theorem tri_succ (n : Nat) : tri (n + 1) = (n + 1) + tri n := rfl

theorem tri_zero : tri 0 = 0 := rfl

theorem tri_one : tri 1 = 1 := rfl

/-- `tri n ≤ n * n`: the sharp form from which the two square bounds below follow. -/
theorem tri_le_mul_self (n : Nat) : tri n ≤ n * n := by
  induction n with
  | zero => simp [tri]
  | succ n ih =>
      rw [tri_succ]
      have h : (n + 1) * (n + 1) = n * n + n + (n + 1) := by
        rw [Nat.mul_succ, Nat.add_mul, Nat.one_mul]
      rw [h]
      omega

/-- A `tri` is at most the next square. -/
theorem tri_le_sq (n : Nat) : tri n ≤ (n + 1) * (n + 1) :=
  Nat.le_trans (tri_le_mul_self n) (Nat.mul_le_mul (Nat.le_succ n) (Nat.le_succ n))

theorem two_mul_tri (n : Nat) : 2 * tri n = n * (n + 1) := by
  induction n with
  | zero => simp [tri]
  | succ n ih =>
      rw [tri_succ, Nat.mul_add, ih, Nat.mul_succ 2 n, Nat.mul_succ (n + 1) (n + 1),
        Nat.mul_succ (n + 1) n, Nat.mul_comm (n + 1) n]
      omega

theorem tri_eq_add_pred (n : Nat) : tri n = n + tri (n - 1) := by
  cases n with
  | zero => rfl
  | succ m => rw [tri_succ]; rfl

/-- `tri (m - 1) ≤ m * m`, the form used by the algorithms whose loops scan a
suffix of length `m`. -/
theorem tri_pred_le_sq (n : Nat) : tri (n - 1) ≤ n * n :=
  Nat.le_trans (tri_le_mul_self (n - 1)) (Nat.mul_le_mul (Nat.pred_le n) (Nat.pred_le n))

theorem tri_mono {m n : Nat} (h : m ≤ n) : tri m ≤ tri n := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih =>
      exact Nat.le_trans ih (by rw [tri_succ]; exact Nat.le_add_left _ _)

/-! ## Uniform big-O -/

/-- `f i ≤ c * g (size i)` for every input of the family. -/
def IsBigOWith {ι : Type u} (c : Nat) (size : ι → Nat) (f : ι → Nat) (g : Nat → Nat) : Prop :=
  ∀ i, f i ≤ c * g (size i)

/-- `f = O(g)` for an input family with an explicit size. -/
def IsBigO {ι : Type u} (size : ι → Nat) (f : ι → Nat) (g : Nat → Nat) : Prop :=
  ∃ c, IsBigOWith c size f g

theorem IsBigOWith.mono {ι : Type u} {c c' : Nat} {size : ι → Nat} {f : ι → Nat}
    {g : Nat → Nat} (h : c ≤ c') (hO : IsBigOWith c size f g) : IsBigOWith c' size f g :=
  fun i => Nat.le_trans (hO i) (Nat.mul_le_mul_right _ h)

/-- Weaken the bound function: it is enough to dominate `g` pointwise. -/
theorem IsBigOWith.of_le {ι : Type u} {c : Nat} {size : ι → Nat} {f : ι → Nat}
    {g g' : Nat → Nat} (h : ∀ n, g n ≤ g' n) (hO : IsBigOWith c size f g) :
    IsBigOWith c size f g' :=
  fun i => Nat.le_trans (hO i) (Nat.mul_le_mul_left _ (h _))

theorem IsBigO.ofWith {ι : Type u} {c : Nat} {size : ι → Nat} {f : ι → Nat}
    {g : Nat → Nat} (h : IsBigOWith c size f g) : IsBigO size f g :=
  ⟨c, h⟩

theorem IsBigOWith.add {ι : Type u} {c c' : Nat} {size : ι → Nat} {f₁ f₂ : ι → Nat}
    {g : Nat → Nat} (h₁ : IsBigOWith c size f₁ g) (h₂ : IsBigOWith c' size f₂ g) :
    IsBigOWith (c + c') size (fun i => f₁ i + f₂ i) g := by
  intro i
  rw [Nat.add_mul]
  exact Nat.add_le_add (h₁ i) (h₂ i)

theorem IsBigOWith.const_mul {ι : Type u} {c k : Nat} {size : ι → Nat} {f : ι → Nat}
    {g : Nat → Nat} (h : IsBigOWith c size f g) :
    IsBigOWith (k * c) size (fun i => k * f i) g := fun i => by
  rw [Nat.mul_assoc]
  exact Nat.mul_le_mul_left _ (h i)

/-- A measured cost both of whose components are `O(g)`: the comparison count and
the move count are each at most `c * g (size i)`. -/
def CostBigOWith {ι : Type u} (c : Nat) (size : ι → Nat) (f : ι → Cost) (g : Nat → Nat) : Prop :=
  ∀ i, f i ≤ Cost.const (c * g (size i))

/-- `f = O(g)` for a measured cost. -/
def CostBigO {ι : Type u} (size : ι → Nat) (f : ι → Cost) (g : Nat → Nat) : Prop :=
  ∃ c, CostBigOWith c size f g

theorem CostBigOWith.cmp {ι : Type u} {c : Nat} {size : ι → Nat} {f : ι → Cost}
    {g : Nat → Nat} (h : CostBigOWith c size f g) :
    IsBigOWith c size (fun i => (f i).cmp) g := fun i => (Cost.le_def.mp (h i)).1

theorem CostBigOWith.mv {ι : Type u} {c : Nat} {size : ι → Nat} {f : ι → Cost}
    {g : Nat → Nat} (h : CostBigOWith c size f g) :
    IsBigOWith c size (fun i => (f i).mv) g := fun i => (Cost.le_def.mp (h i)).2

theorem CostBigOWith.mono {ι : Type u} {c c' : Nat} {size : ι → Nat} {f : ι → Cost}
    {g : Nat → Nat} (h : c ≤ c') (hO : CostBigOWith c size f g) : CostBigOWith c' size f g :=
  fun i => Cost.le_trans (hO i) (Cost.const_le_const (Nat.mul_le_mul_right _ h))

theorem CostBigOWith.of_le {ι : Type u} {c : Nat} {size : ι → Nat} {f : ι → Cost}
    {g g' : Nat → Nat} (h : ∀ n, g n ≤ g' n) (hO : CostBigOWith c size f g) :
    CostBigOWith c size f g' :=
  fun i => Cost.le_trans (hO i) (Cost.const_le_const (Nat.mul_le_mul_left _ (h _)))

theorem CostBigO.ofWith {ι : Type u} {c : Nat} {size : ι → Nat} {f : ι → Cost}
    {g : Nat → Nat} (h : CostBigOWith c size f g) : CostBigO size f g :=
  ⟨c, h⟩

end Tcs
