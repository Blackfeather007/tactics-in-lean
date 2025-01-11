import Mathlib.Tactic

#help tactic constructor

example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor
  · exact hp
  · exact hq

example (m n k : ℕ) : lcm m n ∣ k ↔ m ∣ k ∧ n ∣ k := by
  constructor
  · intro h
    constructor
    · apply (dvd_lcm_left _ _ ).trans h
    · apply (dvd_lcm_right _ _).trans h
  · intro h
    apply and_imp.2
    apply lcm_dvd
    exact h

example (x : ℝ) (h : ∀ ε > 0, x ≤ ε) : x ≤ 0 := by
  contrapose! h
  use x / 2
  constructor <;> linarith

example {x y : ℝ} : x ≤ y ∧ ¬y ≤ x ↔ x ≤ y ∧ x ≠ y := by
  constructor
  · rintro ⟨h0, h1⟩
    constructor
    · exact h0
    intro h2
    apply h1
    rw [h2]
  rintro ⟨h0, h1⟩
  constructor
  · exact h0
  intro h2
  apply h1
  apply le_antisymm h0 h2

def f : ℝ → ℝ := fun x => x

open Function in
example : Bijective f := by
  constructor
  · intro a b hab
    dsimp [f] at hab
    exact hab
  · intro a
    use a
    dsimp [f]

example (a b c : ℤ) (hab : b ≤ a) (hac : a ≤ c) : a ∈ Finset.Icc b c := by
  apply Finset.mem_Icc.2
  constructor
  · exact hab
  · exact hac

example (p q r : Prop) (hp : p) (hq : q) (hr : r) : ((p ∧ q) ∧ r) ∧ (p ∨ q) := by
  constructorm* _ ∧ _, _ ∧ _, _ ∨ _
  exact hp
  exact hq
  exact hr
  exact hp

structure IsLinear (f : ℝ → ℝ) where
  is_additive : ∀ x y, f (x + y) = f x + f y
  preserves_mul : ∀ x c, f (c * x) = c * f x

example : let f : ℝ → ℝ := fun x => x; IsLinear f := by
  intro f
  constructor
  · intro x y
    dsimp [f]
  · intro x c
    dsimp [f]

structure Group₁ (α : Type*) [Add α] [Neg α] [Zero α] where
  add_assoc : ∀ x y z : α, Add.add (Add.add x y) z = Add.add x (Add.add y z)
  add_one : ∀ x : α, Add.add x Zero.zero = x
  one_add : ∀ x : α, Add.add Zero.zero x = x
  inv_add_cancel : ∀ x : α, Add.add (Neg.neg x) x = Zero.zero

example : Group₁ ℚ := by
  constructor
  · intro x y z
    apply add_assoc
  · intro x
    apply add_zero
  · intro x
    apply zero_add
  · intro x
    apply neg_add_cancel
