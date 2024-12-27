import Mathlib.Tactic

#help tactic constructor

example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by sorry

example (m n k : ℕ) : lcm m n ∣ k ↔ m ∣ k ∧ n ∣ k := by sorry

example (x : ℝ) (h : ∀ ε > 0, x ≤ ε) : x ≤ 0 := by sorry

example {x y : ℝ} : x ≤ y ∧ ¬y ≤ x ↔ x ≤ y ∧ x ≠ y := by sorry

def f : ℝ → ℝ := fun x => x

open Function in
example : Bijective f := by sorry

example (a b c : ℤ) (hab : b ≤ a) (hac : a ≤ c) : a ∈ Finset.Icc b c := by sorry

example (p q r : Prop) (hp : p) (hq : q) (hr : r) : ((p ∧ q) ∧ r) ∧ (p ∨ q) := by sorry

structure IsLinear (f : ℝ → ℝ) where
  is_additive : ∀ x y, f (x + y) = f x + f y
  preserves_mul : ∀ x c, f (c * x) = c * f x

example : let f : ℝ → ℝ := fun x => x; IsLinear f := by sorry

structure Group₁ (α : Type*) [Add α] [Neg α] [Zero α] where
  add_assoc : ∀ x y z : α, Add.add (Add.add x y) z = Add.add x (Add.add y z)
  add_one : ∀ x : α, Add.add x Zero.zero = x
  one_add : ∀ x : α, Add.add Zero.zero x = x
  inv_add_cancel : ∀ x : α, Add.add (Neg.neg x) x = Zero.zero

example : Group₁ ℚ := by sorry
