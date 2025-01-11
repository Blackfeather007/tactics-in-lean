import Mathlib.Tactic

#help tactic apply

example : 1 + 1 = 2 := by sorry

example (a b c : ℕ) : a * b * c = a * (b * c) := by sorry

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by sorry

example (a b : ℝ) (h : a ≤ b ∧ -a ≤ b) : |a| ≤ b := by sorry

example (a b : ℝ) : min a b = min b a := by sorry

example (a b : ℝ) (f : ℝ → ℝ) (h : a = b) : f a = f b := by sorry

example (a b : ℚ) (h : (a : ℝ) = (b : ℝ)) : a = b := by sorry
