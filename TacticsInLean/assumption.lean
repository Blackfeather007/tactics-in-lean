import Mathlib.Tactic

#help tactic assumption

example (a b : ℝ) (h : a = b) : a = b := by sorry

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by sorry

example (x y z : ℚ) (h₀ : (x : ℝ) ≤ (y : ℝ)) (h₁ : (y : ℝ) ≤ (z : ℝ)) : x ≤ z := by sorry
