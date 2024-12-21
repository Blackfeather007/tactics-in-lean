import Mathlib.Tactic

section cases

#help tactic cases

example (x : ℤ) (h : x = 1 ∧ x > 0) : x = 1 := by sorry

example (p q : Prop) (h : p ∨ q) : q ∨ p := by sorry

example (x : ℤ) (h : x > 0 ∨ x < 0) : x ≠ 0 := by sorry

example (x : ℤ) (h : x = 2 ∨ x = 3) : x ∣ 6 := by sorry

example (x : ℤ) (h : ∃ r : ℤ, r * x ≠ 0) : x ≠ 0 := by sorry

example (x y : ℤ) (h1 : 2 ∣ x) (h2 : 2 ∣ y) : 2 ∣ x + y := by sorry

end cases
