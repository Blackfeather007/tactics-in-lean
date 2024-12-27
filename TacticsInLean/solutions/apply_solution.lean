import Mathlib.Tactic

#help tactic apply

example : 1 + 1 = 2 := by
  apply one_add_one_eq_two

example (a b c : ℕ) : a * b * c = a * (b * c) := by
  apply mul_assoc a b c

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  apply le_trans
  · apply h₀
  · apply h₁

example (a b : ℝ) (h : a ≤ b ∧ -a ≤ b) : |a| ≤ b := by
  apply abs_le'.mpr h

example (a b : ℝ) : min a b = min b a := by
  apply le_antisymm
  · apply le_min
    · apply min_le_right
    apply min_le_left
  · apply le_min
    · apply min_le_right
    apply min_le_left

example (a b : ℝ) (f : ℝ → ℝ) (h : a = b) : f a = f b := by
  apply_fun f at h
  apply h

example (a b : ℚ) (h : (a : ℝ) = (b : ℝ)) : a = b := by
  apply_mod_cast h

