import Mathlib.Tactic

#help tactic norm_num

example : (1 : ℝ) + 1 = 2 := by
  norm_num

example : (1 : ℚ) + 1 ≤ 3 := by
  norm_num

example : (1 : ℤ) + 1 < 4 := by
  norm_num

example : (1 : ℂ) + 1 ≠ 5 := by
  norm_num

example : (1 : ℕ) + 1 ≠ 6 := by
  norm_num

example : ¬ (5 : ℤ) ∣ 12 := by
  norm_num

example : (3.141 : ℝ) + 2.718 = 5.859 := by
  norm_num

example : 3.141 + 2.718 = 5.859 := by
  norm_num -- it cannot deal with Floats
  sorry

/- `norm_num` can even solve absolute values-/
example : |(3 : ℝ) - 7| = 4 := by
  norm_num

/- Sometimes `norm_num` calls `simp`, but it's not the correct usage-/
example {x : Nat} : x + 0 = x := by norm_num

/- `norm_num1` is a basic version of `norm_num` that does not call `simp` -/
-- example {x : Nat} : x + 0 = x := by norm_num1

example {n : ℕ} : n % 4 < 4 := by sorry

example {x : ℝ} (h : x = 1 ∨ x = 2) : x ^ 2 - 3 * x + 2 = 0 := by
  sorry

example : ∃ r : ℤ, 0 ≤ r ∧ r < 3 ∧ 11 ≡ r [ZMOD 3] := by sorry


example (f : ℝ → ℝ) (h₀ : ∀ x, f x =  3 * Real.sqrt (2 * x - 7) - 8) : f 16 = 7:= by
  sorry

/- use `Real.rpow_def_of_neg`-/
example : ((-1 : ℝ) ^ 3) ^ (2 / 3 : ℝ) = Real.cos (2 /3 * Real.pi) := by
  sorry

/-
A discussion of the `norm_num` tactic.
https://leanprover.zulipchat.com/#narrow/channel/113489-new-members/topic/How.20to.20do.201.20.2B.201.20.3D.202
-/
variable {n : ℕ}

open Nat

example : (n + 1 + 1) = (n + 2) := by norm_num

example : (n + 1 + 1)! = (n + 2)! := by norm_num

-- example : (n + 1 + 1) / 2 = (n + 2) / 2 := by norm_num  -- fails
example : (n + 1 + 1) / 2 = (n + 2) / 2 := by omega  -- succeeds
