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

example : (3.141 : ℝ) + 2.718 = 5.859 := by
  norm_num

/- Sometimes norm_num calls simp, but it's not the correct usage-/
example {x : Nat} : x + 0 = x := by norm_num

example {x : ℝ} (h : x = 1 ∨ x = 2) : x ^ 2 - 3 * x + 2 = 0 := by
  rcases h with rfl | rfl <;> norm_num

-- example {x : Nat} : x + 0 = x := by norm_num1

example : 3 / 2 = 1.5 := by

  sorry
example : |(3 : ℝ) - 7| = 4 := by
  norm_num

def Bounded (f : ℝ → ℝ) (Dom: Set ℝ) : Prop :=
  ∃ M, ∀ x ∈ Dom, |f x| ≤ M

example : ¬Bounded (fun x : ℝ ↦ 1 / x) (Set.Ioo 0 1) := by
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
