import Mathlib.Tactic

example {n : ℕ} : n % 4 < 4 := Nat.mod_lt n (by norm_num)

example {x : ℝ} (h : x = 1 ∨ x = 2) : x ^ 2 - 3 * x + 2 = 0 := by
  rcases h with rfl | rfl <;> norm_num

example (f : ℝ → ℝ) (h₀ : ∀ x, f x =  3 * Real.sqrt (2 * x - 7) - 8) : f 16 = 7:= by
  simp [h₀]
  rw [show (2 : ℝ) * 16 - 7 = 5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num

example : ∃ r : ℤ, 0 ≤ r ∧ r < 3 ∧ 11 ≡ r [ZMOD 3] := by
  use 2
  constructor
  · norm_num
  constructor
  · norm_num
  · dsimp [Int.ModEq]

example : ((-1 : ℝ) ^ 3) ^ (2 / 3 : ℝ) = Real.cos (2 /3 * Real.pi) := by
  rw [Real.rpow_def_of_neg]
  simp
  norm_num
