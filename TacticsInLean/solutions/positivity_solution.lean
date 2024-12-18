import Mathlib.Tactic

section Positivity

example {a : ℤ} (ha : 3 < a) : 0 ≤ a ^ 3 + a := by positivity

example {a : ℤ} (ha : 1 < a) : 0 < |(3:ℤ) + a| := by positivity

example {b : ℤ} : 0 ≤ max (-3) (b ^ 2) := by positivity

example (a b c d : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (h : a * a * b * c - a * b * d = 0) : a * c = d := by
  apply mul_left_cancel₀ (by positivity : a * b ≠ 0)
  linarith

example : 0 < 5 - (-3) := by
  positivity --works :) positivity invokes some NormNum logic

example : ¬ (5 : ℤ) ∣ 12 := by
  apply (Int.exists_lt_and_lt_iff_not_dvd (12 : ℤ) (by positivity : 0 < (5 : ℤ))).mp
  use 2
  norm_num

end Positivity
