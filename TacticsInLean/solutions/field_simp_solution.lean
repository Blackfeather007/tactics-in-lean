import Mathlib.Tactic

example (a b c d x y : ℂ) (hx : x ≠ 0) (hy : y ≠ 0) :
    a + b / x + c / x^2 + d / x^3 = a + x⁻¹ * (y * b / y + (d / x + c) / x) := by
  field_simp
  ring

example (a b : ℝ) (ha : a ≠ 0) (h : a * b - a = 0) : b = 1 := by
  rw [sub_eq_zero] at h
  field_simp at h
  assumption

/- Try different ways to proof tedious calculation -/
example (a b c d : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (h : a * a * b * c - a * b * d = 0) : a * c = d := by
  rw [sub_eq_zero] at h
  apply_fun (· / (a * b)) at h
  convert h using 1 <;> field_simp
  ring

example (a b c d : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (h : a * a * b * c - a * b * d = 0) : a * c = d := by
  rw [sub_eq_zero] at h
  rw [← mul_right_inj' (by field_simp : a * b ≠ 0)]
  convert h using 1
  ring

example (x : ℝ) (h : x ^ 2 / (1 + x ^ 2) = 2) :
    1 / (1 + x ^ 2) = - 1 := by
  field_simp at *
  linear_combination -h


/-
Let x,y,z be real numbers greater than 1 such that 1/x + 1/y + 1/z = 2. Prove that
√(x + y + z) ≥ √(x - 1) + √(y - 1) + √(z - 1).
Proof: By the Cauchy-Schwarz inequality, we have
(√(x - 1) + √(y - 1) + √(z - 1))^2 ≤ (x + y + z)((x - 1)/x + (y - 1)/y + (z - 1)/z) = x + y + z = (√(x + y + z))^2.
Note that (x - 1) / x + (y - 1) / y + (z - 1) / z = 1,
so this yields √(x + y + z) ≥ √(x - 1) + √(y - 1) + √(z - 1).
-/
#check Finset.sum_mul_sq_le_sq_mul_sq -- Cauchy-Schwarz inequality we need

theorem inequality (x y z : ℝ)
    (hx : x > 1) (hy : y > 1) (hz : z > 1)
    (h : 1 / x + 1 / y + 1 / z = 2) :
    √(x + y + z) ≥ √(x - 1) + √(y - 1) + √(z - 1) := by
  suffices x + y + z ≥ (√(x - 1) + √(y - 1) + √(z - 1))^2 by
    exact Real.le_sqrt_of_sq_le this
  have h : (x-1)/x+(y-1)/y+(z-1)/z = 1 := by
    field_simp
    field_simp at h
    linarith
  suffices (x + y + z) * ((x-1)/x+(y-1)/y+(z-1)/z) ≥ (√(x-1)+√(y-1)+√(z-1))^2 by
    rw [h] at this
    linarith
  convert_to (∑ i : Fin 3, (![√x, √y, √z] i)^2) * (∑ i : Fin 3, (![√((x-1)/x), √((y-1)/y), √((z-1)/z)] i)^2) ≥ (∑ i : Fin 3, ![√x, √y, √z] i * (![√((x-1)/x), √((y-1)/y), √((z-1)/z)] i))^2
  · simp [Fin.sum_univ_three]
    field_simp
    rw [Real.sq_sqrt, Real.sq_sqrt, Real.sq_sqrt]
    all_goals simp
    all_goals linarith
  . simp [Fin.sum_univ_three]
    field_simp
  apply Finset.sum_mul_sq_le_sq_mul_sq
