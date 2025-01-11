import Mathlib.Tactic

#help tactic field_simp
/--
The goal of `field_simp` is to reduce an expression in a field to an expression of the form `n / d`
  where neither `n` nor `d` contains any division symbol, just using the simplifier (with a carefully
  crafted simpset named `field_simps`) to reduce the number of division symbols whenever possible by
  iterating the following steps:

  - write an inverse as a division
  - in any product, move the division to the right
  - if there are several divisions in a product, group them together at the end and write them as a
    single division
  - reduce a sum to a common denominator

  If the goal is an equality, this simpset will also clear the denominators, so that the proof
  can normally be concluded by an application of `ring`.

  `field_simp [hx, hy]` is a short form for
  `simp (disch := field_simp_discharge) [-one_div, -one_divp, -mul_eq_zero, hx, hy, field_simps]`

  Note that this naive algorithm will not try to detect common factors in denominators to reduce the
  complexity of the resulting expression. Instead, it relies on the ability of `ring` to handle
  complicated expressions in the next step.

  As always with the simplifier, reduction steps will only be applied if the preconditions of the
  lemmas can be checked. **This means that proofs that denominators are nonzero should be included**. The
  fact that a product is nonzero when all factors are, and that a power of a nonzero number is
  nonzero, are included in the simpset, but more complicated assertions (especially dealing with sums)
  should be given explicitly. If your expression is not completely reduced by the simplifier
  invocation, check the denominators of the resulting expression and provide proofs that they are
  nonzero to enable further progress.
-/


example (x : ℝ) (h : x > 0) : 1 / x + 1 = (x + 1) / x := by
  field_simp
  ring

example (x: ℝ) (h1: x > 0)  : (1 - x) / √x = 1/√x - √x  := by
  field_simp

example (a b c d x y : ℂ) (hx : x ≠ 0) (hy : y ≠ 0) :
    a + b / x + c / x^2 + d / x^3 = a + x⁻¹ * (y * b / y + (d / x + c) / x) := by
  sorry

/- An important example-/
example {a b : ℝ} (h : b ≠ 1) : a = (a * b - a) / (b - 1) := by
  field_simp [sub_ne_zero_of_ne h]
  ring

example (a b : ℝ) (ha : a ≠ 0) (h : a * b - a = 0) : b = 1 := by
  sorry

example (a b c d : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (h : a * a * b * c - a * b * d = 0) : a * c = d := by
  sorry

example (x : ℝ) (h : x ^ 2 / (1 + x ^ 2) = 2) :
    1 / (1 + x ^ 2) = - 1 := by
  sorry


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
  have h : (x - 1) / x + (y - 1) / y + (z - 1) / z = 1 := by
    sorry
  suffices (x + y + z) * ((x - 1) / x + (y - 1) / y + (z - 1) / z) ≥ (√(x - 1) + √(y - 1) + √(z - 1)) ^ 2 by
    sorry
  convert_to (∑ i : Fin 3, (![√x, √y, √z] i)^2) * (∑ i : Fin 3, (![√((x-1)/x), √((y-1)/y), √((z-1)/z)] i)^2) ≥ (∑ i : Fin 3, ![√x, √y, √z] i * (![√((x-1)/x), √((y-1)/y), √((z-1)/z)] i))^2
  · sorry
  . sorry
  apply Finset.sum_mul_sq_le_sq_mul_sq
