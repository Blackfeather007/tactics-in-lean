import Mathlib.Tactic

section Positivity

/-
syntax "positivity"... [Mathlib.Tactic.Positivity.positivity]
  Tactic solving goals of the form `0 ≤ x`, `0 < x` and `x ≠ 0`.  The tactic works recursively
  according to the syntax of the expression `x`, if the atoms composing the expression all have
  numeric lower bounds which can be proved positive/nonnegative/nonzero by `norm_num`.  This tactic
  either closes the goal or fails.
-/

#help tactic positivity

-- practice

example {a : ℤ} (ha : 3 < a) : 0 ≤ a ^ 3 + a := by sorry

example {a : ℤ} (ha : 1 < a) : 0 < |(3:ℤ) + a| := by sorry

example {b : ℤ} : 0 ≤ max (-3) (b ^ 2) := by sorry

example (a b c d : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (h : a * a * b * c - a * b * d = 0) : a * c = d := by
  sorry

example : 0 < 5 - (-3) := by
  sorry

example : ¬ (5 : ℤ) ∣ 12 := by
  sorry

-- for teaching

-- example {n : ℕ} (hn : 0 < n) : (0 : ENNReal) < 1 / n := by
--   positivity -- fails


-- example (x : ℝ) (hx : 0 < x) : 0 < 5 + x := by
--   positivity --works :)

-- example : 0 < 5 - (-3) := by
--   positivity --works :)

-- example (x : ℝ) (hx : 0 < x) : 0 < 5 - (-x) := by
--   positivity --Doesn't work!

-- lemma foo (x : ℝ) : 0 < x := sorry

-- example (x : ℝ) : 0 < x := by
--   positivity -- fails as expected
--   sorry

-- example (x : ℝ) : 0 < x := by
--   have := foo x
--   positivity -- works as expected

-- example (x : ℝ) : 0 < x := by
--   positivity [foo x] -- cannot when 'linarith' can
--   sorry


-- example : emultiplicity 3 18 = 2 := by
--   rw [← padicValNat_eq_emultiplicity]
--   · norm_cast
--     sorry
--   positivity

end Positivity
