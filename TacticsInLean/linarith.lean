import Mathlib.Tactic

section linarith

#help tactic linarith

/-
The linarith tactic solves certain kinds of linear equalities and inequalities in concrete types such as the naturals or reals.
-/


/- Hint: try to use `lt_of_lt_of_le` and `add_lt_add` to prove it -/
example {a b c d : ℝ} (h1 : a < b) (h2 : b ≤ c) (h3 : c = d) : a + a < d + b := by
  sorry

example {a b c d : ℝ} (h1 : a < b) (h2 : b ≤ c) (h3 : c = d) : a + a < d + b := by
  linarith -- linarith can solve this obvious inequality

example {n : ℕ} (h : n = 5) : ¬ n = 1 := by
  intro hn
  linarith -- linarith can find contradiction

example (x y z : ℚ) (h1 : 2 * x < 3 * y) (h2 : - 4 * x + 2 * z < 0)
    (h3 : 12 * y - 4 * z < 0) : False := by
  linarith

example {a b : ℚ} (H : a ≤ 1 ∧ a + b ≤ 3) : 2 * a + b ≤ 4 := by
  linarith

example {x y : ℝ} (h1 : x = 5) (h2 : 1 ≤ y) : x * y + x ≥ 10 := by
  rw [h1] -- `linarith` will fail without this rw, since it can only handle linear arithmetic
  linarith

example {x y : ℝ} (h1 : y ≤ x + 5) (h2 : x ≤ -2) : x + y < 2 := by
  sorry

example (x ε : ℝ) (hε : 0 < ε) (h1 : x < ε / 2) (h2 : -x < ε / 2) : |x| < ε := by
  sorry

example {p q : ℝ} (h: (p - 1) * (q - 2) = 0): p = 1 ∨ q = 2 := by
  sorry

example (a b : ℝ) (ha : a ≠ 0) (h : a * b - a = 0) : b = 1 :=
  sorry


example (a b c d : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (h : a * a * b * c - a * b * d = 0) : a * c = d := by
  sorry

example {m n : ℚ} (hm : m ≠ 0) (h : ((3 / 4) * m) * (n - 120) = m * (n - 245)) : n = 620 := by
  sorry

example {a b c : ℝ} (ha : a ≤ b + c) (hb : b ≤ a + c) (hc : c ≤ a + b) :
    ∃ x y z, x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ a = y + z ∧ b = x + z ∧ c = x + y := by
  set x := (b - a + c) / 2 with hx_def
  set y := (a - b + c) / 2 with hy_def
  set z := (a + b - c) / 2 with hz_def
  sorry


/- linarith对Order的要求-/
-- example {α : Type*} [Preorder α] (x: α) (h: x < x) : False := by
--   linarith -- fails

example {α: Type*} [LinearOrderedCommRing α] (x : α) (h: x < x) : False := by
  linarith -- succeeds


end linarith


section nlinarith

#help tactic nlinarith


example {x : ℝ} (h : x ≤ -3) : x ^ 2 ≥ 9 := by nlinarith

example {n : ℕ} : n ^ 2 ≠ 2 :=
match n with
| 0 => sorry
| 1 => sorry
| n + 2 => sorry

end nlinarith
