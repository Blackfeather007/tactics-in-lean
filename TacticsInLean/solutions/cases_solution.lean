import Mathlib.Tactic

section cases

#help tactic cases

example (x : ℤ) (h : x = 1 ∧ x > 0) : x = 1 := by
  cases' h with h1 h2
  exact h1

example (p q : Prop) (h : p ∨ q) : q ∨ p := by
  cases' h with hp hq
  · exact Or.inr hp
  · exact Or.inl hq

example (x : ℤ) (h : x > 0 ∨ x < 0) : x ≠ 0 := by
  cases' h with hp hq
  · exact Ne.symm (Int.ne_of_lt hp)
  · exact Ne.symm (Int.ne_of_gt hq)

example (x : ℤ) (h : x = 2 ∨ x = 3) : x ∣ 6 := by
  cases' h with h1 h2
  · rw [h1]
    use 3
    rfl
  · rw [h2]
    use 2
    rfl

example (x : ℤ) (h : ∃ r : ℤ, r * x ≠ 0) : x ≠ 0 := by
  cases' h with r hr
  by_contra h1
  rw [h1, mul_zero] at hr
  exact hr rfl

example (x y : ℤ) (h1 : 2 ∣ x) (h2 : 2 ∣ y) : 2 ∣ x + y := by
  cases' h1 with x' hx
  cases' h2 with y' hy
  use x' + y'
  rw [hx, hy, mul_add]

end cases
