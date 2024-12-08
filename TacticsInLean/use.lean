import Mathlib.Tactic


section Use

/-
syntax "use"... [Mathlib.Tactic.useSyntax]
  `use e₁, e₂, ⋯` is similar to `exists`, but unlike `exists` it is equivalent to applying the tactic
  `refine ⟨e₁, e₂, ⋯, ?_, ⋯, ?_⟩` with any number of placeholders (rather than just one) and
  then trying to close goals associated to the placeholders with a configurable discharger (rather
  than just `try trivial`).

  Examples:

  ```lean
  example : ∃ x : Nat, x = x := by use 42

  example : ∃ x : Nat, ∃ y : Nat, x = y := by use 42, 42

  example : ∃ x : String × String, x.1 = x.2 := by use ("forty-two", "forty-two")
  ```
-/
#help tactic use

-- Exercise

example : ∃ n : ℕ, n > 2024 := by
  sorry

example : ∃ m n : ℕ, m + n ∣ 2024 := by
  sorry

example : ∃ t : ℕ × ℕ, t.1 - t.2 = 2024 := by
  sorry

example : ∃ n : ℕ, ∀ m < 2024, ∃ x, x > n * m := by
  sorry

example : ∃ s : Set ℕ, ∀ x ∈ s, 3 ∣ x := by
  sorry

example : ∃ a ∈ {n : ℕ | Even n}, 3 ∣ a := by
  sorry

example : ∀ ε > 0, ∃ n > 0 , Real.exp (- n) < ε := by
  sorry

example : ∀ a b c : ℝ, ∃ x : ℝ, a ≠ 0 → b ^ 2 - 4 * a * c ≥ 0 → a * x ^ 2 + b * x + c = 0 := by
  sorry

example : ∃ f : ℕ → ℕ, ∀ x : ℕ, x > 0 →
  f x < ∑ i ∈ Finset.range 2024, i * x ^ i ∧ f x > ∑ i ∈ Finset.range 2023, i * x ^ i:= by
  sorry

structure UpperPlanePoint where
  x : ℝ
  y : ℝ
  y_pos : y > 0

def dist' (p q : UpperPlanePoint) := |p.x - q.x| ⊔ |p.y - q.y|

example : ∃ p q : UpperPlanePoint, dist' p q > 2024 := by
  sorry

example : ∃ m n : ℕ,  m ≠ n ∧ n.divisors.sum id = m + n ∧ m.divisors.sum id = m + n := by
  sorry

end Use
