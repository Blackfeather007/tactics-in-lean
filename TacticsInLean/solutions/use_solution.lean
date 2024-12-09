import Mathlib.Tactic


section Use

example : ∃ n : ℕ, n > 2024 := by
  use 2025
  decide

example : ∃ m n : ℕ, m + n ∣ 2024 := by
  use 1, 1
  decide

example : ∃ t : ℕ × ℕ, t.1 - t.2 = 2024 := by
  use ⟨2025, 1⟩
  decide

example : ∃ n : ℕ, ∀ m < 2024, ∃ x, x > n * m := by
  use 1
  intro m hm
  use m + 1
  norm_num

example : ∃ s : Set ℕ, ∀ x ∈ s, 3 ∣ x := by
  use {3}
  norm_num

example : ∃ a ∈ {n : ℕ | Even n}, 3 ∣ a := by
  use 6
  norm_num
  decide

example : ∀ ε > 0, ∃ n > 0 , Real.exp (- n) < ε := by
  intro ε εpos
  by_cases h : ε ≥ 1
  · use 1
    norm_num
    apply lt_of_lt_of_le (b := 1)
    norm_num
    exact h
  push_neg at h
  use - Real.log (ε / 2)
  norm_num
  constructor
  · apply Real.log_neg (by linarith) (by linarith)
  rw [Real.exp_log (by linarith)]
  linarith

example : ∀ a b c : ℝ, ∃ x : ℝ, a ≠ 0 → b ^ 2 - 4 * a * c ≥ 0 → a * x ^ 2 + b * x + c = 0 := by
  intro a b c
  use (- b + Real.sqrt (discrim a b c)) / (2 * a)
  intro ha h
  replace h : discrim a b c = Real.sqrt (discrim a b c) * Real.sqrt (discrim a b c) := by
    rw [← pow_two]
    exact Eq.symm (Real.sq_sqrt h)
  have := quadratic_eq_zero_iff ha h
  specialize this ((- b + Real.sqrt (discrim a b c)) / (2 * a))
  simp at this
  rw [← pow_two] at this
  assumption

example : ∃ f : ℕ → ℕ, ∀ x : ℕ, x > 0 →
  f x < ∑ i ∈ Finset.range 2024, i * x ^ i ∧ f x > ∑ i ∈ Finset.range 2023, i * x ^ i:= by
  use fun x => ∑ i ∈ Finset.range 2024, i * x ^ i - 2023 * x ^ 2023 + 1
  intro x hx
  simp
  have : ∑ i ∈ Finset.range 2024, i * x ^ i = ∑ i ∈ Finset.range 2023, i * x ^ i + 2023 * x ^ 2023 := by
      apply Finset.sum_range_succ
  constructor
  · rw [this]
    simp
    apply lt_of_lt_of_le (b := 2023 * x)
    linarith
    simp
    apply le_self_pow₀
    linarith; norm_num
  · rw [this]
    simp

structure UpperPlanePoint where
  x : ℝ
  y : ℝ
  y_pos : y > 0

def dist' (p q : UpperPlanePoint) := |p.x - q.x| ⊔ |p.y - q.y|

example : ∃ p q : UpperPlanePoint, dist' p q > 2024 := by
  let p : UpperPlanePoint := {
    x := 0
    y := 1
    y_pos := by norm_num
  }
  let q : UpperPlanePoint := {
    x := 0
    y := 2027
    y_pos := by norm_num
  }
  use p, q
  rw [dist']
  norm_num

example : ∃ m n : ℕ,  m ≠ n ∧ n.divisors.sum id = m + n ∧ m.divisors.sum id = m + n := by
  use 220, 284
  norm_num
  decide

end Use
