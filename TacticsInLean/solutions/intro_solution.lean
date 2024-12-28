import Mathlib.Tactic

section intro

example : ∀ (a : ℕ), a + a = 2 * a := by
  intro a
  exact Eq.symm (Nat.two_mul a)

-- implicit arguments doesn't matter here
example : ∀ {a : ℕ}, a + a = 2 * a := by
  intro a
  exact (Nat.two_mul a).symm

example : ∀ (a b c : ℕ), a + b + c = c + b + a := by
  intro a b c
  rw [add_comm]
  nth_rw 2 [add_comm]
  rw [add_assoc]

example : ∀ (a b c : ℕ), a + b + c = c + b + a := by
  intro _ _ _
  ring

example : ∀ (a b c : ℕ), a + b + c = c + b + a := by
  intro a
  intro b
  intro c
  ring

example : ∀ x : ℝ, 0 ≤ x → |x| = x := by
  intro x hx
  exact abs_of_nonneg hx

/- notice that `→` is right associative-/
example : ∀ x y ε : ℝ, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intro x y ε epos ele hx hy
  calc
    |x * y| = |x| * |y| := by exact abs_mul x y
    _ ≤ |x| * ε := by
      apply mul_le_mul (by linarith) (by linarith) (abs_nonneg y) ( abs_nonneg x)
    _ < 1 * ε := by
      exact (mul_lt_mul_right epos).mpr (by linarith)
    _ = ε := by rw [one_mul]

/- Here is an example that `intro` can unfold definition-/
def EvenFunc (f : ℝ → ℝ) : Prop := ∀ x, f x = f (-x)

example {f g : ℝ → ℝ} (hf : EvenFunc f) (hg : EvenFunc g) : EvenFunc (f + g) := by
  -- you can use `unfold EvenFunc` to make the goal more clear, but it is not necessary
  intro x
  dsimp
  rw [hf, hg]

example : ∀ {f g : ℝ → ℝ}, EvenFunc f → EvenFunc g → EvenFunc (f + g) := by
  intro f g hf hg x
  show f x + g x = f (-x) + g (-x)
  rw [hf, hg]


#check add_right_injective
example (c : ℝ) : Function.Injective fun x ↦ x + c := by
  intro x₁ x₂ h'
  exact (add_left_inj c).mp h'

#check mul_right_injective₀
example {c : ℝ} (h : c ≠ 0) : Function.Injective fun x ↦ c * x := by
  intro x₁ x₂ h'
  exact mul_left_cancel₀ h h'

end intro

section intros

#help tactic intros
/- Since `intro` can also introduces one or more hypotheses, here is only some corner cases that `intros` is more convenient than `intro` -/

/- `intros x y ...` is equivalent to `intro x y ...` -/
example (p q : Prop) : p → q → p := by
  intros a b
  -- intro a b

  /- Tactic state
      a : p
      b : q
      ⊢ p      -/
  assumption

example (p q : Prop) : p → q → p := by
  intros
  /- Tactic state
      a✝¹ : p
      a✝ : q
      ⊢ p      -/
  assumption

example (p q : Prop) : p → q → p := by
  /- we can intro anonymous variables-/
  /- howerver, `intro` fails here-/
  intro _ _
  /- Tactic state
      a✝¹ : p
      a✝ : q
      ⊢ p      -/
  assumption


end intros
