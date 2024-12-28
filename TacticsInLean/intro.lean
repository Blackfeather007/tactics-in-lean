import Mathlib.Tactic

section intro
#help tactic intro

/-
The `intro` tactic makes progress so long as the goal is a `let` or a pi type (e.g. an implication `⊢ P → Q`, function `ℝ → ℝ`, or universal quantifier `⊢ ∀ x, P x`).
-/

/- These examples just show how hypothesis and goals change after using `intro`-/
example (P Q : Prop) : P → Q := by
  intro p
  /- Tactic state
    P Q : Prop
    p : P
    ⊢ Q   -/
  sorry

example {α : Type*} (P : α → Prop) : ∀ x, P x := by
  intro y
  /- Tactic state
    α : Type u_1
    P : α → Prop
    y : α
    ⊢ P y
    -/
  sorry

example : let n := 1; let k := 2; n + k = 3 := by
  intros
  /- n✝ : Nat := 1
      k✝ : Nat := 2
      ⊢ n✝ + k✝ = 3 -/
  rfl

-- define a function `f : ℝ → ℝ` such that `f x = x ^ 2`
def square : ℝ → ℝ := by
  intro x
  exact x ^ 2

def square' : ℝ → ℝ := fun x ↦ x ^ 2

/- Some more complicated example-/
example : ∀ (a : ℕ), a + a = 2 * a := by
  intro a
  sorry

-- implicit arguments doesn't matter here
example : ∀ {a : ℕ}, a + a = 2 * a := by
  intro a
  sorry

-- `intro` can also introduce several variables at once
example : ∀ (a b c : ℕ), a + b + c = c + b + a := by
  intro a b c
  sorry

example : ∀ (a b c : ℕ), a + b + c = c + b + a := by
  intro a
  intro b
  intro c
  sorry

example : ∀ x : ℝ, 0 ≤ x → |x| = x := by sorry

/- notice that `→` is right associative-/
example : ∀ x y ε : ℝ, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by

  sorry

/- Here is an example that `intro` can unfold definition-/
def EvenFunc (f : ℝ → ℝ) : Prop := ∀ x, f x = f (-x)

example {f g : ℝ → ℝ} (hf : EvenFunc f) (hg : EvenFunc g) : EvenFunc (f + g) := by
  -- you can use `unfold EvenFunc` to make the goal more clear, but it is not necessary
  sorry

example : ∀ {f g : ℝ → ℝ}, EvenFunc f → EvenFunc g → EvenFunc (f + g) := by
  sorry

example (c : ℝ) : Function.Injective fun x ↦ x + c := by
  sorry

example {c : ℝ} (h : c ≠ 0) : Function.Injective fun x ↦ c * x := by
  sorry

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
