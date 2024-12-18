import Mathlib.Tactic

section LeftRight

/-
syntax "left"... [Lean.Parser.Tactic.left]
  Applies the first constructor when
  the goal is an inductive type with exactly two constructors, or fails otherwise.
-/
#help tactic left

/-
syntax "right"... [Lean.Parser.Tactic.right]
  Applies the second constructor when
  the goal is an inductive type with exactly two constructors, or fails otherwise.
-/
#help tactic right

-- practice
example : True ∨ False := by
  sorry

example {p q : Prop} (h : q) : p ∨ q := by
  sorry

end LeftRight
