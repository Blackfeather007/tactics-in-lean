import Mathlib.Tactic

section LeftRight

example : True ∨ False := by
  left
  trivial

example {p q : Prop} (h : q) : p ∨ q := by
  right
  exact h

end LeftRight
