import Mathlib.Tactic

#help tactic trivial
-- #help tactic triv -- **Note** But this in fact has been moved!

section p₁
example : True := by
  trivial
end p₁

section p₂
example : 1 = 1 := by
  trivial
end p₂

section p₃
example (p : Prop) (h : p) (hn : ¬p) : 1 = 3 := by
  trivial
end p₃

section p₄
universe u
example (h : False) : Sort u := by
  trivial
end p₄

section p₅
example (p : Prop) (h : p) : p := by
  trivial
end p₅

section p₆
example : Nat.gcd 18 8 = 2 := by
  trivial
end p₆

section p₇
example (p q : Prop) (h₁ : p) (h₂ : q) : p ∧ q := by
  trivial
end p₇

section p₈
example (p q : Prop) (h : p) : p ∨ q := by
  -- trivial  -- `trivial` fails to prove a `Or` proposition.
  exact Or.inl h
end p₈
