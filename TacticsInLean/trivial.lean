import Mathlib.Tactic

#help tactic trivial
-- #help tactic triv -- **Note** But this in fact has been moved!

section p₁
example : True := sorry
end p₁

section p₂
example : 1 = 1 := sorry
end p₂

section p₃
example (p : Prop) (h : p) (hn : ¬p) : 1 = 3 := sorry
end p₃

section p₄
universe u
example (h : False) : Sort u := sorry
end p₄

section p₅
example (p : Prop) (h : p) : p := sorry
end p₅

section p₆
example : Nat.gcd 18 8 = 2 := sorry
end p₆

section p₇
example (p q : Prop) (h₁ : p) (h₂ : q) : p ∧ q := sorry
end p₇

section p₈
example (p q : Prop) (h : p) : p ∨ q := sorry
end p₈
