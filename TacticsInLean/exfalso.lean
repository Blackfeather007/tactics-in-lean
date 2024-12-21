import Mathlib.Tactic

#help tactic exfalso

section p₁
example (h : False) : 1 = 2 := sorry
end p₁

section p₂
example (p q : Prop) (h₁ : p ∧ q) (h₂ : p → ¬q) : ∃ n : ℕ, ∀ m : ℕ, m ≤ n := sorry
end p₂

section p₃
example (n : ℕ) [NeZero n] (x y : ZMod n) : (x + y).val = (x.val + y.val) % n := sorry
end p₃

section p₄
example (x : Fin 0) : ∀ n : ℕ, ∃ x y z : ℤ, x ^ n + y ^ n = z ^ n := sorry
end p₄

section p₅
example (p : ℕ) (hp : p.Prime) (h₁ : ∃ a b, p = a ^ 2 + b ^ 2) (h₂ : p % 4 = 3) : p = 2 := sorry
end p₅
