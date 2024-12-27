import Mathlib.Tactic

#help tactic rewrite
#help tactic rw
#help tactic nth_rw
#help tactic erw

section p₁
example (α : Type*) (a b c : α) (h₁ : a = b) (h₂ : b = c) : a = c := sorry
end p₁

section p₂
example (a : ℕ) (h : 100 + 1 = a) : a = 101 := sorry
end p₂

section p₃
noncomputable def π : ℝ := Real.arccos (-1 : ℝ)
example : Real.cos π = -1 := sorry
end p₃

section p₄
example (a b : ℕ) (h₁ : 0 < b) (h₂ : b ≤ a) : a / b = (a - b) / b + 1 := sorry
end p₄

section p₅
example {α : Type*} [Lattice α] (a b c : α) (h₁ : ∀ x y : α, x ⊓ (x ⊔ y) = x) (h₂ : ∀ x y : α, x ⊔ x ⊓ y = x) (h₃ : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := sorry
end p₅

section p₆
def FnEven (f : ℝ → ℝ) : Prop :=
  ∀ x, f x = f (-x)
def FnOdd (f : ℝ → ℝ) : Prop :=
  ∀ x, f x = -f (-x)

example (f g : ℝ → ℝ) (ef : FnEven f) (og : FnOdd g) : FnOdd fun x ↦ f x * g x := sorry
end p₆

section p₇
example (f : ℝ → ℝ) (h : ¬Monotone f) : ∃ x y, x ≤ y ∧ f y < f x := sorry
end p₇

section p₈
example (a : ℝ) (p : ℝ → Prop) (h : ∀ r, p (r * a)) (k : ℝ) : p (k * a + a) := sorry
end p₈

section p₉
example (a : ℝ) (p : ℝ → Prop) (h : ∀ r, p (r * a)) (k : ℝ) : p (k * a + a - a) := sorry
end p₉

section p₁₀
open Set Notation

example {α : Type*} {A : Set α} {S : Set (Set α)} : A ↓∩ (⋃₀ S) = ⋃₀ { (A ↓∩ B) | B ∈ S } := sorry
end p₁₀
