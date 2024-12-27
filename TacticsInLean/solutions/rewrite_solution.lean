import Mathlib.Tactic

#help tactic rewrite
#help tactic rw
#help tactic nth_rw
#help tactic erw

section p₁
example (α : Type*) (a b c : α) (h₁ : a = b) (h₂ : b = c) : a = c := by
  rw [h₁, h₂]
end p₁

section p₂
example (a : ℕ) (h : 100 + 1 = a) : a = 101 := by
  rw [← h]
end p₂

section p₃
noncomputable def π : ℝ := Real.arccos (-1 : ℝ)
example : Real.cos π = -1 := by
  rw [π, Real.cos_arccos (le_refl _) (by norm_num)]
end p₃

section p₄
example (a b : ℕ) (h₁ : 0 < b) (h₂ : b ≤ a) : a / b = (a - b) / b + 1 := by
  rw [Nat.div_eq_sub_div]
  · exact h₁
  · exact h₂
end p₄

section p₅
example {α : Type*} [Lattice α] (a b c : α) (h₁ : ∀ x y : α, x ⊓ (x ⊔ y) = x) (h₂ : ∀ x y : α, x ⊔ x ⊓ y = x) (h₃ : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  rw [h₃, @inf_comm _ _ (a ⊔ b), h₁, @inf_comm _ _ (a ⊔ b), h₃, ← sup_assoc, @inf_comm _ _ c a,
    h₂, inf_comm]
end p₅

section p₆
def FnEven (f : ℝ → ℝ) : Prop :=
  ∀ x, f x = f (-x)
def FnOdd (f : ℝ → ℝ) : Prop :=
  ∀ x, f x = -f (-x)

example (f g : ℝ → ℝ) (ef : FnEven f) (og : FnOdd g) : FnOdd fun x ↦ f x * g x := by
  intro x
  dsimp
  rw [ef, og, neg_mul_eq_mul_neg]
end p₆

section p₇
example (f : ℝ → ℝ) (h : ¬Monotone f) : ∃ x y, x ≤ y ∧ f y < f x := by
  rw [Monotone] at h
  push_neg  at h
  exact h
end p₇

section p₈
example (a : ℝ) (p : ℝ → Prop) (h : ∀ r, p (r * a)) (k : ℝ) : p (k * a + a) := by
  nth_rw 2 [← one_mul a]
  rw [← add_mul]
  exact h _
end p₈

section p₉
example (a : ℝ) (p : ℝ → Prop) (h : ∀ r, p (r * a)) (k : ℝ) : p (k * a + a - a) := by
  nth_rw 2 3 [← one_mul a]
  rw [← add_mul, ← sub_mul]
  exact h _
end p₉

section p₁₀
open Set Notation

example {α : Type*} {A : Set α} {S : Set (Set α)} : A ↓∩ (⋃₀ S) = ⋃₀ { (A ↓∩ B) | B ∈ S } := by
  -- change _ = ⋃₀ ((fun (s : Set α) => A ↓∩ s) '' S)
  -- rw [sUnion_image]
  erw [sUnion_image]
  simp_rw [sUnion_eq_biUnion, preimage_iUnion]
end p₁₀
