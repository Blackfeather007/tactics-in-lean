import Mathlib.Tactic
import Mathlib.Data.Real.Irrational
section cases

open Nat

example (n : Nat) (h : n ≠ 0) : succ (pred n) = n := by
  sorry

example (x : ℤ) (h : x > 0 ∨ x < 0) : x ≠ 0 := by
  sorry

end cases

section rcases

example {x : ℝ} (h : x = 1 ∨ x = 2) : x ^ 2 - 3 * x + 2 = 0 := by
  sorry

example {x y : ℝ} (h : x = 2 ∨ y = -2) : x * y + 2 * x = 2 * y + 4 := by
  sorry

def f (_ : List Empty) (b : Bool) := b
@[simp]
theorem lem2 (a b : Bool) (x y : List Empty)
  (h : f x a = f y b) : x = y := by
    sorry

open ZMod
theorem mul_inv_of_unit' {n : ℕ} {a : ZMod n} (h : IsUnit a) : a * a⁻¹ = 1 := by
  sorry

class inductive Something where
 | oneThing : Something
 | anotherThing : Something
instance instOne : Something := Something.oneThing
@[instance]
def instAnother : Something := Something.anotherThing
example [s : Something] : s = Something.oneThing ∨ s = Something.anotherThing := by
  sorry

end rcases

section rintro

variable {α : Type*}
variable (s t u : Set α)
open Set
example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  rw [subset_def, inter_def, inter_def]
  rw [subset_def] at h
  simp only [mem_setOf]
  sorry

example : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  sorry

example : s ∩ (s ∪ t) = s := by
  sorry

example : s ∪ s ∩ t = s := by
  sorry

end rintro

section obtain

example (h : ∃ x, x > 0) : ∃ y, y > 0 := by
  sorry

example {α β : Prop} (h : α ∨ β) : α ∨ β := by
  sorry

example {α β : Prop} (h : α → β) : α → β := by
  sorry

example {x y : ℝ} (h : ∀ x, ∃ y, x + y = 0) : ∀ x, ∃ y, x + y = 0 := by
  sorry

example (h : ∃ x, ∃ y, x + y = 3) : ∃ x, ∃ y, x + y = 3 := by
  sorry

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a
def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a
theorem fnUb_add {f g : ℝ → ℝ} {a b : ℝ} (hfa : FnUb f a) (hgb : FnUb g b) :
    FnUb (fun x ↦ f x + g x) (a + b) := fun x ↦ add_le_add (hfa x) (hgb x)
example {f g : ℝ → ℝ} (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  sorry

end obtain

section induction

example (n : ℕ) : 2 * ∑ i : ℕ in Finset.range (n + 1), i = n * (n + 1) := by
  sorry

example (a b c : ℕ) (ha : a ≠ 0) (h : a * b = a * c) : b = c := by
  sorry

#check Fin.induction
example (n : ℕ) (f : Fin (n + 2) → Fin (n + 2)) (hf : ∀ i < Fin.last (n + 1), f (i + 1) = f i + 1) : Function.Injective f := by
  have aux (x : Fin (n + 2)) : f x = f 0 + x := by
    sorry
  sorry

end induction

section tactic_match

variable {x y : ℝ}
example : x < |y| → x < y ∨ x < -y := by
  sorry

end tactic_match
