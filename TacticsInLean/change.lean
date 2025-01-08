import Mathlib.Tactic
import Mathlib.Data.Real.Irrational

#help tactic change

section p₁
example (f : ℕ → ℕ) (h : ∀ x, f x = 1) (x : ℕ) : (fun (x : ℕ) => f x) x + (fun (x : ℕ) => f x) x = 2 := sorry
end p₁

section p₂
example (f : ℕ → ℕ) (h : ∀ x, (fun (x : ℕ) => f x) x = 1) (x : ℕ) : f x + f x = 2 := sorry
end p₂

section p₃
#check Nat.sub_add_comm
example (n : ℕ) (x y : Fin n) : (x - y).val = (n + x.val - y.val) % n := sorry
end p₃

section p₄
example : let f : ℕ → ℕ := fun n => 2 * n; f (f 2) = 8 := sorry
end p₄

section p₅
example (a b c d : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hd : d > 0) (h₁ : a ≥ c) (h₂ : b ≥ d) : (a * b) ^ ((1 : ℝ) / 2) ≥ (c * d) ^ ((1 : ℝ) / 2) := sorry
end p₅

section p₆
example (α : Type*) (p : α → Prop) [DecidablePred p] (a : α) (hnp : ¬p a) : (not ∘ fun x => decide (p x)) a = true := sorry
end p₆

section p₇
example (a : ZMod 0) : ∃ (d : ℕ) (u : ZMod 0), a = u * d := sorry
end p₇
