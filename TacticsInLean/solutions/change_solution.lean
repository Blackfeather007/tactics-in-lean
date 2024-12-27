import Mathlib.Tactic
import Mathlib.Data.Real.Irrational

#help tactic change

section p₁
example (f : ℕ → ℕ) (h : ∀ x, f x = 1) (x : ℕ) : (fun (x : ℕ) => f x) x + (fun (x : ℕ) => f x) x = 2 := by
  -- rw [h] -- This fails because Lean doesn't find `f x` in the expression `h`.
  change f x + f x = 2
  rw [h]
end p₁

section p₂
example (f : ℕ → ℕ) (h : ∀ x, (fun (x : ℕ) => f x) x = 1) (x : ℕ) : f x + f x = 2 := by
  change ∀ x, f x = 1 at h
  rw [h]
end p₂

section p₃
#check Nat.sub_add_comm
example (n : ℕ) (x y : Fin n) : (x - y).val = (n + x.val - y.val) % n := by
  change _ % _ = _
  congr
  -- omega
  exact Eq.symm <| Nat.sub_add_comm <| le_of_lt y.isLt
end p₃

section p₄
example : let f : ℕ → ℕ := fun n => 2 * n; f (f 2) = 8 := by
  intro f
  show 2 * 2 * 2 = 8
  norm_num
end p₄

section p₅
example (a b c d : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hd : d > 0) (h₁ : a ≥ c) (h₂ : b ≥ d) : (a * b) ^ ((1 : ℝ) / 2) ≥ (c * d) ^ ((1 : ℝ) / 2) := by
  -- rw [Real.rpow_le_rpow_iff]  -- `rw` fails because Lean doesn't sythesize an expression like `_ ≤ _`.
  show _ ≤ _
  rw [Real.rpow_le_rpow_iff]   -- `rw` works!
  · refine mul_le_mul h₁ h₂ ?_ ?_
    · positivity
    · positivity
  · positivity
  · positivity
  · positivity
end p₅

section p₆
example (α : Type*) (p : α → Prop) [DecidablePred p] (a : α) (hnp : ¬p a) : (not ∘ fun x => decide (p x)) a = true := by
  -- simp   /- Simple but uncontrolled. -/
  -- change not _ = _   /- Not the one we want. -/
  change not (decide _) = _   /- More explicit format controls. -/
  rw [← Bool.not_false]
  congr 1
  rw [Bool.decide_false hnp]
end p₆

section p₇
example (a : ZMod 0) : ∃ (d : ℕ) (u : ZMod 0), a = u * d := by
  exists 1, a
  change _ = _ * 1
  rw [mul_one]
end p₇
