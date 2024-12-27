import Mathlib.Tactic

#help tactic by_cases

example (P : Prop) : ¬¬P → P := by sorry

example (a : ℝ) (h1 : 0 ≤ a) (h2 : a ≤ 1) : ⌈a⌉ = 0 ∨ ⌈a⌉ = 1 := by sorry

example (x : ℝ) : ⌈x⌉ = ⌊x⌋ ∨ ⌈x⌉ = ⌊x⌋ + 1 := by sorry

example (n : ℕ) : Even (n * (n + 1)) := by sorry

example (x a b c : ℤ) (_ : a ≤ b) (_ : b ≤ c) (hx : x ∈ Finset.Icc a c) : x ∈ Finset.Icc a b ∪ Finset.Icc (b + 1) c := by sorry

def f : ℚ → ℚ := fun x => if x = 0 then 0
                            else |x| + 1

example {n : ℚ} : 0 ≤ f n := by sorry

example {α : Type*} (s t : Set α): s \ t ∪ t = s ∪ t := by sorry

example {α I : Type*} (A : I → Set α) (s : Set α) : (s ∪ ⋂ i, A i) = ⋂ i, A i ∪ s := by sorry

example (n : ℕ) (a b : Fin (n + 1)) (h : a - 1 < b) : a ≤ b := by sorry
