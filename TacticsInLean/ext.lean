import Mathlib.Tactic

#help tactic ext

def evens : Set ℕ :=
  { n | Even n }

def odds : Set ℕ :=
  { n | ¬Even n }

open Set in
example : evens ∪ odds = univ := by sorry

example {α : Type*} (s t : Set α) : s ∩ t = t ∩ s := by sorry

example {α I : Type*} (A : I → Set α) (s : Set α) : (s ∩ ⋃ i, A i) = ⋃ i, A i ∩ s := by sorry

example {α : Type*} (s t r : Set α) : s ∩ (t ∪ r) = (s ∩ t) ∪ (s ∩ r) := by sorry

def f₁ : ℝ → ℝ := fun x => (x - 1) * (x + 1)
def f₂ : ℝ → ℝ := fun x => x * x - 1

example : f₁ = f₂ := by sorry

example {α β : Type*} (f : α → β) (s t : Set α) : f '' (s ∪ t) = f '' s ∪ f '' t := by sorry

example {α β : Type*} (f : α → β) (s : Set α) (v : Set β) : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by sorry

example (n : ℕ) (a : ℕ → ℕ) (ha : ∀ i ≤ n + 2, 0 < a i) :  ∑ i ∈ Finset.range (n + 1), ↑(a (n + 2)) / (a (n + 1) : ℚ) * ((a 0) * (a (n + 1)) / ((a i : ℚ) * (a (i + 1) : ℚ))) + (a 0) * (a (n + 2)) / ((a (n + 1) : ℚ) * (a (n + 2) : ℚ)) = ∑ x ∈ Finset.range (n + 1), (a 0) * (a (n + 2)) / ((a x : ℚ) * (a (x + 1) : ℚ)) + (a 0) * (a (n + 2)) / ((a (n + 1) : ℚ) * (a (n + 1 + 1) : ℚ)) := by sorry

example {α : Type*} [SupSet α] {p : ι → Prop} {f g : (i : ι) → p i → α} (h : ∀ i (hi : p i), f i hi = g i hi) : ⨆ i, ⨆ (hi : p i), f i hi = ⨆ i, ⨆ (hi : p i), g i hi := by sorry

def f : ℕ → ℚ := fun x => (x * (x + 1) / ((x + 2) * (x + 3) : ℚ)) * ((x + 2) / (x + 1 : ℚ))
def g (y : ℕ) : ℕ → ℚ := fun x => x + y

example (n : ℕ) : ∑ i ∈ Finset.range n, (f i + ∑ j ∈ Finset.range i, g i j) = ∑ i ∈ Finset.range n, (i / (i + 3 : ℚ) + ∑ j ∈ Finset.range i, (i + j)) := by sorry
