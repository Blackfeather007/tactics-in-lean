import Mathlib.Tactic

#help tactic ext

def evens : Set ℕ :=
  { n | Even n }

def odds : Set ℕ :=
  { n | ¬Even n }

open Set in
example : evens ∪ odds = univ := by
  rw [evens, odds]
  ext n
  simp
  by_cases h : Even n
  · left
    exact h
  · right
    exact Nat.not_even_iff_odd.mp h

example {α : Type*} (s t : Set α) : s ∩ t = t ∩ s := by
  ext x
  simp only [Set.mem_inter_iff]
  constructor
  · intro ⟨xs, xt⟩; exact ⟨xt, xs⟩
  · intro ⟨xt, xs⟩; exact ⟨xs, xt⟩

example {α I : Type*} (A : I → Set α) (s : Set α) : (s ∩ ⋃ i, A i) = ⋃ i, A i ∩ s := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_iUnion]
  constructor
  · intro ⟨xs, ⟨i, xAi⟩⟩
    exact ⟨i, xAi, xs⟩
  intro ⟨i, xAi, xs⟩
  exact ⟨xs, ⟨i, xAi⟩⟩

example {α : Type*} (s t r : Set α) : s ∩ (t ∪ r) = (s ∩ t) ∪ (s ∩ r) := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_union]
  constructor
  · intro ⟨hx1, hx2⟩
    cases hx2 <;> rename _ => h
    · left
      constructor
      · exact hx1
      · exact h
    · right
      constructor
      · exact hx1
      · exact h
  · rintro (⟨hx1, hx2⟩ | ⟨hx1, hx2⟩)
    · constructor
      · exact hx1
      · left
        exact hx2
    · constructor
      · exact hx1
      · right
        exact hx2

def f₁ : ℝ → ℝ := fun x => (x - 1) * (x + 1)
def f₂ : ℝ → ℝ := fun x => x * x - 1

example : f₁ = f₂ := by
  ext x
  dsimp [f₁, f₂]
  ring

example {α β : Type*} (f : α → β) (s t : Set α) : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y; constructor
  · rintro ⟨x, xs | xt, rfl⟩
    · left
      use x, xs
    right
    use x, xt
  rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
  · use x, Or.inl xs
  use x, Or.inr xt

example {α β : Type*} (f : α → β) (s : Set α) (v : Set β) : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  ext y; constructor
  · rintro ⟨⟨x, xs, rfl⟩, fxv⟩
    use x, ⟨xs, fxv⟩
  rintro ⟨x, ⟨⟨xs, fxv⟩, rfl⟩⟩
  exact ⟨⟨x, xs, rfl⟩, fxv⟩

example (n : ℕ) (a : ℕ → ℕ) (ha : ∀ i ≤ n + 2, 0 < a i) :  ∑ i ∈ Finset.range (n + 1), ↑(a (n + 2)) / (a (n + 1) : ℚ) * ((a 0) * (a (n + 1)) / ((a i : ℚ) * (a (i + 1) : ℚ))) + (a 0) * (a (n + 2)) / ((a (n + 1) : ℚ) * (a (n + 2) : ℚ)) = ∑ x ∈ Finset.range (n + 1), (a 0) * (a (n + 2)) / ((a x : ℚ) * (a (x + 1) : ℚ)) + (a 0) * (a (n + 2)) / ((a (n + 1) : ℚ) * (a (n + 1 + 1) : ℚ)) := by
  congr ; ext i
  rw [div_mul_div_comm, ← mul_assoc, mul_comm, mul_div_mul_comm, div_self, one_mul, mul_comm]
  apply ne_of_gt
  apply Nat.cast_pos.2
  apply ha
  linarith

example {α ι : Type*} [SupSet α] {p : ι → Prop} {f g : (i : ι) → p i → α} (h : ∀ i (hi : p i), f i hi = g i hi) : ⨆ i, ⨆ (hi : p i), f i hi = ⨆ i, ⨆ (hi : p i), g i hi := by
  congr; ext i; congr; ext hi; exact h i hi

def f : ℕ → ℚ := fun x => (x * (x + 1) / ((x + 2) * (x + 3) : ℚ)) * ((x + 2) / (x + 1 : ℚ))
def g (y : ℕ) : ℕ → ℚ := fun x => x + y

example (n : ℕ) : ∑ i ∈ Finset.range n, (f i + ∑ j ∈ Finset.range i, g i j) = ∑ i ∈ Finset.range n, (i / (i + 3 : ℚ) + ∑ j ∈ Finset.range i, (i + j)) := by
  dsimp [f]
  calc
    _ = ∑ i ∈ Finset.range n, (i / (i + 3 : ℚ) + ∑ j ∈ Finset.range i, g i j) := by
      congr; ext i
      congr 1
      rw [div_mul_div_comm, mul_assoc, mul_comm (i + 2 : ℚ), mul_assoc, mul_div_mul_comm, mul_comm (i + 1 : ℚ), div_self, mul_one]
      apply ne_of_gt
      apply mul_pos
      · exact neg_lt_iff_pos_add.mp rfl
      · exact Nat.cast_add_one_pos i
    _ = _ := by
      congr; ext i
      simp only [g, Nat.cast_sum]
      congr; ext j
      simp only [Nat.cast_add, add_comm]
