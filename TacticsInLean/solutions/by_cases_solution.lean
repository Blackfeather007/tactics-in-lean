import Mathlib.Tactic

#help tactic by_cases

example (P : Prop) : ¬¬P → P := by
  intro h
  by_cases h' : P
  · assumption
  · contradiction

example (a : ℝ) (h1 : 0 ≤ a) (h2 : a ≤ 1) : ⌈a⌉ = 0 ∨ ⌈a⌉ = 1 := by
  by_cases h : a = 0
  · left
    rw [h, Int.ceil_zero]
  · right
    apply Int.ceil_eq_iff.mpr
    constructor
    · simp only [Int.cast_one, sub_self]
      apply lt_of_le_of_ne h1
      push_neg at h
      apply h.symm
    · simp only [Int.cast_one]
      apply h2

example (x : ℝ) : ⌈x⌉ = ⌊x⌋ ∨ ⌈x⌉ = ⌊x⌋ + 1 := by
  by_cases h : ⌈x⌉ = ⌊x⌋
  · left
    exact h
  · right
    apply le_antisymm
    · apply Int.ceil_le_floor_add_one
    · apply Int.add_one_le_of_lt
      apply lt_of_le_of_ne
      exact Int.floor_le_ceil x
      exact fun a => h (id (Eq.symm a))

example (n : ℕ) : Even (n * (n + 1)) := by
  apply Nat.even_mul.2
  by_cases hn : Even n
  · left
    exact hn
  · right
    exact Nat.even_add_one.mpr hn

example (x a b c : ℤ) (_ : a ≤ b) (_ : b ≤ c) (hx : x ∈ Finset.Icc a c) : x ∈ Finset.Icc a b ∪ Finset.Icc (b + 1) c := by
  simp only [Finset.mem_union, Finset.mem_Icc] at *
  by_cases hx' : x ≤ b
  · left
    constructor
    · apply hx.1
    · apply hx'
  · right
    constructor
    · linarith [hx']
    · apply hx.2

def f : ℚ → ℚ := fun x => if x = 0 then 0
                            else |x| + 1

example {n : ℚ} : 0 ≤ f n := by
  by_cases h : n = 0
  · simp only [h, f, ↓reduceIte, le_refl]
  · simp only [h, f, ↓reduceIte]
    apply le_of_lt
    apply lt_of_le_of_lt (abs_nonneg n) (lt_add_one |n|)

example {α : Type*} (s t : Set α): s \ t ∪ t = s ∪ t := by
  ext x; constructor
  · rintro (⟨xs, _⟩ | xt)
    · left
      exact xs
    . right
      exact xt
  by_cases h : x ∈ t
  · intro
    right
    exact h
  rintro (xs | xt)
  · left
    use xs
  right; exact xt

example {α I : Type*} (A : I → Set α) (s : Set α) : (s ∪ ⋂ i, A i) = ⋂ i, A i ∪ s := by
  ext x
  simp only [Set.mem_union, Set.mem_iInter]
  constructor
  · rintro (xs | xI)
    · intro i
      right
      exact xs
    intro i
    left
    exact xI i
  intro h
  by_cases xs : x ∈ s
  · left
    exact xs
  right
  intro i
  cases h i
  · assumption
  contradiction

example (n : ℕ) (a b : Fin (n + 1)) (h : a - 1 < b) : a ≤ b := by
  by_cases hn : n = 0
  · subst hn
    rw [Fin.eq_zero a, Fin.eq_zero b]
  · rw [Fin.lt_def] at h
    by_cases ha : 1 ≤ a
    · rw [Fin.coe_sub_iff_le.mpr, Fin.val_one'', Nat.mod_eq_of_lt] at h
      rw [Fin.le_def]
      · omega
      · exact Nat.sub_ne_zero_iff_lt.mp hn
      · exact ha
    · push_neg at ha
      rw [Fin.lt_def, Fin.val_one'', Nat.mod_eq_of_lt] at ha
      · omega
      · omega
