import Mathlib.Tactic
import Mathlib.Data.Real.Irrational
section cases

open Nat

example (x : ℤ) (h : x = 2 ∨ x = 3) : x ∣ 6 := by
  sorry

example (x : ℤ) (h : ∃ r : ℤ, r * x ≠ 0) : x ≠ 0 := by
  sorry

example (x y : ℤ) (h1 : 2 ∣ x) (h2 : 2 ∣ y) : 2 ∣ x + y := by
  sorry

example (a b : ℝ) (f : (Set.Icc a b) → ℝ) (hf : StrictMono f) :
  ¬ (∃ x y : Set.Icc a b, x ≠ y ∧ f x = 0 ∧ f y = 0) := by
  sorry

end cases

section rcases

def mwe' := {s : String // s ∈ ({"A", "B", "C"} : Set String)}
def A : mwe' := ⟨"A", by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, String.reduceEq,
  or_false]⟩
def B : mwe' := ⟨"B", by simp only [Set.mem_insert_iff, String.reduceEq, Set.mem_singleton_iff,
  or_false, or_true]⟩
def C : mwe' := ⟨"C", by simp only [Set.mem_insert_iff, String.reduceEq, Set.mem_singleton_iff,
  or_true]⟩
example (x : mwe') : x = A ∨ x = B ∨ x = C := by
  sorry

lemma sq_mod_four {x : ℤ} :x ^ 2 % 4 = 0 ∨ x ^ 2 % 4 = 1 := by
  sorry

-- hard
theorem Int.neg_ediv_natCast (a : ℤ) (b : ℕ) : (-a) / b = - ((a + b - 1) / b) := by
  sorry
-- middle
theorem Int.neg_ediv (a b : ℤ) : (-a) / b = - ((a + b.natAbs - 1) / b) := by
  sorry

@[ext]
class PFilter {X: Type*} (A: Set X) extends Filter X where
  point : Set X
  point_eq : point = A
  point_in : A ∈ sets
lemma eq {X: Type*} (A: Set X): ∀ (F G: PFilter A), F.sets = G.sets → F = G := by
  sorry

open BigOperators Real Nat Topology Rat
#check nlinarith
#check sq_nonneg
example (a : ℝ) (h : 0 < a) (h_eq : a^3 = 6 * (a + 1)) : ¬ ∃ x : ℝ, x^2 + a * x + a^2 - 6 = 0 := by
  sorry

inductive X : Type
  | mkX : List Unit → X
abbrev X.nil : X := ⟨[]⟩
abbrev X.cons : Unit → X → X | x, ⟨xs⟩ => ⟨x :: xs⟩
inductive P : X → X → Prop
  | step (x' : X) : P x' x' → P (X.cons () x') (X.cons () x')
  | nil : P X.nil X.nil
theorem no_bug {x' y a : X} (h : P y a) (hy : y = X.cons () x' ): ∃ x'', a = X.cons () x'' := by
  sorry
theorem bug? {x' a} (h : P (X.cons () x') a) : ∃ x'', a = X.cons () x'' := by
  let y := X.cons () x'
  have hy : y = X.cons () x' := rfl
  rw [← hy] at h
  exact no_bug h hy
theorem Real_archimedean' (x y : ℝ) : (0 < x) → (0 < y) → ∃ (n : ℕ), y < n * x := by
  sorry
end rcases

section rintro

variable {α : Type*}
variable (s t u : Set α)
open Set

example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  sorry

example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  sorry

example : s ∩ t = t ∩ s := by
  sorry

example : s \ (t ∪ u) ⊆ (s \ t) \ u := by
  sorry

example : s \ t ∪ t = s ∪ t := by
  sorry

example : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
  sorry

end rintro

section obtain

example {α β γ ζ ε δ : Prop} (h : (α ∧ β) ∨ (γ ∧ δ) ∨ (ε ∧ ζ)) : α ∧ β ∨ γ ∧ δ ∨ ε ∧ ζ := by
  sorry

end obtain

section induction

-- normal
#check Multiset.induction
example (s : Multiset Bool) : let f : Bool → Bool := fun x => !x; (s.map f).map f = s := by
  sorry

-- normal
lemma List.sorted_of_sorted_append_left {α : Type*} (l₁ l₂ : List α) (r : α → α → Prop) (h : (l₁ ++ l₂).Sorted r) : l₁.Sorted r := by
  sorry

-- normal
lemma List.sorted_of_sorted_append_right {α : Type*} (l₁ l₂ : List α) (r : α → α → Prop) (h : (l₁ ++ l₂).Sorted r) : l₂.Sorted r := by
  sorry

-- hard
lemma List.sorted_append_iff {α : Type*} (l₁ l₂ : List α) (r : α → α → Prop) : (l₁ ++ l₂).Sorted r ↔ l₁.Sorted r ∧ l₂.Sorted r ∧ ∀ a ∈ l₁, ∀ b ∈ l₂, r a b := by
  sorry

def List.quickSort {α : Type*} (r : α → α → Prop) [DecidableRel r] (l : List α) :=
  match l with
  | [] => []
  | x :: t =>
      let ts := List.partition (fun m => r m x) t
      List.quickSort r ts.1 ++ [x] ++ List.quickSort r ts.2
termination_by l.length
decreasing_by
· simp only [List.partition_eq_filter_filter, List.length_cons, gt_iff_lt]
  suffices (List.filter (fun m ↦ r m x) t).length ≤ t.length by
    linarith
  exact List.length_filter_le (fun m ↦ r m x) t
· simp only [List.partition_eq_filter_filter, List.length_cons, gt_iff_lt]
  suffices (List.filter (not ∘ fun m ↦ r m x) t).length ≤ t.length by
    linarith
  exact List.length_filter_le (not ∘ fun m ↦ r m x) t
lemma List.sorted_append_singleton_append_iff {α : Type*} (l₁ l₂ : List α) (a : α) (r : α → α → Prop) : (l₁ ++ [a] ++ l₂).Sorted r ↔ l₁.Sorted r ∧ l₂.Sorted r ∧ (∀ x ∈ l₁, r x a) ∧ (∀ x ∈ l₂, r a x) ∧ (∀ x ∈ l₁, ∀ y ∈ l₂, r x y) := by
  constructor <;> intro h
  · simp only [List.sorted_append_iff] at h
    constructor
    · exact h.left.left
    constructor
    · exact h.right.left
    constructor
    · intro x mem
      exact h.left.right.right x mem a (List.mem_singleton_self _)
    constructor
    · intro x mem
      exact h.right.right a (by
        rw [List.mem_append]
        exact Or.inr <| List.mem_singleton_self _) x mem
    · intro x mem₁ y mem₂
      exact h.right.right x (by
        rw [List.mem_append]
        exact Or.inl mem₁) y mem₂
  · simp only [List.sorted_append_iff]
    constructor
    constructor
    · exact h.left
    constructor
    · exact List.sorted_singleton _
    · intro x mem₁ b mem₂
      rw [List.mem_singleton] at mem₂
      exact mem₂ ▸ h.right.right.left x mem₁
    constructor
    · exact h.right.left
    · intro x mem₁ b mem₂
      rw [List.mem_append] at mem₁
      cases mem₁ <;> rename _ => mem₁
      · exact h.right.right.right.right x mem₁ b mem₂
      · rw [List.mem_singleton] at mem₁
        exact mem₁ ▸ h.right.right.right.left b mem₂

-- very hard
lemma List.mem_quickSort_iff_mem {α : Type*} (r : α → α → Prop) [DecidableRel r] (l : List α) : ∀ x, x ∈ List.quickSort r l ↔ x ∈ l := by
  sorry

-- very hard
theorem List.sorted_quickSort {α : Type*} (r : α → α → Prop) [DecidableRel r] [IsTotal α r] [IsTrans α r] (l : List α) : List.Sorted (fun a b => r a b) (List.quickSort r l) := by
  sorry

-- very hard
example (a : ℝ) (h : ¬Irrational (Real.cos a)) (n : ℕ) : ¬Irrational (Real.cos (n * a)) := by
  sorry

-- very very hard
#check Nat.decreasing_induction_of_infinite
open BigOperators
example : ∀ (x : ℕ → ℝ), (∀ i, x i > 0) → ∀ (n : ℕ), (∑ i in Finset.range (n + 1), x i) / (n + 1 : ℝ) ≥ (∏ i in Finset.range (n + 1), x i) ^ ((1 : ℝ) / (n + 1)) := by
  sorry

end induction

section tactic_match

variable {x y : ℝ}

theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  sorry

theorem abs_add'' (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  sorry

end tactic_match
