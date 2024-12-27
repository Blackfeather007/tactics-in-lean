import Mathlib.Tactic
import Mathlib.Data.Real.Irrational

section p₁
example (n : ℕ) : 2 * ∑ i : ℕ in Finset.range (n + 1), i = n * (n + 1) := sorry
end p₁

section p₂
example (a b c : ℕ) (ha : a ≠ 0) (h : a * b = a * c) : b = c := by
  -- `induction' b with d hd`  /- Try not to use `generalizing c` and see why this doesn't work. -/
  induction' b with d hd generalizing c
  · admit
  · admit
end p₂

section p₃
example (n : ℕ) (f : Fin (n + 2) → Fin (n + 2)) (hf : ∀ i < Fin.last (n + 1), f (i + 1) = f i + 1) : Function.Injective f := sorry
end p₃

section p₄
/- Maybe we could come up with a better problem, so that it fits more `induction`. -/
example (s : Multiset Bool) : let f : Bool → Bool := fun x => !x; (s.map f).map f = s := sorry
end p₄

section p₅
lemma List.sorted_of_sorted_append_left {α : Type*} (l₁ l₂ : List α) (r : α → α → Prop) (h : (l₁ ++ l₂).Sorted r) : l₁.Sorted r := sorry
end p₅

section p₆
lemma List.sorted_of_sorted_append_right {α : Type*} (l₁ l₂ : List α) (r : α → α → Prop) (h : (l₁ ++ l₂).Sorted r) : l₂.Sorted r := sorry
end p₆

section p₇
lemma List.sorted_append_iff {α : Type*} (l₁ l₂ : List α) (r : α → α → Prop) : (l₁ ++ l₂).Sorted r ↔ l₁.Sorted r ∧ l₂.Sorted r ∧ ∀ a ∈ l₁, ∀ b ∈ l₂, r a b := sorry
end p₇

section p₈
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

lemma List.mem_quickSort_iff_mem {α : Type*} (r : α → α → Prop) [DecidableRel r] (l : List α) : ∀ x, x ∈ List.quickSort r l ↔ x ∈ l := by
  generalize h : l.length = n
  induction n using Nat.strongRecOn generalizing l with
  | ind n hn =>
    match l with
    | [] =>
      rw [List.quickSort]
      exact fun x => Eq.to_iff rfl
    | .cons a l =>
      rw [List.length] at h
      rw [List.quickSort]
      intro x; constructor <;> intro mem
      · simp only [List.mem_append, List.mem_append, List.partition_eq_filter_filter] at mem
        cases mem <;> rename _ => mem
        cases mem <;> rename _ => mem
        · rw [List.mem_cons]
          refine Or.inr <| List.mem_of_mem_filter (p := fun m => r m a) ?_
          refine (hn _ ?_ _ rfl _).mp mem
          rw [← h, Nat.lt_add_one_iff]
          exact List.length_filter_le _ _
        · rw [List.mem_singleton] at mem
          rw [List.mem_cons]
          exact Or.inl mem
        · rw [List.mem_cons]
          refine Or.inr <| List.mem_of_mem_filter (p := not ∘ fun m => r m a) ?_
          refine (hn _ ?_ _ rfl _).mp mem
          rw [← h, Nat.lt_add_one_iff]
          exact List.length_filter_le _ _
      · rw [List.mem_cons] at mem
        cases mem <;> rename _ => mem
        · rw [← List.mem_singleton] at mem
          simp only [List.mem_append]
          exact Or.inl <| Or.inr mem
        · simp only [List.partition_eq_filter_filter, List.mem_append]
          by_cases hx : r x a
          · replace mem := (List.mem_filter (p := fun m => r m a)).mpr ⟨mem, by
            rw [decide_eq_true hx]⟩; clear hx
            refine Or.inl <| Or.inl ?_
            refine (hn _ ?_ _ rfl _).mpr mem
            rw [← h, Nat.lt_add_one_iff]
            exact List.length_filter_le _ _
          · replace mem := (List.mem_filter (p := not ∘ fun m => r m a)).mpr ⟨mem, by
            show not (decide _) = _
            rw [decide_eq_false hx]; exact rfl⟩; clear hx
            refine Or.inr ?_
            refine (hn _ ?_ _ rfl _).mpr mem
            rw [← h, Nat.lt_add_one_iff]
            exact List.length_filter_le _ _

theorem List.sorted_quickSort {α : Type*} (r : α → α → Prop) [DecidableRel r] [IsTotal α r] [IsTrans α r] (l : List α) : List.Sorted (fun a b => r a b) (List.quickSort r l) := sorry
end p₈

section p₉
example (a : ℝ) (h : ¬Irrational (Real.cos a)) (n : ℕ) : ¬Irrational (Real.cos (n * a)) := sorry
end p₉

section p₁₀
#check Nat.decreasing_induction_of_infinite
open BigOperators
/-- Known as "AM-GM inequality". -/
example : ∀ (x : ℕ → ℝ), (∀ i, x i > 0) → ∀ (n : ℕ), (∑ i in Finset.range (n + 1), x i) / (n + 1 : ℝ) ≥ (∏ i in Finset.range (n + 1), x i) ^ ((1 : ℝ) / (n + 1)) := sorry
end p₁₀
