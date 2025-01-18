import Mathlib.Tactic
import Mathlib.Data.Real.Irrational
section cases

open Nat

example (n : Nat) (h : n ≠ 0) : succ (pred n) = n := by
  cases n with
  | zero =>
    apply absurd rfl h
  | succ m =>
    rfl

example (x : ℤ) (h : x > 0 ∨ x < 0) : x ≠ 0 := by
  cases' h with hp hq
  · exact Ne.symm (Int.ne_of_lt hp)
  · exact Ne.symm (Int.ne_of_gt hq)

example (x : ℤ) (h : x = 2 ∨ x = 3) : x ∣ 6 := by
  cases' h with h1 h2
  · rw [h1]
    use 3
    rfl
  · rw [h2]
    use 2
    rfl

example (x : ℤ) (h : ∃ r : ℤ, r * x ≠ 0) : x ≠ 0 := by
  cases' h with r hr
  by_contra h1
  rw [h1, mul_zero] at hr
  exact hr rfl

example (x y : ℤ) (h1 : 2 ∣ x) (h2 : 2 ∣ y) : 2 ∣ x + y := by
  cases' h1 with x' hx
  cases' h2 with y' hy
  use x' + y'
  rw [hx, hy, mul_add]

example (a b : ℝ) (f : (Set.Icc a b) → ℝ) (hf : StrictMono f) :
  ¬ (∃ x y : Set.Icc a b, x ≠ y ∧ f x = 0 ∧ f y = 0) := by
  push_neg
  intro x y hxy hfxzero hfyzero
  replace hxy := lt_or_gt_of_ne (Subtype.coe_injective.ne hxy)
  cases hxy with
  | inl hlt => linarith [hf hlt, hfxzero, hfyzero]
  | inr hgt => linarith [hf hgt, hfxzero, hfyzero]

end cases

section rcases

example {x : ℝ} (h : x = 1 ∨ x = 2) : x ^ 2 - 3 * x + 2 = 0 := by
  rcases h with rfl | rfl <;> norm_num

example {x y : ℝ} (h : x = 2 ∨ y = -2) : x * y + 2 * x = 2 * y + 4 := by
  rcases h with rfl | rfl <;> ring

def f (_ : List Empty) (b : Bool) := b
@[simp]
theorem lem2 (a b : Bool) (x y : List Empty)
  (h : f x a = f y b) : x = y := by
    rcases x with _ | ⟨⟨⟩, _⟩
    rcases y with _ | ⟨⟨⟩, _⟩
    rfl

open ZMod
theorem mul_inv_of_unit' {n : ℕ} {a : ZMod n} (h : IsUnit a) : a * a⁻¹ = 1 := by
  rcases h with ⟨u, rfl⟩
  rw [inv_coe_unit, u.mul_inv]

class inductive Something where
 | oneThing : Something
 | anotherThing : Something
instance instOne : Something := Something.oneThing
@[instance]
def instAnother : Something := Something.anotherThing
example [s : Something] : s = Something.oneThing ∨ s = Something.anotherThing := by
  rcases s with h | h
  . simp
  . simp

def mwe' := {s : String // s ∈ ({"A", "B", "C"} : Set String)}
def A : mwe' := ⟨"A", by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, String.reduceEq,
  or_false]⟩
def B : mwe' := ⟨"B", by simp only [Set.mem_insert_iff, String.reduceEq, Set.mem_singleton_iff,
  or_false, or_true]⟩
def C : mwe' := ⟨"C", by simp only [Set.mem_insert_iff, String.reduceEq, Set.mem_singleton_iff,
  or_true]⟩
example (x : mwe') : x = A ∨ x = B ∨ x = C := by
  obtain ⟨h, property⟩ := x
  rw [A, B, C]
  rcases property
  left
  simp_all
  rename_i property
  rcases property
  right
  left
  simp_all
  rename_i property
  right
  right
  simp only [Set.mem_singleton_iff] at property
  simp_all

lemma sq_mod_four {x : ℤ} :x ^ 2 % 4 = 0 ∨ x ^ 2 % 4 = 1 := by
  have hx := Int.even_or_odd x
  rcases hx with hx | hx
  · unfold Even at hx
    rcases hx with ⟨r, hr⟩
    left
    rw [hr, sq]
    simp only [EuclideanDomain.mod_eq_zero]
    ring_nf
    rw [Int.mul_comm]
    simp only [dvd_mul_right]
  · unfold Odd at hx
    rcases hx with ⟨_, rfl⟩
    ring_nf
    rw [add_assoc, ← add_mul, Int.add_mul_emod_self]
    decide

-- hard
theorem Int.neg_ediv_natCast (a : ℤ) (b : ℕ) : (-a) / b = - ((a + b - 1) / b) := by
  rcases eq_or_ne b 0 with rfl | hb
  · simp
  have hb' : 0 < (b : ℚ) := by norm_cast; omega
  rw [← Rat.floor_intCast_div_natCast, ← Rat.floor_intCast_div_natCast]
  simp only [cast_neg, neg_div, floor_neg, cast_sub, cast_add, cast_natCast, cast_one, neg_inj]
  rw [← Int.emod_add_ediv a b]
  simp only [cast_add, cast_mul, cast_natCast, add_div, ne_eq, Nat.cast_eq_zero, hb,
    not_false_eq_true, mul_div_cancel_left₀, ceil_add_int, sub_div, div_self]
  simp only [add_comm, add_assoc, add_sub_assoc, floor_int_add, add_right_inj]
  rw [← add_sub_assoc, add_comm, add_sub_assoc, ← sub_div]
  rcases eq_or_ne (a % b) 0 with hab | hab
  · simp only [hab, cast_zero, zero_div, ceil_zero, zero_sub]
    rw [eq_comm, Int.floor_eq_zero_iff, neg_div, one_div, Set.mem_Ico, le_add_neg_iff_add_le, zero_add, add_lt_iff_neg_left,
      Left.neg_neg_iff, inv_pos, Nat.cast_pos]
    constructor
    · exact Nat.cast_inv_le_one b
    · omega
  · have : 0 < a % b := (Int.emod_nonneg a (mod_cast hb : (b : ℤ) ≠ 0)).lt_of_ne hab.symm
    have : a % b < b := Int.emod_lt_of_pos a (by omega)
    rw [add_comm, Int.floor_add_one, add_comm, (Int.ceil_eq_iff (z := 1)).mpr, Int.floor_eq_zero_iff.mpr]
    · simp
    · simp only [Set.mem_Ico, le_div_iff₀ hb', zero_mul, sub_nonneg, div_lt_iff₀ hb', one_mul]
      norm_cast
      omega
    · simp [lt_div_iff₀ hb', div_le_iff₀ hb']
      norm_cast
      omega
-- middle
theorem Int.neg_ediv (a b : ℤ) : (-a) / b = - ((a + b.natAbs - 1) / b) := by
  rcases b.natAbs_eq with hb | hb
  · rw [hb]
    apply Int.neg_ediv_natCast
  · rw [hb]
    simp only [Int.ediv_neg, natAbs_neg, abs_abs, neg_neg, Int.neg_ediv_natCast]
    simp only [natCast_natAbs, abs_abs]

@[ext]
class PFilter {X: Type*} (A: Set X) extends Filter X where
  point : Set X
  point_eq : point = A
  point_in : A ∈ sets
lemma eq {X: Type*} (A: Set X): ∀ (F G: PFilter A), F.sets = G.sets → F = G := by
  intros F G h
  rcases F with ⟨⟨A, B, C, D⟩, b, c, d⟩
  rcases G with ⟨⟨A', B', C', D'⟩, b', c', d'⟩
  dsimp at h
  subst c c' h
  rfl

open BigOperators Real Nat Topology Rat
example (a : ℝ) (h : 0 < a) (h_eq : a^3 = 6 * (a + 1)) : ¬ ∃ x : ℝ, x^2 + a * x + a^2 - 6 = 0 := by
  intro h_contra
  rcases h_contra with ⟨x, hx⟩
  nlinarith [sq_nonneg (x + a / 2)]

inductive X : Type
  | mkX : List Unit → X
abbrev X.nil : X := ⟨[]⟩
abbrev X.cons : Unit → X → X | x, ⟨xs⟩ => ⟨x :: xs⟩
inductive P : X → X → Prop
  | step (x' : X) : P x' x' → P (X.cons () x') (X.cons () x')
  | nil : P X.nil X.nil
theorem no_bug {x' y a : X} (h : P y a) (hy : y = X.cons () x' ): ∃ x'', a = X.cons () x'' := by
  rcases h with ⟨x, h'⟩ | _
  · exact ⟨x, rfl⟩
  · refine ⟨x', hy⟩
theorem bug? {x' a} (h : P (X.cons () x') a) : ∃ x'', a = X.cons () x'' := by
  let y := X.cons () x'
  have hy : y = X.cons () x' := rfl
  rw [← hy] at h
  exact no_bug h hy
theorem Real_archimedean' (x y : ℝ) : (0 < x) → (0 < y) → ∃ (n : ℕ), y < n * x := by
  intro x_pos y_pos
  have : ∃ (n : ℕ), y ≤ n • x := by
    apply Archimedean.arch y x_pos
  rcases this with ⟨n, n_eq⟩
  have : n • x = ↑n * x := by
    exact nsmul_eq_mul n x
  use (n + 1)
  rw [this] at n_eq
  apply lt_of_le_of_lt n_eq
  apply mul_lt_mul
  · norm_cast
    linarith
  · rfl
  · exact x_pos
  · norm_cast
    linarith
end rcases

section rintro

variable {α : Type*}
variable (s t u : Set α)
open Set
example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  rw [subset_def, inter_def, inter_def]
  rw [subset_def] at h
  simp only [mem_setOf]
  rintro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩

example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  rintro x ⟨xs, xt | xu⟩
  · left
    exact ⟨xs, xt⟩
  · right
    exact ⟨xs, xu⟩

example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  rintro x ⟨⟨xs, xnt⟩, xnu⟩
  use xs
  rintro (xt | xu) <;> contradiction

example : s ∩ t = t ∩ s := by
  ext x
  simp only [mem_inter_iff]
  constructor
  · rintro ⟨xs, xt⟩; exact ⟨xt, xs⟩
  · rintro ⟨xt, xs⟩; exact ⟨xs, xt⟩

example : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  rintro x (⟨xs, xt⟩ | ⟨xs, xu⟩)
  · use xs; left; exact xt
  · use xs; right; exact xu

example : s \ (t ∪ u) ⊆ (s \ t) \ u := by
  rintro x ⟨xs, xntu⟩
  constructor
  use xs
  · intro xt
    exact xntu (Or.inl xt)
  intro xu
  apply xntu (Or.inr xu)

example : s ∩ (s ∪ t) = s := by
  ext x; constructor
  · rintro ⟨xs, _⟩
    exact xs
  · intro xs
    use xs; left; exact xs

example : s ∪ s ∩ t = s := by
  ext x; constructor
  · rintro (xs | ⟨xs, xt⟩) <;> exact xs
  · intro xs; left; exact xs

example : s \ t ∪ t = s ∪ t := by
  ext x; constructor
  · rintro (⟨xs, nxt⟩ | xt)
    · left
      exact xs
    · right
      exact xt
  by_cases h : x ∈ t
  · intro
    right
    exact h
  rintro (xs | xt)
  · left
    use xs
  right; exact xt

example : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
  ext x; constructor
  · rintro (⟨xs, xnt⟩ | ⟨xt, xns⟩)
    · constructor
      left
      exact xs
      rintro ⟨_, xt⟩
      contradiction
    · constructor
      right
      exact xt
      rintro ⟨xs, _⟩
      contradiction
  rintro ⟨xs | xt, nxst⟩
  · left
    use xs
    intro xt
    apply nxst
    constructor <;> assumption
  · right; use xt; intro xs
    apply nxst
    constructor <;> assumption

end rintro

section obtain

example (h : ∃ x, x > 0) : ∃ y, y > 0 := by
  obtain ⟨y, hy⟩ := h
  exact ⟨y, hy⟩

example {α β : Prop} (h : α ∨ β) : α ∨ β := by
  obtain (h' | h') := h
  left
  exact h'
  right
  exact h'

example {α β : Prop} (h : α → β) : α → β := by
  intro a
  obtain h₀ := h a
  exact h₀

example {x y : ℝ} (h : ∀ x, ∃ y, x + y = 0) : ∀ x, ∃ y, x + y = 0 := by
  intro x
  obtain ⟨y, h'⟩ := h x
  exact ⟨y, h'⟩

example (h : ∃ x, ∃ y, x + y = 3) : ∃ x, ∃ y, x + y = 3 := by
  obtain ⟨x, ⟨y, hxy⟩⟩ := h
  exact ⟨x, ⟨y, hxy⟩⟩

example {α β γ ζ ε δ : Prop} (h : (α ∧ β) ∨ (γ ∧ δ) ∨ (ε ∧ ζ)) : α ∧ β ∨ γ ∧ δ ∨ ε ∧ ζ := by
  obtain (h₁ | h₂) := h  -- 分解 h : (α ∧ β) ∨ (γ ∧ δ) ∨ (ε ∧ ζ)
  { -- 如果 h₁ : α ∧ β
    obtain ⟨a, b⟩ := h₁  -- 从 α ∧ β 中提取 a 和 b
    exact Or.inl ⟨a, b⟩  -- 证明 α ∧ β 成立，构造 Or.inl
  }
  { -- 如果 h₂ : (γ ∧ δ) ∨ (ε ∧ ζ)
    obtain (h₂₁ | h₂₂) := h₂  -- 分解 h₂： (γ ∧ δ) ∨ (ε ∧ ζ)
    { -- 如果 h₂₁ : γ ∧ δ
      obtain ⟨c, d⟩ := h₂₁ -- 从 γ ∧ δ 中提取 c 和 d
      exact Or.inr (Or.inl ⟨c, d⟩)  -- 证明 γ ∧ δ 成立，构造 Or.inr (Or.inl)
    }
    { -- 如果 h₂₂ : ε ∧ ζ
      obtain ⟨e, f⟩ := h₂₂  -- 从 ε ∧ ζ 中提取 e 和 f
      exact Or.inr (Or.inr ⟨e, f⟩)  -- 证明 ε ∧ ζ 成立，构造 Or.inr (Or.inr)
    }
  }

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a
def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a
theorem fnUb_add {f g : ℝ → ℝ} {a b : ℝ} (hfa : FnUb f a) (hgb : FnUb g b) :
    FnUb (fun x ↦ f x + g x) (a + b) :=
  fun x ↦ add_le_add (hfa x) (hgb x)
example {f g : ℝ → ℝ} (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  obtain ⟨a, ubfa⟩ := ubf
  obtain ⟨b, ubgb⟩ := ubg
  exact ⟨a + b, fnUb_add ubfa ubgb⟩

end obtain

section induction

example (n : ℕ) : 2 * ∑ i : ℕ in Finset.range (n + 1), i = n * (n + 1) := by
  induction n with
  | zero =>
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, mul_zero, mul_one]
  | succ k hk =>
    rw [Finset.range_succ, Finset.sum_insert]
    · rw [mul_add, hk]
      ring
    · rw [Finset.mem_range]
      omega

example (a b c : ℕ) (ha : a ≠ 0) (h : a * b = a * c) : b = c := by
  induction' b with d hd generalizing c
  · rw [mul_zero] at h
    have := mul_eq_zero.mp h.symm
    tauto
  · cases' c with e
    · rw [mul_zero] at h
      have := mul_eq_zero.mp h
      tauto
    · repeat rw [mul_add] at h
      rw [mul_one] at h
      let g := add_right_cancel h
      let h' := hd e g
      rw [h']

example (n : ℕ) (f : Fin (n + 2) → Fin (n + 2)) (hf : ∀ i < Fin.last (n + 1), f (i + 1) = f i + 1) : Function.Injective f := by
  have aux (x : Fin (n + 2)) : f x = f 0 + x := by
    induction x using Fin.inductionOn with
    | zero =>
      rw [add_zero]
    | succ x hx =>
      rw [← Fin.coeSucc_eq_succ, hf _, hx, add_assoc]
      exact Fin.castSucc_lt_last x
  intro x y eq
  rw [aux x, aux y, add_left_cancel_iff] at eq
  exact eq

example (s : Multiset Bool) : let f : Bool → Bool := fun x => !x; (s.map f).map f = s := by
  intro f
  -- rw [Multiset.map_map]
  -- convert Multiset.map_id s
  -- ext x
  -- rw [Function.comp]
  -- show (!!x) = x
  -- rw [Bool.not_not]
  induction s using Multiset.induction with
  | empty =>
    simp only [Multiset.map_zero]
  | cons a s hs =>
    simp only [Multiset.map_cons, hs]
    congr 1
    show (!!a) = a
    rw [Bool.not_not]

lemma List.sorted_of_sorted_append_left {α : Type*} (l₁ l₂ : List α) (r : α → α → Prop) (h : (l₁ ++ l₂).Sorted r) : l₁.Sorted r := by
  induction l₁ with
  | nil =>
    exact List.sorted_nil
  | cons a l hl =>
    simp only [List.cons_append, List.sorted_cons] at h ⊢
    constructor
    · intro b mem
      refine h.left b ?_
      rw [List.mem_append]
      exact Or.inl mem
    · exact hl h.right

lemma List.sorted_of_sorted_append_right {α : Type*} (l₁ l₂ : List α) (r : α → α → Prop) (h : (l₁ ++ l₂).Sorted r) : l₂.Sorted r := by
  induction l₁ with
  | nil =>
    rw [List.nil_append] at h
    exact h
  | cons a l hl =>
    simp only [List.cons_append, List.sorted_cons] at h
    exact hl h.right

lemma List.sorted_append_iff {α : Type*} (l₁ l₂ : List α) (r : α → α → Prop) : (l₁ ++ l₂).Sorted r ↔ l₁.Sorted r ∧ l₂.Sorted r ∧ ∀ a ∈ l₁, ∀ b ∈ l₂, r a b := by
  constructor <;> intro h
  · constructor
    · exact List.sorted_of_sorted_append_left l₁ l₂ r h
    constructor
    · exact List.sorted_of_sorted_append_right l₁ l₂ r h
    · induction l₁ with
      | nil =>
        simp_rw [List.mem_nil_iff]
        exact fun _ h => False.elim h
      | cons a l hl =>
        intro x mem₁ b mem₂
        rw [List.cons_append, List.sorted_cons] at h
        rw [List.mem_cons] at mem₁
        cases mem₁ <;> rename _ => mem₁
        · exact mem₁ ▸ h.left b (by
            rw [List.mem_append]
            exact Or.inr mem₂)
        · exact hl h.right x mem₁ b mem₂
  · induction l₁ with
    | nil =>
      rw [List.nil_append]
      exact h.right.left
    | cons a l hl =>
      rw [List.cons_append, List.sorted_cons]
      constructor
      · intro b mem
        rw [List.mem_append] at mem
        cases mem <;> rename _ => mem
        · rw [List.sorted_cons] at h
          exact h.left.left b mem
        · exact h.right.right a (List.mem_cons_self _ _) b mem
      · refine hl ?_
        constructor
        · rw [List.sorted_cons] at h
          exact h.left.right
        constructor
        · exact h.right.left
        · intro x mem₁ b mem₂
          exact h.right.right x (by
            rw [List.mem_cons]
            exact Or.inr mem₁) b mem₂

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



theorem List.sorted_quickSort {α : Type*} (r : α → α → Prop) [DecidableRel r] [IsTotal α r] [IsTrans α r] (l : List α) : List.Sorted (fun a b => r a b) (List.quickSort r l) := by
  generalize h : l.length = n
  induction n using Nat.strongRecOn generalizing l with
  | ind n hn =>
    match l with
    | [] =>
      rw [List.quickSort]
      exact List.sorted_nil
    | .cons a l =>
      rw [List.length] at h
      simp only [List.quickSort, List.partition_eq_filter_filter, List.sorted_append_singleton_append_iff]
      constructor
      · refine hn (List.filter (fun m => r m a) l).length ?_ (List.filter (fun m => r m a) l) rfl
        rw [← h, Nat.lt_add_one_iff]
        exact List.length_filter_le _ _
      constructor
      · refine hn (List.filter (not ∘ fun m => r m a) l).length ?_ (List.filter (not ∘ fun m => r m a) l) rfl
        rw [← h, Nat.lt_add_one_iff]
        exact List.length_filter_le _ _
      constructor
      · intro x mem
        rw [List.mem_quickSort_iff_mem, List.mem_filter, decide_eq_true_eq] at mem
        exact mem.right
      constructor
      · intro x mem
        rw [List.mem_quickSort_iff_mem, List.mem_filter] at mem
        replace mem := mem.right
        change not (decide _) = _ at mem
        apply_fun fun m => not m at mem
        rw [Bool.not_not, Bool.not_true, decide_eq_false_iff_not] at mem
        exact Or.resolve_right (IsTotal.total a x) mem
      · intro x mem₁ y mem₂
        rw [List.mem_quickSort_iff_mem, List.mem_filter] at mem₁ mem₂
        replace mem₁ := mem₁.right
        replace mem₂ := mem₂.right
        change not (decide _) = _ at mem₂
        apply_fun fun m => not m at mem₂
        rw [decide_eq_true_eq] at mem₁
        rw [Bool.not_not, Bool.not_true, decide_eq_false_iff_not] at mem₂
        replace mem₂ := Or.resolve_right (IsTotal.total a y) mem₂
        exact IsTrans.trans _ _ _ mem₁ mem₂

example (a : ℝ) (h : ¬Irrational (Real.cos a)) (n : ℕ) : ¬Irrational (Real.cos (n * a)) := by
  induction n using Nat.strongRecOn with
  | ind n hn =>
    rcases Nat.even_or_odd' n with ⟨k, eq⟩
    cases eq with
    | inl h₁ =>
      rw [h₁]
      push_cast
      rw [mul_assoc, Real.cos_two_mul]
      intro h₂
      rw [show (1 : ℝ) = (1 : ℚ) by norm_cast,irrational_sub_rat_iff,
        show (2 : ℝ) = (2 : ℚ) by norm_cast, irrational_rat_mul_iff] at h₂
      replace h₂ := Irrational.of_pow _ h₂.right
      if h₃ : k = 0 then
        rw [h₃] at h₂
        push_cast at h₂
        rw [zero_mul, Real.cos_zero] at h₂
        exact not_irrational_one h₂
      else
        exact hn _ (by omega) h₂
    | inr h₁ =>
      rw [h₁]
      push_cast
      rw [add_mul, one_mul, Real.cos_add, mul_assoc, Real.sin_two_mul, mul_assoc 2, mul_comm (Real.sin _)]
      intro h₂
      apply Irrational.add_cases at h₂
      cases h₂ with
      | inl h₂ =>
        apply Irrational.mul_cases at h₂
        refine Or.elim h₂ ?_ ?_
        · rw [← mul_assoc, show (2 : ℝ) * (k : ℕ) = (2 * k : ℕ) by norm_cast]
          exact hn _ (by omega)
        · exact h
      | inr h₂ =>
        rw [irrational_neg_iff, ← mul_assoc, mul_assoc (2 * _)] at h₂
        apply Irrational.mul_cases at h₂
        refine Or.elim h₂ ?_ ?_ <;> clear h₂ <;> intro h₂
        · rw [show (2 : ℝ) = (2 : ℚ) by norm_cast, irrational_rat_mul_iff] at h₂
          exact hn _ (by omega) <| h₂.right
        · have h₃ : Real.sin (↑k * a) * Real.sin a = Real.cos (↑k * a) * Real.cos a - Real.cos (↑k * a + a) := by
            rw [Real.cos_add (k * a) a]
            ring
          rw [h₃] at h₂; clear h₃
          apply Irrational.add_cases at h₂
          refine Or.elim h₂ ?_ ?_ <;> clear h₂ <;> intro h₂
          · apply Irrational.mul_cases at h₂
            exact Or.elim h₂ (hn _ (by omega)) h
          · rw [irrational_neg_iff] at h₂
            if h₃ : k = 0 then
              rw [h₃] at h₂
              push_cast at h₂
              rw [zero_mul, zero_add] at h₂
              exact h h₂
            else
              nth_rw 2 [← one_mul a] at h₂
              rw [← add_mul, show (k : ℕ) + (1 : ℝ) = (k + 1 : ℕ) by norm_cast] at h₂
              exact hn _ (by omega) <| h₂

#check Nat.decreasing_induction_of_infinite
open BigOperators
example : ∀ (x : ℕ → ℝ), (∀ i, x i > 0) → ∀ (n : ℕ), (∑ i in Finset.range (n + 1), x i) / (n + 1 : ℝ) ≥ (∏ i in Finset.range (n + 1), x i) ^ ((1 : ℝ) / (n + 1)) := by
  intro x pos n
  induction n using Nat.decreasing_induction_of_infinite generalizing x pos with
  | h n hp' =>
    push_cast at hp'
    have aux₁ : ∏ i ∈ Finset.range (n + 1), x i > 0 := by
      refine Finset.prod_pos ?_
      exact fun _ _ => pos _
    let R := (∏ i in Finset.range (n + 1), x i) ^ ((1 : ℝ) / (n + 1))
    let x' := fun i => if i < n + 1 then x i else R
    have aux₂ : ∀ i, x' i > 0 := fun i => by
      unfold x'
      split
      · exact pos _
      · positivity
    replace hp' := hp' x' aux₂
    nth_rw 2 [Finset.range_succ] at hp'
    rw [Finset.prod_insert Finset.not_mem_range_self,
      show (∏ i in Finset.range (n + 1), x' i) = R ^ (n + 1 : ℝ) by
        unfold R
        rw [← Real.rpow_mul (le_of_lt aux₁)]
        field_simp
        refine Finset.prod_congr rfl ?_
        exact fun _ mem => by
          unfold x'
          rw [Finset.mem_range] at mem
          rw [if_pos mem]] at hp'
    have aux₃ : x' (n + 1) = R := by
      unfold x'
      rw [if_neg (by omega)]
    rw [aux₃, mul_comm R,← Real.rpow_add_one (ne_of_lt (by positivity)).symm] at hp'
    rw [← Real.rpow_mul, Finset.range_succ, Finset.sum_insert, aux₃] at hp'
    field_simp at hp'
    apply mul_le_of_le_div₀ (by
      refine Left.add_nonneg (by positivity) ?_
      refine Finset.sum_nonneg ?_
      exact fun _ mem =>
        le_of_lt (aux₂ _)) (by positivity) at hp'
    · apply tsub_le_iff_left.mpr at hp'
      nth_rw 2 [← mul_one R] at hp'
      rw [← mul_sub, add_sub_cancel_right] at hp'
      calc
        _ ≥ R * (n + 1 : ℝ) / (n + 1 : ℝ) := by
          show _ ≤ _
          rw [div_le_div_iff_of_pos_right (by positivity)]
          convert hp' using 1
          refine Finset.sum_congr rfl ?_
          exact fun _ mem => by
            unfold x'
            rw [Finset.mem_range] at mem
            rw [if_pos mem]
         _ ≥ _ := by
          rw [mul_div_cancel_right₀]
          exact (show 0 ≠ (n + 1 : ℝ) from ne_of_lt (by positivity)).symm
    · exact Finset.not_mem_range_self
    · positivity
  | hP =>
    have aux : ∀ (x : ℕ → ℝ), (∀ i, x i > 0) → ∀ (k : ℕ), (∑ i in Finset.range (2 ^ k), x i) / (2 ^ k : ℝ) ≥ (∏ i in Finset.range (2 ^ k), x i) ^ ((1 : ℝ) / (2 ^ k)) := by
      intro x pos k
      induction k generalizing x pos with
      | zero =>
        simp only [pow_zero, Finset.range_one, Finset.sum_singleton, Finset.prod_singleton, div_one, Real.rpow_one]
        exact le_refl _
      | succ k hk =>
        rw [Finset.range_eq_Ico] at hk
        rw [Finset.range_eq_Ico,
          show Finset.Ico 0 (2 ^ (k + 1)) = Finset.Ico 0 (2 ^ k) ∪ Finset.Ico (2 ^ k) (2 ^ (k + 1)) by
            rw [Finset.Ico_union_Ico_eq_Ico]
            · exact Nat.zero_le _
            · rw [pow_succ]
              omega]
        have disj : Disjoint (Finset.Ico 0 (2 ^ k)) (Finset.Ico (2 ^ k) (2 ^ (k + 1))) := by
          exact Finset.Ico_disjoint_Ico_consecutive 0 (2 ^ k) (2 ^ (k + 1))
        rw [Finset.sum_union disj, Finset.prod_union disj]; clear disj
        have aux₁ : 0 < ∏ i ∈ Finset.Ico 0 (2 ^ k), x i := by
          refine Finset.prod_pos ?_
          exact fun _ _ => pos _
        have aux₂ : 0 < ∏ i ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), x i := by
          refine Finset.prod_pos ?_
          exact fun _ _ => pos _
        have aux₃ : 0 < ∑ i ∈ Finset.Ico 0 (2 ^ k), x i := by
          refine Finset.sum_pos ?_ ?_
          · exact fun _ _ => pos _
          · refine Finset.nonempty_Ico.mpr ?_
            positivity
        have aux₄ : 0 < ∑ i ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), x i := by
          refine Finset.sum_pos ?_ ?_
          · exact fun _ _ => pos _
          · refine Finset.nonempty_Ico.mpr ?_
            rw [pow_lt_pow_iff_right₀ (by omega)]
            omega
        nth_rw 2 3 [pow_succ]
        rw [← div_div, add_div]
        rw [← div_div, ← mul_one (1 / (2 ^ k)), ← mul_div, Real.rpow_mul (by positivity), Real.mul_rpow (by positivity) (by positivity)]
        let x' : ℕ → ℝ := fun i => x (i + 2 ^ k)
        have aux : ∀ n m : ℝ, n > 0 → m > 0 → (n + m) / 2 ≥ (n * m) ^ ((1 : ℝ) / 2) := by
          intro n m pos₁ pos₂
          show _ ≤ _
          rw [one_div, Real.rpow_inv_le_iff_of_pos (by positivity) (by positivity) (by positivity),
            Real.div_rpow (by positivity) (by positivity),
              le_div_iff₀ (by positivity)]
          rw [show (2 : ℝ) ^ (2 : ℝ) = 4 by norm_num]
          rw [show (n + m) ^ (2 : ℝ) = (n + m) ^ 2 by norm_cast]
          refine le_of_sub_nonneg ?_
          calc
            _ ≤ (n - m) ^ 2 := by
              positivity
            _ = _ := by
              ring_nf
        calc
          _ ≥ ((∑ x_1 ∈ Finset.Ico 0 (2 ^ k), x x_1) / 2 ^ k * ((∑ x_1 ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), x x_1) / 2 ^ k)) ^ ((1 : ℝ) / 2) := by
            refine aux _ _ ?_ ?_
            · exact div_pos aux₃ (by positivity)
            · exact div_pos aux₄ (by positivity)
          _ ≥ _ := by
            show _ ≤ _
            rw [Real.rpow_le_rpow_iff (by positivity) (by positivity) (by positivity)]
            refine mul_le_mul ?_ ?_ (by positivity) (by positivity)
            · exact hk _ pos
            · have aux₅ : (∏ i ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), x i) ^ ((1 : ℝ) / 2 ^ k) = (∏ i ∈ Finset.Ico 0 (2 ^ k), x' i) ^ ((1 : ℝ) / 2 ^ k) := by
                symm
                let f : ℕ → ℕ := fun n => n + 2 ^ k
                congr 1
                refine Finset.prod_nbij f ?_ ?_ ?_ ?_
                · intro a mem
                  rw [Finset.mem_Ico] at *
                  unfold f
                  omega
                · intro _ _ _ _ eq
                  unfold f at eq
                  omega
                · intro a mem
                  rw [Set.mem_image]
                  simp_rw [Finset.toSet, Set.mem_setOf, Finset.mem_Ico] at *
                  exists a - 2 ^ k
                  unfold f
                  omega
                · exact fun _ _ => by
                    unfold x' f
                    exact rfl
              have aux₆ : (∑ i ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), x i) / 2 ^ k = (∑ i ∈ Finset.Ico 0 (2 ^ k), x' i) / 2 ^ k := by
                symm
                let f : ℕ → ℕ := fun n => n + 2 ^ k
                congr 1
                refine Finset.sum_nbij f ?_ ?_ ?_ ?_
                · intro a mem
                  rw [Finset.mem_Ico] at *
                  unfold f
                  omega
                · intro _ _ _ _ eq
                  unfold f at eq
                  omega
                · intro a mem
                  rw [Set.mem_image]
                  simp_rw [Finset.toSet, Set.mem_setOf, Finset.mem_Ico] at *
                  exists a - 2 ^ k
                  unfold f
                  omega
                · exact fun _ _ => by
                    unfold x' f
                    exact rfl
              rw [aux₅, aux₆]
              exact hk _ (fun _ => by
                unfold x'
                exact pos _)
    refine Set.Infinite.mono (s := {2 ^ k - 1 | k : ℕ}) ?_ ?_
    · intro kpow mem
      rw [Set.mem_setOf] at mem
      rcases mem with ⟨k, two_pow⟩
      rw [Set.mem_setOf, ← two_pow]
      convert fun x pos => aux x pos k using 2
      norm_cast
      rw [Nat.sub_add_cancel (Nat.one_le_pow _ _ (by positivity))]
    · rw [← Set.infinite_coe_iff]
      refine (Equiv.infinite_iff (α := ℕ) ?_).mp inferInstance
      let toFun : ℕ → {2 ^ k - 1 | k : ℕ} := fun n =>
        ⟨2 ^ n - 1, ⟨n, rfl⟩⟩
      let invFun : {2 ^ k - 1 | k : ℕ} → ℕ := fun x =>
        Classical.choose x.property
      exact {
        toFun := toFun
        invFun := invFun
        left_inv := by
          intro x
          unfold toFun invFun
          apply_fun fun x => 2 ^ x - 1
          · exact Classical.choose_spec (toFun x).property
          · intro n m eq
            change _ - 1 = _ - 1 at eq
            apply Nat.sub_one_cancel at eq
            · exact Nat.pow_right_injective (le_refl _) <| eq
            · exact Nat.one_le_pow _ _ (by positivity)
            · exact Nat.one_le_pow _ _ (by positivity)
        right_inv := by
          intro x
          unfold toFun invFun
          rw [← Subtype.val_inj]
          exact Classical.choose_spec x.property
      }
end induction

section tactic_match

variable {x y : ℝ}
example : x < |y| → x < y ∨ x < -y := by
  match le_or_gt 0 y with
    | Or.inl h =>
      rw [abs_of_nonneg h]
      intro h; left; exact h
    | Or.inr h =>
      rw [abs_of_neg h]
      intro h; right; exact h

theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  match le_or_gt 0 x with
  | Or.inl h =>
    rw [abs_of_nonneg h]
    linarith
  | Or.inr h =>
    rw [abs_of_neg h]

theorem abs_add'' (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  match le_or_gt 0 (x + y) with
  | Or.inl h =>
    rw [abs_of_nonneg h]
    linarith [le_abs_self x, le_abs_self y]
  | Or.inr h =>
    rw [abs_of_neg h]
    linarith [neg_le_abs_self x, neg_le_abs_self y]

end tactic_match
