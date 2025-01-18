import Mathlib.Tactic

section Rcases

example {x : ℝ} (h : x = 1 ∨ x = 2) : x ^ 2 - 3 * x + 2 = 0 := by
  rcases h with rfl | rfl <;> norm_num

example {x y : ℝ} (h : x = 2 ∨ y = -2) : x * y + 2 * x = 2 * y + 4 := by
  rcases h with rfl | rfl <;> ring



def f (_ : List Empty) (b : Bool) := b

@[simp]
theorem lem1 (a : Bool) : f [] a = a := rfl

@[simp]
theorem lem2 (a b : Bool) (x y : List Empty)
  (h : f x a = f y b) : x = y := by
    rcases x with _ | ⟨⟨⟩, _⟩
    rcases y with _ | ⟨⟨⟩, _⟩
    rfl
example : (([] : List Empty).take 0) = [] := by rfl

namespace ZMod

theorem mul_inv_of_unit' {n : ℕ} {a : ZMod n} (h : IsUnit a) : a * a⁻¹ = 1 := by
  rcases h with ⟨u, rfl⟩
  rw [inv_coe_unit, u.mul_inv]

end ZMod

/-
https://leanprover.zulipchat.com/#narrow/channel/113489-new-members/topic/Need.20help.20understanding.20a.20type.20class.20example
-/

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


end Rcases
