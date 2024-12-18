/-编写者 : 袁奕(Yuan Yi), 其中`橘色`字体表示面向助教老师们的注释
-/
import Mathlib

open Classical
suppress_compilation -- because everything is noncomputable



section Introduction1
--Reference : https://www.ma.imperial.ac.uk/~buzzard/xena/formalising-mathematics-2024/Part_B/the_axiom_of_choice.html
/- In my experience, the way people want to use the axiom of choice when doing mathematics in Lean
 is to get an element of X not from a hypothesis ∃ x : X, true, but from a hypothesis like
 ∃ x : ℝ, x^2 = 2 or more generally ∃ x : X, p x where p : X → Prop is a predicate on X. The way to
 do this is as follows: you run Classical.choose on h : ∃ x : X, p x to get the element of X, and
 the proof that this element satisfies p is Classical.choose_spec h. Here’s a worked example.-/

open Polynomial -- so I can use notation ℂ[X] for polynomial rings
                -- and so I can write `X` and not `polynomial.X`

def f : ℂ[X] := X^5 + X + 37 -- a random polynomial

lemma f_degree : degree f = 5 := by
  unfold f
  compute_degree -- polynomial degree computing tactic
  · norm_num
  · exact Nat.le_of_ble_eq_true rfl

theorem f_has_a_root : ∃ (z : ℂ), f.IsRoot z := by
  apply Complex.exists_root -- the fundamental theorem of algebra
  -- ⊢ 0 < degree f
  rw [f_degree]
  -- ⊢ 0 < 5
  norm_num

-- let z be a root of f (getting data from a theorem)
def z : ℂ := choose f_has_a_root

-- proof that z is a root of f (the "API" for `Classical.choose`)
theorem z_is_a_root_of_f : f.IsRoot z := by exact choose_spec f_has_a_root

-- #check choose f_has_a_root
-- #check choose_spec f_has_a_root

--We should prioritize using **recases** or **obtain** over **Classcal.choose**.
example : 1 = 1 := by
  rcases f_has_a_root with  ⟨z1, z1_is_a_root_of_f⟩
  -- #check z1
  -- #check z1_is_a_root_of_f
  have z1_is_a_root_of_f : f.IsRoot z1 := by exact z1_is_a_root_of_f

  simp only

example : 1 = 1 := by
  obtain ⟨z2, z2_is_a_root_of_f⟩ := f_has_a_root
  -- #check z2
  -- #check z2_is_a_root_of_f
  have z2_is_a_root_of_f : f.IsRoot z2 := by exact z2_is_a_root_of_f

  simp only

end Introduction1



section Introduction3
--Reference : https://www.ma.imperial.ac.uk/~buzzard/xena/formalising-mathematics-2024/Part_C/tactics/choose.html
/- Summary : The choose tactic is a relatively straightforward way to go from a proof of a
 proposition of the form ∀ x, ∃ y, P(x,y) (where P(x,y) is some true-false statement depend on x
 and y), to an actual function which inputs an x and outputs a y such that P(x,y) is true.

  Basic usage : The simplest situation where you find yourself wanting to use choose is if you have
 a function f : X → Y which you know is surjective, and you want to write down a one-sided inverse
 g : Y → X, i.e., such that f(g(y))=y for all y : Y. Here’s the set-up:-/

/-`X` is an abstract type and `P` is an abstract true-false
statement depending on an element of `X` and a real number.-/
example (X : Type) (P : X → ℝ → Prop)
    /-
    `h` is the hypothesis that given some `ε > 0` you can find
    an `x` such that the proposition is true for `x` and `ε`
    -/
    (h : ∀ ε > 0, ∃ x, P x ε) :
  /-
  Conclusion: there's a sequence of elements of `X` satisfying the
  condition for smaller and smaller ε
  -/
  ∃ u : ℕ → X, ∀ n, P (u n) (1/(n+1)) := by
  choose g hg using h
  /-
  g : Π (ε : ℝ), ε > 0 → X
  hg : ∀ (ε : ℝ) (H : ε > 0), P (g ε H) ε
  -/
  -- need to prove 1/(n+1)>0 (this is why I chose 1/(n+1) not 1/n, as 1/0=0 in Lean!)
  let u : ℕ → X := fun n ↦ g (1/(n+1)) (by positivity)
  use u -- `u` works
  intro n
  apply hg

end Introduction3



section Introduction2
--Reference : Mathmatics in Lean C4S2
/- To define the inverse of a function f : α → β, we will use two new ingredients. First, we need to
 deal with the fact that an arbitrary type in Lean may be empty. To define the inverse to f at y
 when there is no x satisfying f x = y, we want to assign a default value in α. Adding the
 annotation [Inhabited α] as a variable is tantamount to assuming that α has a preferred element,
 which is denoted default. Second, in the case where there is more than one x such that f x = y, the
 inverse function needs to choose one of them. This requires an appeal to the axiom of choice. Lean
 allows various ways of accessing it; one convenient method is to use the classical choose operator,
  illustrated below.
-/
variable {α β : Type*} [Inhabited α]

#check (default : α)

variable (P : α → Prop) (h : ∃ x, P x)

#check Classical.choose h

example : P (Classical.choose h) :=
  Classical.choose_spec h

/- Given h : ∃ x, P x, the value of Classical.choose h is some x satisfying P x. The theorem
Classical.choose_spec h says that Classical.choose h meets this specification. With these in hand,
we can define the inverse function as follows: -/

def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then Classical.choose h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  rw [inverse, dif_pos h]
  exact Classical.choose_spec h

/-The lines noncomputable section and open Classical are needed because we are using classical logic
 in an essential way. On input y, the function inverse f returns some value of x satisfying f x = y
 if there is one, and a default element of α otherwise. This is an instance of a dependent if
 construction, since in the positive case, the value returned, Classical.choose h, depends on the
 assumption h. The identity dif_pos h rewrites if h : e then a else bto a given h : e, and,
 similarly, dif_neg h rewrites it to b given h : ¬ e. There are also versions if_pos and if_neg that
 works for non-dependent if constructions and will be used in the next section. The theorem
 inverse_spec says that inverse f meets the first part of this specification.-/

end Introduction2



section Example1

--Sometimes the **recases and obtain may not work**
open Pointwise
/-**Example 1** : backgroud(this project will be one of the finnal projet) :
Suppose that $G$ is a group with subgroups $H$ and $K$ such that $H \cap K = \{1\}$, then
$HK \cong H \times K$ (as sets).-/
def Hom_top_product_of_normal_of_disjoint (H K : Set ℝ) : (H * K) → (H × K) := by
  intro x

  have mem_mul_eq : ∃ x_1 ∈ H, ∃ y ∈ K, x_1 * y = x.1 := by
    apply Set.mem_mul.mp
    exact Subtype.coe_prop x

  --`此题涉及到若干处类型转换, 较为困难,因此主讲老师 必须 讲解这道题`
  --之所以考虑保留此题是考虑到类型转换"早折磨晚折磨应该也差不多"
  --`主讲老师请务必强调, 能用rcases 或 obtain 解决就不要用 choose`
  -- obtain⟨a, ha⟩ := mem_mul_eq
  set a := choose mem_mul_eq with a_def
  set ha := choose_spec mem_mul_eq
  set b := choose ha.2 with b_def
  set hb := choose_spec ha.2
  -- simp only [Subsemigroup.mem_carrier, Submonoid.mem_toSubsemigroup, Subgroup.mem_toSubmonoid, ←
  --   a_def, ← b_def] at ha hb--`非必须, 方便看infoview`

  use ⟨a, ha.1⟩, b
  exact hb.1

end Example1



section Exercise1

--Reference : https://github.com/leanprover-community/mathlib4/blob/b09464fc7b0ff4bcfd4de7ff54289799009b5913/Mathlib/Logic/Equiv/Set.lean#L406
universe u v w z
variable {α : Sort u} {β : Sort v} {γ : Sort w}

open Set

/-- If a function `f` is injective on a set `s`, then `s` is equivalent to `f '' s`. -/
def imageOfInjOn1 {α β} (f : α → β) (s : Set α) (H : InjOn f s) : s ≃ f '' s where
  toFun := fun p => ⟨f p, mem_image_of_mem f p.2⟩
  invFun := fun p => ⟨Classical.choose p.2, (choose_spec p.2).1⟩
  left_inv := fun ⟨_, h⟩ => Subtype.eq
      (H (choose_spec (mem_image_of_mem f h)).1 h
        (choose_spec (mem_image_of_mem f h)).2)
  right_inv :=  fun ⟨_, h⟩ => Subtype.eq (Classical.choose_spec h).2

end Exercise1



-- section Exercise2

-- open Polynomial
-- --https://github.com/leanprover-community/mathlib4/blob/1ed7634f46ba697f891ebfb3577230329d4b7196/Mathlib/Algebra/Polynomial/Coeff.lean#L319

-- #check C_dvd_iff_dvd_coeff
-- theorem my_Polynomial.C_dvd_iff_dvd_coeff{R : Type u} [Semiring R] (r : R) (φ : Polynomial R)(h : ∀ i, r ∣ φ.coeff i) :
--  C r ∣ φ := by
--   have : ∃ c : ℕ → R, ∀ (i : ℕ), φ.coeff i = r * c i := by

--     sorry


--   choose c hc using h
--   let c' : ℕ → R := fun i => if i ∈ φ.support then c i else 0
--   let ψ : R[X] := ∑ i ∈ φ.support, monomial i (c' i)
--   use ψ
--   ext i
--   simp only [c', ψ, coeff_C_mul, mem_support_iff, coeff_monomial, finset_sum_coeff,
--     Finset.sum_ite_eq']
--   split_ifs with hi
--   · rw [hc]
--   · rw [Classical.not_not] at hi
--     rwa [mul_zero]

-- end Exercise2



section Exercise3
--Some thing useful which similar to Classical.choose

#check Nat.find
#check Nat.find_spec
#check Nat.find_min

--https://github.com/leanprover-community/mathlib4/blob/1ed7634f46ba697f891ebfb3577230329d4b7196/Mathlib/Algebra/Order/CauSeq/BigOperators.lean#L154
#check IsCauSeq.of_decreasing_bounded

theorem my_IsCauSeq.of_decreasing_bounded (f : ℕ → ℝ) {a : ℝ}(ham : ∀ n, |f n| ≤ a) (hnm : ∀ n, f n.succ ≤ f n) :
IsCauSeq abs f := fun ε ε0 ↦ by

  let ⟨k, hk⟩ := Archimedean.arch a ε0
  have h : ∃ l : ℕ, ∀ n , a - l • ε < f n := by
    use k + k + 1
    intro n
    calc
      _ = a - k • ε - k • ε - ε := by ring
      _ < - a := by linarith
      _ ≤ _ := neg_le_of_abs_le (ham n)

  let l := Nat.find h
  --`此处挖空`
  have hl : ∀ (n : ℕ), a - l • ε < f n := Nat.find_spec h

  have hl0 : l ≠ 0 := by
    intro heq0
    simp only [heq0, zero_smul, sub_zero] at hl
    linarith[lt_of_le_of_lt (ham 0) (hl 0), le_abs_self (f 0)]

  have hint : l - 1 < l := by simp only [tsub_lt_self_iff, zero_lt_one, and_true,Nat.zero_lt_of_ne_zero hl0]

  --`此处挖空`
  have hl' : ∃ (n : ℕ), a - (l - 1) • ε ≥ f n := by
    have := Nat.find_min h hint
    simp only [not_forall, not_lt] at this
    exact this

  obtain ⟨i, hi⟩ := hl'
  use i
  intro j hj

  have hfij : f j ≤ f i := by
    apply (Nat.rel_of_forall_rel_succ_of_le_of_le (· ≥ ·) (fun n a => hnm n) (Nat.zero_le i) hj).le

  rw [abs_of_nonpos (sub_nonpos.2 hfij), neg_sub, sub_lt_iff_lt_add']
  calc
    f i ≤ a - Nat.pred l • ε := hi
    _ = a - l • ε + ε := by
      conv =>
        rhs
        rw [← Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hl0), succ_nsmul, sub_add, add_sub_cancel_right]
    _ < f j + ε := by linarith[hl j]

end Exercise3


--Reference : https://github.com/leanprover-community/mathlib4/blob/197eebfa5455aa09b7a4c2ad3c3eb9123245df90/Mathlib/FieldTheory/JacobsonNoether.lean#L120



-- example [R : Type*][Ring R](ι : ℕ → Ideal R) : ∀ i, ι i ≤ ι (i + 1) → ∃ k, ∀ i > k , ι i = ι k := sorry
