import Mathlib.Tactic


open Classical
suppress_compilation -- because everything is noncomputable


section Introduction1
--Reference : https://www.ma.imperial.ac.uk/~buzzard/xena/formalising-mathematics-2024/Part_C/tactics/choose.html
/-
 **∀ x, ∃ y, P(x,y) (where P(x,y) is some true-false statement depend on x and y)**
 **to an actual function which inputs an x and outputs a y such that P(x,y) is true.**
-/
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

end Introduction1



section Introduction2
--Reference : Mathmatics in Lean C4S2
/-
1. Adding the annotation [Inhabited α] as a variable is tantamount to assuming that α has a preferred element,
 which is denoted default.
2. The inverse function requires an appeal to the axiom of choice.
-/
variable {α β : Type*} [Inhabited α]

#check (default : α)

variable (P : α → Prop) (h : ∃ x, P x)

#check Classical.choose h

example : P (Classical.choose h) :=
  Classical.choose_spec h

/- **Given prop h : ∃ x, P x, the value of Classical.choose h is some x satisfying P x.**
 **The theorem Classical.choose_spec h says that Classical.choose h meets this specification.**-/

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

open Set

theorem mySet.InjOn.image_iInter_eq{α : Type*} {β : Type*} {ι : Sort*} [Nonempty ι] {s : ι → Set α} {f : α → β}
 (h : Set.InjOn f (⋃ (i : ι), s i)) : f '' ⋂ (i : ι), s i = ⋂ (i : ι), f '' s i := by
  inhabit ι
  refine Subset.antisymm (image_iInter_subset s f) fun y hy => ?_
  simp only [mem_iInter, mem_image] at hy
  choose x hx hy using hy
  refine ⟨x default, mem_iInter.2 fun i => ?_, hy _⟩
  suffices x default = x i by
    rw [this]
    apply hx
  replace hx : ∀ i, x i ∈ ⋃ j, s j := fun i => (subset_iUnion _ _) (hx i)
  apply h (hx _) (hx _)
  simp only [hy]

end Exercise1



section Exercise2

open Set

--https://github.com/leanprover-community/mathlib4/blob/8bd57d67caa56c16d165be48ea7309648270f309/Mathlib/Data/Set/Lattice.lean#L201
theorem nonempty_of_nonempty_iUnion {α : Type*} {ι : Sort*} {s : ι → Set α} (h_Union : (⋃ i, s i).Nonempty) :
 Nonempty ι := by
  obtain ⟨x, hx⟩ := h_Union
  have : ∃ i, x ∈ s i := mem_iUnion.mp hx
  use Classical.choose this

end Exercise2



section Exercise3

--Reference : https://github.com/leanprover-community/mathlib4/blob/b09464fc7b0ff4bcfd4de7ff54289799009b5913/Mathlib/Logic/Equiv/Set.lean#L406
open Set

/-- If a function `f` is injective on a set `s`, then `s` is equivalent to `f '' s`. -/
def myimageOfInjOn {α : Sort*} {β : Sort*} {γ : Sort*}{α β} (f : α → β) (s : Set α) (H : InjOn f s) : s ≃ f '' s where
  toFun := fun p => ⟨f p, mem_image_of_mem f p.2⟩
  invFun := fun p => ⟨Classical.choose p.2, (choose_spec p.2).1⟩
  left_inv := fun ⟨_, h⟩ => Subtype.eq
      (H (choose_spec (mem_image_of_mem f h)).1 h
        (choose_spec (mem_image_of_mem f h)).2)
  right_inv :=  fun ⟨_, h⟩ => Subtype.eq (Classical.choose_spec h).2

end Exercise3



section Exercise4

noncomputable def mySet.sigmaEquiv{α : Type*} {β : Type*} (s : α → Set β) (hs : ∀ (b : β), ∃! i : α, b ∈ s i) :
(i : α) × ↑(s i) ≃ β where
  toFun | ⟨_, b⟩ => b
  invFun b := ⟨(hs b).choose, b, (hs b).choose_spec.1⟩
  left_inv | ⟨i, b, hb⟩ => Sigma.subtype_ext ((hs b).choose_spec.2 i hb).symm rfl
  right_inv _ := rfl

end Exercise4




section Exercise5

--Some thing useful which similar to Classical.choose

#check Nat.find
#check Nat.find_spec
#check Nat.find_min


theorem myexists_nat_pow_near {x y : ℕ}(hx : 1 ≤ x) (hy : 1 < y) : ∃ n : ℕ, y ^ n ≤ x ∧ x < y ^ (n + 1) := by
  have h : ∃ n : ℕ, x < y ^ n := pow_unbounded_of_one_lt _ hy
  let n := Nat.find h
  have hn : x < y ^ n := Nat.find_spec h
  have hnp : 0 < n :=
    pos_iff_ne_zero.2 fun hn0 => by rw [hn0, pow_zero] at hn; exact not_le_of_gt hn hx
  have hnsp : Nat.pred n + 1 = n := Nat.succ_pred_eq_of_pos hnp
  have hltn : Nat.pred n < n := Nat.pred_lt (ne_of_gt hnp)
  exact ⟨Nat.pred n, le_of_not_lt (Nat.find_min h hltn), by rwa [hnsp]⟩

end Exercise5




section Exercise6

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

end Exercise6
