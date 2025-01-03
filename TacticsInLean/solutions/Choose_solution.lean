import Mathlib.Tactic


open Classical
suppress_compilation -- because everything is noncomputable

#help tactic choose

example (h : ∀ n m : ℕ, ∃ i j, m = n + i ∨ m + j = n) : True := by
    choose i j h using h
    guard_hyp i : ℕ → ℕ → ℕ
    guard_hyp j : ℕ → ℕ → ℕ
    guard_hyp h : ∀ (n m : ℕ), m = n + i n m ∨ m + j n m = n
    trivial

example (h : ∀ i : ℕ, i < 7 → ∃ j, i < j ∧ j < i+i) : True := by
  choose! f h h' using h
  guard_hyp f : ℕ → ℕ
  guard_hyp h : ∀ (i : ℕ), i < 7 → i < f i
  guard_hyp h' : ∀ (i : ℕ), i < 7 → f i < i + i
  trivial

section Introduction1
--Reference : https://www.ma.imperial.ac.uk/~buzzard/xena/formalising-mathematics-2024/Part_C/tactics/choose.html
--Reference : https://github.com/leanprover-community/mathlib4/blob/725fd7ac1c92cf4d7984b25646052f5a6e717d31/Mathlib/Tactic/Choose.lean#
/-
 **∀ x, ∃ y, P(x,y) (where P(x,y) is some true-false statement depend on x and y)**
 **to an actual function which inputs an x and outputs a y such that P(x,y) is true.**
 * `choose a b h h' using hyp` takes a hypothesis `hyp` of the form
  `∀ (x : X) (y : Y), ∃ (a : A) (b : B), P x y a b ∧ Q x y a b`
  for some `P Q : X → Y → A → B → Prop` and outputs
  into context a function `a : X → Y → A`, `b : X → Y → B` and two assumptions:
  `h : ∀ (x : X) (y : Y), P x y (a x y) (b x y)` and
  `h' : ∀ (x : X) (y : Y), Q x y (a x y) (b x y)`. It also works with dependent versions.

* `choose! a b h h' using hyp` does the same, except that it will remove dependency of
  the functions on propositional arguments if possible. For example if `Y` is a proposition
  and `A` and `B` are nonempty in the above example then we will instead get
  `a : X → A`, `b : X → B`, and the assumptions
  `h : ∀ (x : X) (y : Y), P x y (a x) (b x)` and
  `h' : ∀ (x : X) (y : Y), Q x y (a x) (b x)`.

The `using hyp` part can be omitted,
which will effectively cause `choose` to start with an `intro hyp`.
-/
example (X : Type) (P : X → ℝ → Prop)
/-
`h` is the hypothesis that given some `ε > 0` you can find an `x` such that the proposition is true for `x` and `ε`
-/
(h : ∀ ε > 0, ∃ x, P x ε) :
/-
Conclusion: there's a sequence of elements of `X` satisfying the condition for smaller and smaller ε
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
--Sometimes the **recases and obtain may not work**
----`主讲老师请务必强调, 能用rcases 或 obtain 解决就不要用 choose`

variable {α β : Type*} [Inhabited α]

#check (default : α)
/-
 Inhabited α is a typeclass that says that α has a designated element, called (default : α).
 This is sometimes referred to as a "pointed type".
 This class is used by functions that need to return a value of the type when called "out of domain".
 For example, Array.get! arr i : α returns a value of type α when arr : Array α, but if i is not in range of the array,
 it reports a panic message, but this does not halt the program, so it must still return a value of type α
 (and in fact this is required for logical consistency), so in this case it returns default.
-/

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

end Introduction2



section Example1
--Reference : https://github.com/leanprover-community/mathlib4/blob/b09464fc7b0ff4bcfd4de7ff54289799009b5913/Mathlib/Logic/Equiv/Set.lean#L406
--`有类型转换`

open Set

#check Equiv.Set.imageOfInjOn

/-- If a function `f` is injective on a set `s`, then `s` is equivalent to `f '' s`. -/
def myimageOfInjOn {α β} (f : α → β) (s : Set α) (H : InjOn f s) : s ≃ f '' s where
  toFun := by
    intro p
    use f p
    exact mem_image_of_mem f p.2
  invFun := by
    intro p
    --`挖空`
    have hint : p.1 ∈ f '' s := p.2
    use choose p.2
    exact (choose_spec p.2).1
  left_inv := by
    --We want to prove f⁻¹ (f p) = p
    intro p
    have : f p ∈ f '' s := mem_image_of_mem f p.2
    show ⟨choose this, (choose_spec this).1⟩ = p

    have feq : f (choose this) = f p := by
      --`挖空`
      exact (choose_spec (mem_image_of_mem f p.2)).2

    have : (choose this) =  p := by
      apply H
      --`挖空`
      exact (choose_spec (mem_image_of_mem f p.2)).1
      exact p.2
      exact feq
    exact SetCoe.ext this

  right_inv := by
    --We want to prove f (f⁻¹ p) = p
    intro p
    have : f (choose p.2) = p.1 := by
      --`挖空`
      exact (choose_spec p.2).2

    exact SetCoe.ext this
end Example1



section Example2

open Set

theorem mySet.InjOn.image_iInter_eq{α : Type*} {β : Type*} {ι : Sort*} [Nonempty ι] [Inhabited ι]{s : ι → Set α} {f : α → β}
 (h : Set.InjOn f (⋃ (i : ι), s i)) : f '' ⋂ (i : ι), s i ⊇ ⋂ (i : ι), f '' s i := by
  intro y hy
  simp only [mem_iInter, mem_image] at hy
  --`挖空`
  choose x hx hy using hy
  use x default

  constructor
  · apply mem_iInter.2
    intro i
    suffices x default = x i by
      rw [this]
      apply hx
    have : ∀ i, x i ∈ ⋃ j, s j := fun i => (subset_iUnion _ _) (hx i)
    apply h (this _) (this _)
    simp only [hy]
  · exact hy default

end Example2



section Exercise1
--Reference : https://github.com/leanprover-community/mathlib4/blob/c91dd0e151d3f0b6755d35119cd7943a516addb8/Mathlib/Data/Set/Function.lean#L669-L680

open Set

#check exists_eq_graphOn_image_fst

theorem myexists_eq_graphOn_image_fst{α : Type*} {β : Type*} [Nonempty β] {s : Set (α × β)}
(h : Set.InjOn Prod.fst s) : ∃ (f : α → β), s = Set.graphOn f (Prod.fst '' s):= by
  have : ∀ x ∈ Prod.fst '' s, ∃ y, (x, y) ∈ s := forall_mem_image.2 fun (x, y) h ↦ ⟨y, h⟩
  --`挖空`
  choose! f hf using this

  rw [forall_mem_image] at hf
  use f
  rw [graphOn, image_image, EqOn.image_eq_self]
  exact fun x hx ↦ h (hf hx) hx rfl

end Exercise1



section Exercise2
--Reference : https://github.com/leanprover-community/mathlib4/blob/c91dd0e151d3f0b6755d35119cd7943a516addb8/Mathlib/Data/Set/Lattice.lean#L198-L201

open Set

#check nonempty_of_nonempty_iUnion

theorem mynonempty_of_nonempty_iUnion {α : Type*} {ι : Sort*} {s : ι → Set α} (h_Union : (⋃ i, s i).Nonempty) :
 Nonempty ι := by
  obtain ⟨x, hx⟩ := h_Union
  have : ∃ i, x ∈ s i := mem_iUnion.mp hx
  use Classical.choose this

end Exercise2



section Exercise3

open Pointwise

def Hom_top_product_of_normal_of_disjoint (H K : Set ℝ) : (H * K) → (H × K) := by
  intro x

  have mem_mul_eq : ∃ x_1 ∈ H, ∃ y ∈ K, x_1 * y = x.1 := by
    apply Set.mem_mul.mp
    exact Subtype.coe_prop x

  --`此题涉及到若干处类型转换, 较为困难,因此主讲老师 必须 讲解这道题`
  --之所以考虑保留此题是考虑到类型转换"早折磨晚折磨应该也差不多"

  -- obtain⟨a, ha⟩ := mem_mul_eq
  set a := choose mem_mul_eq with a_def
  set ha := choose_spec mem_mul_eq
  set b := choose ha.2 with b_def
  set hb := choose_spec ha.2
  -- simp only [Subsemigroup.mem_carrier, Submonoid.mem_toSubsemigroup, Subgroup.mem_toSubmonoid, ←
  --   a_def, ← b_def] at ha hb--`非必须, 方便看infoview`

  use ⟨a, ha.1⟩, b
  exact hb.1

end Exercise3



section Exercise4
--Reference : https://github.com/leanprover-community/mathlib4/blob/c91dd0e151d3f0b6755d35119cd7943a516addb8/Mathlib/Data/Set/Lattice.lean#L1942-L1949

#check Set.sigmaEquiv

noncomputable def mySet.sigmaEquiv{α : Type*} {β : Type*} (s : α → Set β) (hs : ∀ (b : β), ∃! i : α, b ∈ s i) :
(i : α) × (s i) ≃ β where
  toFun := by
    intro p
    use p.2
  invFun := by
    intro b
    exact ⟨(hs b).choose, ⟨b, (hs b).choose_spec.1⟩⟩
  left_inv := by
    intro p
    ext
    · show (hs p.2).choose = p.1
      apply ExistsUnique.unique (hs p.2)
      · exact (hs p.2).choose_spec.1
      · exact Subtype.coe_prop p.snd
    · rfl
  right_inv _:= rfl

end Exercise4



section Exercise5
--Some thing useful which similar to Classical.choose
--Reference : https://github.com/leanprover-community/mathlib4/blob/c91dd0e151d3f0b6755d35119cd7943a516addb8/Mathlib/Algebra/Order/Archimedean/Basic.lean#L225-L236

#check Nat.find
#check Nat.find_spec
#check Nat.find_min

#check exists_nat_pow_near

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
--Reference : https://github.com/leanprover-community/mathlib4/blob/1ed7634f46ba697f891ebfb3577230329d4b7196/Mathlib/Algebra/Order/CauSeq/BigOperators.lean#L154

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
