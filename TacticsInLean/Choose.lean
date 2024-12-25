import Mathlib.Tactic


open Classical
suppress_compilation

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
example (X : Type) (P : X → ℝ → Prop)(h : ∀ ε > 0, ∃ x, P x ε) : ∃ u : ℕ → X, ∀ n, P (u n) (1/(n+1)) := by
  --`用choose tactic 替换掉下面两行，示例如下`
  let g : (ε : ℝ) → ε > 0 → X := sorry
  have hg : ∀ (ε : ℝ) (a : ε > 0), P (g ε a) ε := sorry
  /-
  `-`let g : (ε : ℝ) → ε > 0 → X := sorry
  `-`have hg : ∀ (ε : ℝ) (a : ε > 0), P (g ε a) ε := sorry
  `+`choose g hg using h
  -/
  choose g hg using h

  let u : ℕ → X := fun n ↦ g (1/(n+1)) (by positivity)
  use u
  intro n
  apply hg

end Introduction1



section Introduction2

variable {α β : Type*} [Inhabited α]

variable (P : α → Prop) (h : ∃ x, P x)

#check Classical.choose h

example : P (Classical.choose h) :=
  --use `Classical.choose_spec`
  sorry

def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then Classical.choose h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  rw [inverse, dif_pos h]
  --use `Classical.choose_spec`
  sorry

end Introduction2



section Example1

open Set

def myimageOfInjOn {α β} (f : α → β) (s : Set α) (H : InjOn f s) : s ≃ f '' s where
  toFun := by
    intro p
    use f p
    exact mem_image_of_mem f p.2
  invFun := by
    intro p
    have hint : p.1 ∈ f '' s := p.2
    --use `Classical.choose` and `Classical.choose_spec`
    sorry
  left_inv := by
    intro p
    have : f p ∈ f '' s := mem_image_of_mem f p.2

    have feq : f (choose this) = f p := by
      --use `Classical.choose_spec`
      sorry

    have : (choose this) =  p := by
      apply H
      --use `Classical.choose_spec`
      sorry
      exact p.2
      exact feq
    exact SetCoe.ext sorry

  right_inv := by
    intro p
    have : f (choose p.2) = p.1 := by
      --use `Classical.choose_spec`
      sorry

    exact SetCoe.ext sorry
end Example1



section Example2

open Set

theorem mySet.InjOn.image_iInter_eq{α : Type*} {β : Type*} {ι : Sort*} [Nonempty ι] [Inhabited ι]{s : ι → Set α} {f : α → β}
 (h : Set.InjOn f (⋃ (i : ι), s i)) : f '' ⋂ (i : ι), s i ⊇ ⋂ (i : ι), f '' s i := by
  intro y hy
  simp only [mem_iInter, mem_image] at hy

  --`用choose tactic 替换掉下面两行，如 Introduction1 示例所示`
  let x : ι → α := sorry
  have hx : ∀ (i : ι), x i ∈ s i := sorry
  have hy : ∀ (i : ι), f (x i) = y := sorry

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

open Set

theorem myexists_eq_graphOn_image_fst{α : Type*} {β : Type*} [Nonempty β] {s : Set (α × β)}
(h : Set.InjOn Prod.fst s) : ∃ (f : α → β), s = Set.graphOn f (Prod.fst '' s):= by
  have : ∀ x ∈ Prod.fst '' s, ∃ y, (x, y) ∈ s := forall_mem_image.2 fun (x, y) h ↦ ⟨y, h⟩

  --`用choose！tactic 替换掉下面两行，如 Introduction1 示例所示`
  let f : α → β := sorry
  have hf : ∀ x ∈ Prod.fst '' s, (x, f x) ∈ s := sorry

  rw [forall_mem_image] at hf
  use f
  rw [graphOn, image_image, EqOn.image_eq_self]
  exact fun x hx ↦ h (hf hx) hx rfl

end Exercise1



section Exercise2

open Set

theorem mynonempty_of_nonempty_iUnion {α : Type*} {ι : Sort*} {s : ι → Set α} (h_Union : (⋃ i, s i).Nonempty) :
 Nonempty ι := by
  obtain ⟨x, hx⟩ := h_Union
  have : ∃ i, x ∈ s i := mem_iUnion.mp hx
  --use `Classical.choose_spec``
  sorry

end Exercise2



section Exercise3

open Pointwise

def Hom_top_product_of_normal_of_disjoint (H K : Set ℝ) : (H * K) → (H × K) := by
  intro x

  have mem_mul_eq : ∃ x_1 ∈ H, ∃ y ∈ K, x_1 * y = x.1 := by
    apply Set.mem_mul.mp
    exact Subtype.coe_prop x

  --use `Classical.choose_spec`
  set a := choose mem_mul_eq
  have ha : a ∈ H ∧ ∃ y ∈ K, a * y = x := by sorry
  set b := choose ha.2

  sorry


end Exercise3



section Exercise4

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
      · show p.2.1 ∈ s (hs p.2).choose
        sorry
      · show p.2.1 ∈ s p.1
        exact Subtype.coe_prop p.snd
    · rfl
  right_inv _:= rfl

end Exercise4



section Exercise5
--Some thing useful which similar to Classical.choose

#check Nat.find
#check Nat.find_spec
#check Nat.find_min

theorem myexists_nat_pow_near {x y : ℕ}(hx : 1 ≤ x) (hy : 1 < y) : ∃ n : ℕ, y ^ n ≤ x ∧ x < y ^ (n + 1) := by
  have h : ∃ n : ℕ, x < y ^ n := pow_unbounded_of_one_lt _ hy
  let n := Nat.find h
  have hn : x < y ^ n := by sorry
  have hnp : 0 < n :=
    pos_iff_ne_zero.2 fun hn0 => by rw [hn0, pow_zero] at hn; exact not_le_of_gt hn hx
  have hnsp : Nat.pred n + 1 = n := Nat.succ_pred_eq_of_pos hnp
  have hltn : Nat.pred n < n := Nat.pred_lt (ne_of_gt hnp)
  sorry

end Exercise5



section Exercise6

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

  have hl : ∀ (n : ℕ), a - l • ε < f n := sorry

  have hl0 : l ≠ 0 := by
    intro heq0
    simp only [heq0, zero_smul, sub_zero] at hl
    linarith[lt_of_le_of_lt (ham 0) (hl 0), le_abs_self (f 0)]

  have hint : l - 1 < l := by simp only [tsub_lt_self_iff, zero_lt_one, and_true,Nat.zero_lt_of_ne_zero hl0]


  have hl' : ∃ (n : ℕ), a - (l - 1) • ε ≥ f n := by
    sorry

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
