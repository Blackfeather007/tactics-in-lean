import Mathlib.Tactic
import Mathlib.Data.Real.Irrational

section p₁
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
end p₁

section p₂
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
end p₂

section p₃
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
end p₃

section p₄
/- Maybe we could come up with a better problem, so that it fits more `induction`. -/
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
end p₄

section p₅
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
end p₅

section p₆
lemma List.sorted_of_sorted_append_right {α : Type*} (l₁ l₂ : List α) (r : α → α → Prop) (h : (l₁ ++ l₂).Sorted r) : l₂.Sorted r := by
  induction l₁ with
  | nil =>
    rw [List.nil_append] at h
    exact h
  | cons a l hl =>
    simp only [List.cons_append, List.sorted_cons] at h ⊢
    exact hl h.right
end p₆

section p₇
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
end p₈

section p₉
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
end p₉

section p₁₀
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
end p₁₀
