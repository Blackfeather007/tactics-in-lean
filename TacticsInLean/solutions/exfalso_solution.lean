import Mathlib.Tactic

#help tactic exfalso

section p₁
example (h : False) : 1 = 2 := by
  exfalso
  exact h
end p₁

section p₂
example (p q : Prop) (h₁ : p ∧ q) (h₂ : p → ¬q) : ∃ n : ℕ, ∀ m : ℕ, m ≤ n := by
  exfalso
  exact h₂ h₁.left <| h₁.right
end p₂

section p₃
example (n : ℕ) [NeZero n] (x y : ZMod n) : (x + y).val = (x.val + y.val) % n := by
  cases n
  · exfalso
    exact NeZero.ne 0 <| rfl
  · exact rfl
end p₃

section p₄
example (x : Fin 0) : ∀ n : ℕ, ∃ x y z : ℤ, x ^ n + y ^ n = z ^ n := by
  -- exact Fin.elim0 x
  exfalso
  exact not_lt_of_le (Nat.zero_le x) <| x.isLt
end p₄

section p₅
example (p : ℕ) (hp : p.Prime) (h₁ : ∃ a b, p = a ^ 2 + b ^ 2) (h₂ : p % 4 = 3) : p = 2 := by
  apply Nat.Prime.eq_two_or_odd' at hp
  cases hp with
  | inl h =>
    exfalso
    rw [h, Nat.mod_eq_of_lt (show 2 < 4 by omega)] at h₂
    omega
  | inr h =>
    rcases h₁ with ⟨a, b, eq⟩
    repeat rw [pow_two] at eq
    exfalso
    cases Nat.even_or_odd a <;> cases Nat.even_or_odd b
    · rename Even a => ha
      rename Even b => hb
      have h₁ : Even p := by
        rw [eq]
        exact Even.add (Even.mul_left ha _) (Even.mul_right hb _)
      exact Nat.not_even_iff_odd.mpr h <| h₁
    · rename Even a => ha
      rename Odd b => hb
      rcases ha with ⟨n, eqa⟩
      rcases hb with ⟨m, eqb⟩
      have h₁ : p % 4 = 1 := by
        rw [eq]
        calc
          _ = (4 * n ^ 2 + 4 * m ^ 2 + 4 * m + 1) % 4:= by
            congr 1
            rw [eqa, eqb]
            ring_nf
          _ = _ := by
            omega
      rw [h₁] at h₂
      omega
    · rename Odd a => ha
      rename Even b => hb
      rcases ha with ⟨n, eqa⟩
      rcases hb with ⟨m, eqb⟩
      have h₁ : p % 4 = 1 := by
        rw [eq]
        calc
          _ = (4 * n ^ 2 + 4 * n + 4 * m ^ 2 + 1) % 4:= by
            rw [eqa, eqb]
            ring_nf
          _ = _ := by
            omega
      rw [h₁] at h₂
      omega
    · rename Odd a => ha
      rename Odd b => hb
      have h₁ : Even p := by
        rw [eq]
        exact Odd.add_odd (Odd.mul ha ha) (Odd.mul hb hb)
      exact Nat.not_even_iff_odd.mpr h <| h₁
end p₅
