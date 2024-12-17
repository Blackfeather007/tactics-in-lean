import Mathlib.Tactic

section Obtain

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



end Obtain
