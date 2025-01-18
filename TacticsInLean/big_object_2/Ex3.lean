import Mathlib

/-
Let $G$ be a group, $H_{1}$, $H_{2}$ two subgroup of $G$. If $H_{1} \cup H_{2} $ is a subgroup, then either $H_{1} \subseteq H_{2}$ or $H_{2} \subseteq H_{1}$
-/

theorem myThm {G : Type*} [Group G] (H₁ H₂ : Subgroup G) : (∃ H : Subgroup G, H.carrier = H₁.carrier ∪ H₂.carrier) ↔ H₁ ≤ H₂ ∨ H₂ ≤ H₁  := by
  constructor
  · rintro ⟨H, hH⟩
    by_cases h₀ : ¬ H₁.carrier ⊆ H₂.carrier
    · right
      intro x hx
      rcases Set.not_subset.mp h₀ with ⟨y, hy₁, hy₂⟩
      have h₁ : x * y ∈ H := by
        refine (Subgroup.mul_mem_cancel_right H ?h).mpr ?_
        · apply Subgroup.mem_carrier.mp
          rw [hH]
          exact Set.subset_union_left hy₁
        · apply Subgroup.mem_carrier.mp
          rw [hH]
          exact Set.subset_union_right hx
      have h₂ : x * y ∈ H₁ := by
        by_cases h' : x * y ∈ H₁.carrier
        exact Subgroup.mem_carrier.mp h'
        have : x * y ∈ H₂ := by
          apply Subgroup.mem_carrier.mp
          rw [← Subgroup.mem_carrier, hH] at h₁
          apply Set.mem_or_mem_of_mem_union at h₁
          rcases h₁ with h₁ | h₁
          exact False.elim (h' h₁)
          exact h₁
        apply Subgroup.mem_carrier.mp at hx
        have : y ∈ H₂.carrier := by
          exact (Subgroup.mul_mem_cancel_left H₂ hx).mp this
        exact False.elim (hy₂ this)
      apply Subgroup.mem_carrier.mp at hy₁
      apply Subgroup.mem_carrier.mpr
      exact (Subgroup.mul_mem_cancel_right H₁ hy₁).mp h₂
    · left
      simp only [not_not] at h₀
      exact h₀
  · intro h
    rcases h with h | h
    · use H₂
      exact Eq.symm (Set.union_eq_self_of_subset_left h)
    · use H₁
      exact Eq.symm (Set.union_eq_self_of_subset_right h)

variable (K : Type*) [Group K] (K₁ K₂ : Subgroup K)

example : (K₁.carrier ⊆ K₂.carrier) = (K₁ ≤ K₂) := rfl

example (x : K) : (x ∈ K₁) = (x ∈ K₁.carrier) := rfl

#check myThm K₁ K₂
#check mul_assoc
