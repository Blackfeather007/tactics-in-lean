import Mathlib.Tactic

#check inv_mul_self
#print Group



/-(x y : G) (hex : x ∈ H₁ ∧ ¬(x ∈ H₂)) (hey : ¬(y ∈ H₁) ∧ y ∈ H₂)-/
example {G : Type*} [inst : Group G] (H₁ H₂ : Subgroup G)(h : ∀ (x y : G), x ∈ H₁ ∨ x ∈ H₂ →  y ∈ H₁ ∨ y ∈ H₂ → x⁻¹ * y ∈ H₁ ∨ x⁻¹ * y ∈ H₂):(∀ x : G, x ∈ H₁ → x ∈ H₂) ∨ (∀ x : G, x ∈ H₂ → x ∈ H₁)
    := by
    by_contra! this
    obtain ⟨⟨u,⟨hu,hpu⟩⟩, ⟨v,⟨hv,hpv⟩⟩⟩ := this
    let m := h u v (Or.inl hu) (Or.inr hv)
    obtain (hiuvmh2 | hiuvmh1) := m
    · suffices hvmh1 : v ∈ H₁ from by
        exact hpv hvmh1
      rw [← one_mul v, ← mul_inv_cancel u, mul_assoc]
      exact H₁.mul_mem hu hiuvmh2
    · suffices hvmh2 : u⁻¹ ∈ H₂ from by
        apply hpu ?_
        rw [← inv_inv u]
        exact H₂.inv_mem hvmh2
      rw [← mul_one u⁻¹, ← mul_inv_cancel v, ← mul_assoc]
      apply H₂.mul_mem hiuvmh1 ?_
      exact H₂.inv_mem' hv





example {G : Type*} [inst : Group G] (H₁ H₂ : Subgroup G) :
    (∀ (x y : G), x ∈ H₁ ∨ x ∈ H₂ →  y ∈ H₁ ∨ y ∈ H₂ → x⁻¹ * y ∈ H₁ ∨ x⁻¹ * y ∈ H₂) →
    (∀ x : G, x ∈ H₁ → x ∈ H₂) ∨ (∀ x : G, x ∈ H₂ → x ∈ H₁)
    := fun h => by
    by_contra! this
    obtain ⟨⟨u,⟨hu,hpu⟩⟩, ⟨v,⟨hv,hpv⟩⟩⟩ := this
    exact Or.elim (h u v (Or.inl hu) (Or.inr hv))
      ( fun hiuvmh2 =>
        have h'' : u * (u⁻¹ * v) ∈ H₁ := H₁.mul_mem hu hiuvmh2
        show False from hpv ((one_mul v) ▸ (mul_inv_cancel u) ▸ (mul_assoc u u⁻¹ v).symm ▸ h''))
      ( fun hiuvmh1 =>
        have hvmh2 : u⁻¹ ∈ H₂ := ((mul_one u⁻¹) ▸ (mul_inv_cancel v) ▸ (mul_assoc u⁻¹ v v⁻¹) ▸ (H₂.mul_mem hiuvmh1 (H₂.inv_mem' hv)))
        show False from hpu ((Group.toDivisionMonoid.proof_1 u) ▸ (H₂.inv_mem hvmh2)))
