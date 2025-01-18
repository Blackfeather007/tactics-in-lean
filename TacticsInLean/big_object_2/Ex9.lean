import Mathlib.Tactic
import Mathlib

#check Subgroup
example {G : Type*} [Group G] (H₁ H₂ : Subgroup G) (h1: IsSubgroup ((H₁ ∪ H₂): Set G)): (∀ x ∈ H₁,x∈ H₂ ) ∨ (∀ x ∈ H₂,x∈ H₁):=by
  by_contra h
  push_neg at h
  rcases h.1 with ⟨a, ha⟩
  rcases h.2 with ⟨b, hb⟩
  have hbb: b∈ ((H₁ ∪ H₂): Set G):= Set.mem_union_right (↑H₁) hb.1
  have h2: b*a∈ ((H₁ ∪ H₂): Set G):=by
    exact (IsSubgroup.mul_mem_cancel_right h1 (Set.mem_union_left (↑H₂) ha.1)).mpr hbb
  rcases h2 with h3 | h3'
  · have h4: (b*a)*(a⁻¹) ∈ H₁:=by
      exact (Subgroup.mul_mem_cancel_right H₁ ((Subgroup.inv_mem_iff H₁).mpr ha.1)).mpr h3
    have h5: (b*a)*(a⁻¹) = b*(a*a⁻¹):=by
      exact mul_assoc b a a⁻¹
    rw[h5] at h4
    have h6: b∈ H₁:=by
      exact (Subgroup.mul_mem_cancel_right H₁ ha.1).mp h3
    exact hb.2 h6
  · have h4: (b⁻¹)*(b*a) ∈ H₂:=by
      exact (Subgroup.mul_mem_cancel_right H₂ h3').mpr ((Subgroup.inv_mem_iff H₂).mpr hb.1)
    have h5: b⁻¹*(b*a)=(b⁻¹*b)*a:=by
      exact Eq.symm (mul_assoc b⁻¹ b a)
    rw[h5] at h4
    have h6:a∈ H₂:=by
      exact (Subgroup.mul_mem_cancel_left H₂ hb.1).mp h3'
    exact ha.2 h6
