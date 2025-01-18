import Mathlib.Tactic

universe u v

variables (𝕜 : Type*) [Field 𝕜] (V : Type*) [AddCommGroup V] [Module 𝕜 V]
variable (p q: V →ₗ[𝕜] V)

#check IsCompl
theorem xiti_1 (hp : ∀ v : V, p (p v) = p v) :
    (∀ v ∈ LinearMap.ker p, ∀ w ∈ LinearMap.range p, v + w = 0 → v = 0 ∧ w = 0)
    ∧ (∀ v : V, ∃ u ∈ LinearMap.ker p, ∃ w ∈ LinearMap.range p, v = u + w) := by
  constructor /- 用calc 应该会很好但是不会用-/
  . intro v hv
    intro w hw
    have hw2 : ∃ v0, p v0 = w := by
      exact hw
    rcases hw2 with ⟨ v0,hw2' ⟩
    intro h3
    rw[← hw2'] at h3
    have h3' : p (v + p v0) = p 0 :=by
      exact congrArg (⇑p) h3
    have h3'' : p (v) + p (p v0) =p (v + p v0) := by
      exact Eq.symm (LinearMap.map_add p v (p v0))
    rw[← h3''] at h3'
    have h3''' : p (v) + p (p v0) = p (v) + p (v0) :=by
      exact congrArg (HAdd.hAdd (p v)) (hp v0)
    rw[h3'''] at h3'
    have h4 : p (v + v0) = p (v) + p (v0) :=by
      exact LinearMap.map_add p v v0
    rw[← h4] at h3'
    have h4' : p 0 = 0 := by
      exact LinearMap.map_zero p
    rw[h4'] at h3'
    have h5 : v + v0 ∈ LinearMap.ker p := by
      exact h3'
    have h5' : v0 ∈ LinearMap.ker p := by
      exact (Submodule.add_mem_iff_right (LinearMap.ker p) hv).mp h3'
    constructor
    . have h5'' : p v0 =0 := by
        exact h5'
      rw[h5''] at h3
      rw[add_zero] at h3
      exact h3
    . rw[← hw2']
      exact h5'
  . intro v /-不知道怎么实现-/

    sorry
theorem xiti_2 (hp : ∀ v : V , p (q v) = q (p v)) :
(∀ v ∈ LinearMap.ker p , q v ∈ LinearMap.ker p )∧
(∀ v ∈ LinearMap.range p, q v ∈ LinearMap.range p ):= by
  constructor
  . intro v2
    intro h
    simp only [LinearMap.mem_ker]
    have h2 : p (q v2) = q (p v2) :=by
      exact hp v2
    have h3 : q (p v2) = 0 :=by
      rw [h]
      exact LinearMap.map_zero q
    have h5 : p (q v2) = 0 :=by
      rw [h2]
      rw [h3]
    exact h5
  . intro v2 h
    have h2 : ∃ v0 : V, p v0 = v2 := by
      exact h
    rcases h2 with ⟨v0, hv0⟩
    rw [← hv0]
    rw [← hp v0]
    exact LinearMap.mem_range_self p (q v0)
