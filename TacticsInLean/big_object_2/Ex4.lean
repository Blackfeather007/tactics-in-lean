import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Homeomorph
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Sets.Compacts
import Mathlib.Tactic
import Mathlib.Logic.Equiv.Defs

-- 习题7.1
-- 证明紧空间到 T2 空间的连续双射是同胚

variable (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace X] [T2Space Y]

theorem Myhomeomorphism (f : X → Y) (conf : Continuous f) (bijf : Function.Bijective f): IsOpenMap f:= by
-- Prove IsopenMap is equal to IsclosedMap when f is bijection
  have open_to_close : (∀ (U : Set X), IsClosed U → IsClosed (f '' U)) → IsOpenMap f := by
    intro closemap U uopen
    let V := Uᶜ
    have closeV  : IsClosed V := isClosed_compl_iff.mpr uopen
    have fvclose : IsClosed (f '' V) := closemap V closeV
    let fU := (f '' V)ᶜ
    have openfu : IsOpen (fU) :=IsClosed.isOpen_compl
    have t1 : fU = (f '' V)ᶜ  := by rfl
    have t2 : V = Uᶜ          := by rfl
    have equal : fU = f '' U := by
      rw [t1, t2]
      have sym : f '' Uᶜ = (f '' U)ᶜ → (f '' Uᶜ)ᶜ = f '' U := by
        let A := f '' Uᶜ
        let B := f '' U
        have t1 : A = f '' Uᶜ := by rfl
        have t2 : B = f '' U  := by rfl
        rw [← t1, ← t2]
        nth_rw 1 [← compl_compl A]
        exact compl_inj_iff.1
      apply sym
      exact Set.image_compl_eq bijf
    rw [← equal]
    exact openfu
  apply open_to_close
-- Prove any closed set is compact in X since X is compact
  intro U
  have close_is_compact : ∀ (U : Set X),  IsClosed U → IsCompact U:= fun _ hU ↦ IsClosed.isCompact hU
-- Prove continuous mapping transmits compact sets

-- Any compact set is closed in Hausdorff space
  exact fun a => IsCompact.isClosed ((fun U a => IsCompact.image a conf) U (close_is_compact U a))



noncomputable def LI_Hao_homeomorphism (f : X → Y) (conf : Continuous f) (bijf : Function.Bijective f) (Openf : IsOpenMap f): X ≃ₜ Y :=
{
    toEquiv := Equiv.ofBijective f bijf,
    continuous_toFun := conf,
    continuous_invFun := by
        let g := (Equiv.ofBijective f bijf).invFun
        have gc : Continuous g → Continuous (Equiv.ofBijective f bijf).invFun := by
          intro gcc
          exact gcc
        apply gc
        refine { isOpen_preimage := ?isOpen_preimage }
        intro U hU
        have _ : f = (Equiv.ofBijective f bijf).toFun := by rfl
        have hf1 : f ∘ g = id := by
          calc
            f ∘ g = f ∘ (Equiv.ofBijective f bijf).invFun := by rfl
            _ = (Equiv.ofBijective f bijf).toFun ∘ (Equiv.ofBijective f bijf).invFun := by rfl
            _ = id := by simp
        have hf1' : f ∘ g = id → Function.LeftInverse f g := by exact fun _ => congrFun hf1
        have hf2 : g ∘ f = id := by
          calc
            g ∘ f = g ∘ (Equiv.ofBijective f bijf).toFun := by rfl
            _ = (Equiv.ofBijective f bijf).invFun ∘ (Equiv.ofBijective f bijf).toFun := by rfl
            _ = id := by simp
        have hf2' : g ∘ f = id → Function.RightInverse f g := by exact fun _ => congrFun hf2
        apply hf1' at hf1
        apply hf2' at hf2
        have hf : (Function.LeftInverse f g) ∧ (Function.RightInverse f g) := by
          exact ⟨hf1, hf2⟩
        let preimage := (Equiv.ofBijective f bijf).invFun ⁻¹' U
        have h : preimage = f '' U := by
          dsimp [preimage]
          have h1 : (Equiv.ofBijective f bijf).invFun ⁻¹' U ⊆ f '' U := by
            apply Set.preimage_subset_image_of_inverse hf.1
          have h2 : f '' U ⊆ (Equiv.ofBijective f bijf).invFun ⁻¹' U := by
            apply Set.image_subset_preimage_of_inverse hf.2
          apply Set.eq_of_subset_of_subset h1 h2
        have open_preimage : IsOpen preimage := by
          rw [h]
          apply Openf
          exact hU
        exact open_preimage
}



noncomputable def CHEN_Gaoyi_homeomorphism (f : X → Y) (conf : Continuous f) (bijf : Function.Bijective f) (Openf : IsOpenMap f): X ≃ₜ Y :=
{
    toEquiv := Equiv.ofBijective f bijf,
    continuous_toFun := conf,
    continuous_invFun := by
      refine { isOpen_preimage := ?isOpen_preimage }
      have left_inverse : (Equiv.ofBijective f bijf).toFun ∘ (Equiv.ofBijective f bijf).invFun = id := by
        simp only [Equiv.toFun_as_coe,
        Equiv.invFun_as_coe, Equiv.self_comp_symm]
      have right_inverse : (Equiv.ofBijective f bijf).invFun ∘ (Equiv.ofBijective f bijf).toFun = id := by
        simp only [Equiv.invFun_as_coe,
        Equiv.toFun_as_coe, Equiv.symm_comp_self]
      intro U Uopen
      have lefinv : Function.LeftInverse (Equiv.ofBijective f bijf).invFun (Equiv.ofBijective f bijf).toFun := by
        exact congrFun right_inverse
      have riginv : Function.RightInverse (Equiv.ofBijective f bijf).invFun (Equiv.ofBijective f bijf).toFun := by
        exact congrFun left_inverse
      have exa : (Equiv.ofBijective f bijf).invFun '' ((Equiv.ofBijective f bijf).toFun '' U) = (Equiv.ofBijective f bijf).invFun ∘ (Equiv.ofBijective f bijf).toFun '' U := by
        exact
          Eq.symm
            (Set.image_comp (Equiv.ofBijective f bijf).invFun (Equiv.ofBijective f bijf).toFun U)
      have bijecg : Function.Bijective (Equiv.ofBijective f bijf).invFun := by
        apply Function.bijective_iff_has_inverse.2
        use (Equiv.ofBijective f bijf).toFun
        refine ⟨riginv, lefinv⟩
      have inverse_inverse_eq : (Equiv.ofBijective f bijf).invFun ⁻¹' U =  (Equiv.ofBijective f bijf).toFun '' U := by
        refine (Set.preimage_eq_iff_eq_image ?hf).mpr ?_
        · exact bijecg
        · symm
          rw [exa, right_inverse]
          exact Set.image_id U
      rw [inverse_inverse_eq]
      exact Openf U Uopen
}
