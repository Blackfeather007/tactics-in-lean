/-
前方屎山预警
前方屎山预警
前方屎山预警
前方屎山预警
前方屎山预警
前方屎山预警
前方屎山预警
前方屎山预警
前方屎山预警
前方屎山预警
前方屎山预警
前方屎山预警
前方屎山预警
前方屎山预警
前方屎山预警
前方屎山预警
前方屎山预警
前方屎山预警
前方屎山预警
前方屎山预警
前方屎山预警
前方屎山预警
前方屎山预警
前方屎山预警
前方屎山预警
前方屎山预警
前方屎山预警
前方屎山预警
前方屎山预警
前方屎山预警
前方屎山预警
前方屎山预警
前方屎山预警
前方屎山预警
-/

import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Ideal.Prime

private lemma lem1 {R : Type*} [CommRing R] [DecidableEq (Ideal R)] (S : Finset (Ideal R)) (hS : S.Nonempty) (hpi : ∀ P ∈ S, P.IsPrime) (hnc : { x : Ideal R // x ∈ S } → R) (v : Ideal R) (hv: v ∈ S) (hv' : (hnc ⟨v,hv⟩) ∈ v): (∏x ∈ S.attach, (hnc x) ∈ v) := by
  generalize S.attach = Sa
  induction' hS using Finset.Nonempty.cons_induction with h₀ h₁ h₂ h₃ h₄ h₅
  · rw [Finset.mem_singleton.1 hv]
    have t₁ : Sa = {⟨h₀,Finset.mem_singleton_self h₀⟩} := by
      sorry
    rw [t₁] at *
    rw [Finset.prod_singleton hnc ⟨h₀,Finset.mem_singleton_self h₀⟩]
    have t₂ : hnc ⟨h₀,Finset.mem_singleton_self h₀⟩ = hnc ⟨v,hv⟩ := by
      congr
      rw [Finset.mem_singleton.1 hv]
    rw [t₂]
    apply ((Ideal.ext_iff.1 (Finset.mem_singleton.1 hv)) (hnc ⟨v,hv⟩)).1 hv'
  · sorry

private lemma lem2 {R : Type*} [CommRing R] [DecidableEq (Ideal R)] (S : Finset (Ideal R)) (hnc : { x : Ideal R // x ∈ S } → R) (v : Ideal R) (hv: v.IsPrime) (hpd : ∏ x ∈ S.attach, (hnc x) ∈ v) : ∃ x ∈ S.attach, (hnc x) ∈ v := by
  induction S using Finset.induction with
  | empty =>
    simp at *
    revert hpd
    show 1 ∉ v
    refine (Ideal.ne_top_iff_one v).mp ?_
    exact Ideal.IsPrime.ne_top hv
  | @insert a s n_mem hp =>
    have aux₁ (x : {x // x ∈ s}) : x.val ∈ insert a s := by
      rw [Finset.mem_insert]
      exact Or.inr x.property

    have aux₂ : a ∈ insert a s := by
      rw [Finset.mem_insert]
      exact Or.inl rfl

    set hnc' : {x // x ∈ s} → R := fun x =>
      hnc ⟨x.val, aux₁ _⟩ with hnc'_def
    set coe : {x // x ∈ s} → {x // x ∈ insert a s} := fun x =>
      ⟨x.val, aux₁ _⟩ with coe_def

    have aux₃ : ∏ x ∈ s.attach, hnc' x = ∏ x ∈ Finset.image coe s.attach, hnc x := by
      refine Finset.prod_bij ?_ ?_ ?_ ?_ ?_
      · exact (fun x _ => ⟨x.val, aux₁ _⟩)
      · exact fun x mem => by
          rw [Finset.mem_image]
          exists x
      · exact fun x₁ _ x₂ _ map_eq => by
          rw [← Subtype.val_inj] at map_eq ⊢
          exact map_eq
      · exact fun y mem => by
          rw [Finset.mem_image] at mem
          rcases mem with ⟨x, mem, map_eq⟩
          exists x, mem
      · exact fun x _ => by
          rw [hnc'_def]

    rw [Finset.attach_insert, Finset.prod_insert] at hpd
    · conv at hpd =>
        enter [2, 2]
        rw [← aux₃]
      by_cases mem_v : ∏ x ∈ s.attach, hnc' x ∈ v
      · replace hp := hp hnc' mem_v
        rcases hp with ⟨x, _, mem₂⟩
        exists ⟨x, aux₁ _⟩
        constructor
        · exact Finset.mem_attach _ _
        · rw [hnc'_def] at mem₂
          exact mem₂
      · rw [Ideal.IsPrime.mul_mem_iff_mem_or_mem hv] at hpd
        replace mem_v := Or.resolve_right hpd mem_v
        exists ⟨a, aux₂⟩
        constructor
        · exact Finset.mem_attach _ _
        · exact mem_v
    · exact fun mem => by
        rw [Finset.mem_image] at mem
        rcases mem with ⟨x, _, eq⟩
        rw [← Subtype.val_inj] at eq
        change x.val = a at eq
        exact n_mem (eq ▸ x.property)


private lemma prime_avoidance_core {R : Type*} [CommRing R] [DecidableEq (Ideal R)] (S : Finset (Ideal R)) (I: Ideal R) ( n : ℕ ) (hne : S.card = n + 1) (hpi : ∀ P ∈ S, P.IsPrime) (hnc : ∀ P ∈ S, ¬ ((I: Set R) ⊆ P)) : (∃ x ∈ I, ∀ P ∈  S, x ∉ P) := by
    induction n
    case zero =>
      simp at *
      rw [Finset.card_eq_one] at hne
      rcases hne with ⟨Q, hQ⟩
      have hQ' : Q ∈ S := by
        rw [hQ] ; exact Finset.mem_singleton_self Q
      rcases Set.not_subset.1 (hnc Q hQ') with ⟨x, hx, hnx⟩
      use x
      constructor
      · exact hx
      · intro P hP
        rw [hQ] at hP ; rw [Finset.mem_singleton.1 hP]
        exact hnx
    case succ _ k _ =>
      have c : ∀ P ∈ S, ∃ xₚ ∈ I, ∀ Q ∈ S.erase P, xₚ ∉ Q := by
        intro P hP
        have hneₖ : (S.erase P).card = k + 1 := by
          rw [Finset.card_erase_of_mem hP,hne]
          simp
        have hpiₖ : ∀ Q ∈ S.erase P, Q.IsPrime := by
          intro Q hQ
          exact hpi Q (Finset.mem_erase.1 hQ).2
        have hncₖ : ∀ Q ∈ S.erase P, ¬ ((I: Set R) ⊆ Q) := by
          intro Q hQ
          exact hnc Q (Finset.mem_erase.1 hQ).2
        rcases prime_avoidance_core (S.erase P) I k hneₖ (hpiₖ) hncₖ with ⟨xₚ, hxₚ, hₚ⟩
        use xₚ
      let f : {x : Ideal R // x ∈ S} → R := fun ⟨a,ha⟩ => Classical.choose (c a ha)
      by_cases h : ∀ a : {x : Ideal R // x ∈ S}, f a ∈ a.val
      · have hne' : S.Nonempty := by
          apply Finset.one_le_card.1 ; rw [hne] ; simp
        rcases hne' with ⟨P, hP⟩
        let prod_f : R := ∏ N ∈ (S.erase P).attach, (f ⟨N.val, Finset.mem_of_mem_erase N.property⟩)
        let zᵣ : R := f ⟨P, hP⟩
        use prod_f + zᵣ
        have shit : (S.erase P).Nonempty := by
                apply Finset.one_le_card.1
                rw [← Finset.card_erase_add_one hP] at hne
                simp at hne ; rw [hne] ; simp
        constructor
        · apply Ideal.add_mem
          · apply Finset.prod_induction_nonempty
            · intro _ _ b _
              apply Ideal.mul_mem_right ; exact b
            · exact Finset.Nonempty.attach shit
            · intro N _
              exact (Classical.choose_spec (c N.val (Finset.mem_of_mem_erase N.property))).1
          · exact (Classical.choose_spec (c P hP)).left
        · by_contra fi ; push_neg at fi
          rcases fi with ⟨v,hv⟩
          by_cases hj : v = P
          · rw [hj] at hv
            rcases lem2 (S.erase P) (fun x => f ⟨x.val, Finset.mem_of_mem_erase x.property⟩) P (hpi P hv.1) ((Ideal.add_mem_iff_left P (h ⟨P,hP⟩)).1 hv.2) with ⟨z,⟨_,hz2⟩⟩
            have t₅ : P ∈ S.erase z.val := by
              apply Finset.mem_erase_of_ne_of_mem
              apply Ne.symm
              apply Finset.ne_of_mem_erase
              · exact Finset.coe_mem z
              · exact hP
            apply (Classical.choose_spec (c z.val (Finset.mem_of_mem_erase z.property))).2 P t₅
            exact hz2
          · have t: prod_f ∈ v := by
              have u₃ : ∀ Y ∈ (S.erase P), Y.IsPrime := by
                intro Y hY
                apply Finset.erase_subset at hY; exact hpi Y hY
              apply lem1 (S.erase P) shit u₃ (fun x => f ⟨x.val, Finset.mem_of_mem_erase x.property⟩) v (Finset.mem_erase_of_ne_of_mem hj hv.1) (h ⟨v,hv.1⟩)
            apply (Classical.choose_spec (c P hP)).right v (Finset.mem_erase.2 ⟨hj,hv.1⟩)
            exact (Ideal.add_mem_iff_right v t).1 hv.2
      · push_neg at h ; rcases h with ⟨a, ha⟩
        use (f a)
        constructor
        · apply(Classical.choose_spec (c a a.2)).1
        · intro P hP
          by_cases hP' : P = a.1
          · rw [hP']; exact ha
          · have hP'' : P ∈ S.erase a.1 := by
              rw [Finset.mem_erase] ; exact ⟨hP',hP⟩
            exact (Classical.choose_spec (c a a.2)).2 P hP''

theorem prime_avoidance {R : Type*} [CommRing R] [DecidableEq (Ideal R)] (S : Finset (Ideal R)) (I: Ideal R) (hne : S.Nonempty) (hpi : ∀ P ∈ S, P.IsPrime) (hnc : ∀ P ∈ S, ¬ (I <= P)) : (∃ x ∈ I, ∀ P ∈ S, x ∉ P) := by
    apply Finset.card_ne_zero.2 at hne
    generalize hS : S.card = n
    induction n
    case zero => contradiction
    case succ _ k _ =>
      exact prime_avoidance_core S I k hS hpi hnc



