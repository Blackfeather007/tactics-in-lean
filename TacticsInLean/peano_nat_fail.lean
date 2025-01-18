import Mathlib.Tactic

class NatLike (α : Type*) where
  zero : α
  succ : α → α
  eq_iff_succ_eq : ∀ b c : α, b = c ↔ succ b = succ c
  zero_ne_succ : ∀ a : α, zero ≠ succ a
  rename_induction' : ∀ p : α → Prop, p zero → (∀ a : α, p a → p (succ a)) → (∀ a : α, p a)
instance : NatLike Nat where
  zero := Nat.zero
  succ := Nat.succ
  eq_iff_succ_eq _ _ := Nat.succ_inj'.symm
  zero_ne_succ := Nat.zero_ne_add_one
  rename_induction' _ hp hp' a := Nat.recAux hp (fun d hd => hp' d hd) a
variable {α : Type*} [NatLike α]
namespace NatLike

theorem zero_or_succ_of_some : ∀ a : α, a = zero ∨ (∃ b : α, a = succ b) := by
  intro a
  by_cases h : a = zero
  · exact Or.inl h
  · simp [h]
    let p : α → Prop := fun n => (n ≠ zero → (∃ m : α, n = succ m))
    have hp_zero : p zero := by
      unfold p
      simp
    have hp_forall : ∀ a : α , p a → p (succ a) := fun a ha => (by unfold p at *; simp)
    exact rename_induction' p hp_zero hp_forall a h


inductive le (n : α) : α → Prop where
  | refl : NatLike.le n n
  | step m : NatLike.le n m → NatLike.le n (succ m)

theorem succ_le (m n : α) : NatLike.le (succ m) n → NatLike.le m n := by
  intro h
  induction h with
  | refl =>
    refine le.step m le.refl
  | step m _ hq₂ =>
    exact le.step m hq₂


#check Nat.le

lemma zero_le : ∀ n : α , le zero n := rename_induction' (fun n => (le zero n)) le.refl (fun _ ha => le.step _ ha)

lemma ne_le_zero : ∀ n : α , n ≠ zero → ¬ le n zero := rename_induction' (fun n => n ≠ zero → (¬ le n zero)) (by simp) (by
  intro a ha
  simp [(zero_ne_succ a).symm]
  
  sorry)

theorem not_succ_le_zero : ∀ n : α , ¬ (le (succ n) zero) := rename_induction' (fun n => (¬ (le (succ n) zero))) (by
  dsimp

  sorry) (by sorry)

theorem not_succ_le_self (n : α) : ¬NatLike.le (succ n) n := by
  intro h
  rcases zero_or_succ_of_some n with ⟨hn_zero | ⟨b, hb⟩⟩
  · sorry
  · sorry

theorem not_le_iff (m n : α) : ¬NatLike.le m n ↔ NatLike.le (succ n) m := by
  sorry

end NatLike




instance {α : Type*} [NatLike α] : LinearOrder α where
  le := NatLike.le
  le_refl := fun _ => NatLike.le.refl
  le_trans a b c aleb blec:= by
    induction aleb with
    | refl => exact blec
    | step m h ih => exact ih (NatLike.succ_le m c blec)
  le_antisymm a b hab hba := by
    induction hab with
    | refl => rfl
    | step _ _ =>
      sorry
  le_total := sorry
  decidableLE := sorry
