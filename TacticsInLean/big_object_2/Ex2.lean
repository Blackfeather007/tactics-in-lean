import Mathlib


theorem Contra_div_eq_iff_eq_mul_right {a b c : ℕ} (H : 0 < b) (H' : b ∣ a) :
    a ≠ b * c ↔ a / b ≠ c :=by
  apply Iff.intro
  {
    intro h
    intro h'
    have h'' := Nat.eq_mul_of_div_eq_right H' h'
    contradiction
  }
  {
    intro h
    intro h'
    have h'' := Nat.div_eq_of_eq_mul_right H h'
    contradiction
  }


theorem Contra_div_eq_iff_eq_mul_left {a b c : Nat} (H : 0 < b) (H' : b ∣ a) :
     a ≠ c * b  ↔ a / b ≠  c := by
  apply Iff.intro
  {
    intro h
    intro h'
    have h'':=Nat.eq_mul_of_div_eq_right H' h'
    rw[Nat.mul_comm] at h''
    contradiction

  }
  {
    intro h
    intro h'
    rw[mul_comm] at h'
    have h'' := Nat.div_eq_of_eq_mul_right H h'
    contradiction
  }
