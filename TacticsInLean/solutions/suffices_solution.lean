import Mathlib.Tactic


section Suffices

example (P Q R : Prop) (h₁ : P → R) (h₂ : Q) (h₃ : Q → P) : R := by
  suffices h : P from h₁ h
  exact h₃ h₂

example (n : ℕ) : 3 ∣ n ^ 3 + 3 * n ^ 2 + 2 * n := by
  suffices h : 3 ∣ n * (n + 1) * (n + 2) from by
    trans n * (n + 1) * (n + 2)
    assumption
    have : n * (n + 1) * (n + 2) = n ^ 3 + 3 * n ^ 2 + 2 * n := by ring
    rw [this]
  induction' n with n ih
  · norm_num
  have : Nat.Prime 3 := by decide
  apply this.dvd_mul.mp at ih
  rcases ih with ih | ih
  · apply this.dvd_mul.mp at ih
    rcases ih with ih | ih
    · trans (n + 1 + 2)
      exact Nat.dvd_add_self_right.mpr ih
      exact Nat.dvd_mul_left (n + 1 + 2) ((n + 1) * (n + 1 + 1))
    trans n + 1
    exact ih
    rw [mul_assoc]
    exact Nat.dvd_mul_right (n + 1) ((n + 1 + 1) * (n + 1 + 2))
  trans n + 2
  exact ih
  trans (n + 1) * (n + 1 + 1)
  exact Nat.dvd_mul_left (n + 2) (n + 1)
  exact Nat.dvd_mul_right ((n + 1) * (n + 1 + 1)) (n + 1 + 2)


example (n : ℕ) : Odd (n ^ 2 + n + 1) := by
  suffices h : Even (n ^ 2 + n) from by
    exact Even.add_one h
  apply Nat.even_add.mpr
  constructor
  · intro h
    by_contra h'
    simp at h'
    have : Odd (n ^ 2) := Odd.pow h'
    rw [Nat.not_odd_iff_even.symm] at h
    exact h this
  intro h
  apply Nat.even_pow.mpr
  simpa

example (n : ℕ) : 3 ∣ (n ^ 2 + 3 * n + 2) * (n ^ 2 + n) := by
  suffices h : 3 ∣ n * (n + 1) * (n + 2)  from by
    have :  (n ^ 2 + 3 * n + 2) * (n ^ 2 + n) = n * (n + 1) * (n + 2) * (n + 1) := by ring
    rw [this]
    exact Dvd.dvd.mul_right h (n + 1)
  induction' n with n ih
  · norm_num
  have : Nat.Prime 3 := by decide
  apply this.dvd_mul.mp at ih
  rcases ih with ih | ih
  · apply this.dvd_mul.mp at ih
    rcases ih with ih | ih
    · trans (n + 1 + 2)
      exact Nat.dvd_add_self_right.mpr ih
      exact Nat.dvd_mul_left (n + 1 + 2) ((n + 1) * (n + 1 + 1))
    trans n + 1
    exact ih
    rw [mul_assoc]
    exact Nat.dvd_mul_right (n + 1) ((n + 1 + 1) * (n + 1 + 2))
  trans n + 2
  exact ih
  trans (n + 1) * (n + 1 + 1)
  exact Nat.dvd_mul_left (n + 2) (n + 1)
  exact Nat.dvd_mul_right ((n + 1) * (n + 1 + 1)) (n + 1 + 2)

example (n : ℕ) : Even ((n ^ 3 + 97 * n ^ 2 + 38 * n + 8) * (n ^ 2 + n)) := by
  suffices h : Even (n ^ 2 + n) from by
    apply Even.mul_left h
  apply Nat.even_add.mpr
  constructor
  · intro h
    by_contra h'
    simp at h'
    have : Odd (n ^ 2) := Odd.pow h'
    rw [Nat.not_odd_iff_even.symm] at h
    exact h this
  intro h
  apply Nat.even_pow.mpr
  simpa

theorem List.Sorted.sublist_sorted {α : Type*} {r : α → α → Prop} [PartialOrder α]
  {l : List α} (h : List.Sorted r l) : ∀ l' ∈ l.sublists, List.Sorted r l' := by
    intro l' hl'
    rw [mem_sublists] at hl'
    match l with
    | [] =>
      rw [sublist_nil] at hl'
      rw [hl']
      exact h
    | a :: tail =>
      cases hl' with
      | cons _ hl' =>
        apply List.Sorted.tail at h
        dsimp at h
        exact h.sublist_sorted _ (mem_sublists.mpr hl')
      | cons₂ _ hl' =>
        rename List α => l''
        apply List.sorted_cons.mpr
        constructor
        · suffices htail : ∀ b ∈ tail, r a b from by
            intro b bl''
            exact htail b (hl'.mem bl'')
          exact (List.sorted_cons.mp h).1
        · apply List.Sorted.tail at h
          dsimp at h
          exact h.sublist_sorted _ (mem_sublists.mpr hl')

example {α : Type*} [LinearOrder α] (a b c d e : α) (h : a < b) :
  ¬List.Sorted (· < ·) [c, d, b, e, a] := by
  suffices h' : ¬List.Sorted (· < ·) [b, a] from by
    contrapose! h'
    apply h'.sublist_sorted
    simp
  simp
  exact le_of_lt h

example (s : Set ℕ) (h : {n | 3 ∣ n} ⊆ s) : ∃ x ∈ s, Even x := by
  suffices h' : ∃ x ∈ {n | 3 ∣ n}, Even x from by
    rcases h' with ⟨x, hx, x_even⟩
    use x
    exact ⟨h hx, x_even⟩
  use 6
  rw [Set.mem_setOf_eq]
  decide

example (m n : ℕ) (h : ¬m.Coprime n) (nezero : m ≠ 0 ∧ n ≠ 0) : m.primeFactors ∩ n.primeFactors ≠ ∅ := by
  suffices h' : ∃ p, p.Prime ∧ p ∣ n ∧ p ∣ m from by
    rcases h' with ⟨p, hp₁, hp₂, hp₃⟩
    rw [Finset.nonempty_iff_ne_empty.symm, Finset.Nonempty]
    use p
    simp [hp₁, hp₂, hp₃, nezero]
  use (m.gcd n).minFac
  rw [Nat.Coprime] at h
  constructor
  · exact Nat.minFac_prime h
  constructor
  · trans (m.gcd n)
    exact Nat.minFac_dvd (m.gcd n)
    exact Nat.gcd_dvd_right m n
  · trans (m.gcd n)
    exact Nat.minFac_dvd (m.gcd n)
    exact Nat.gcd_dvd_left m n

end Suffices
