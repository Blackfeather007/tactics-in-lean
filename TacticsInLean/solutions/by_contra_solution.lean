import Mathlib.Tactic

#help tactic by_contra

open Nat

example (h : ¬¬Q) : Q := by
  by_contra h'
  exact h h'

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a

example {n : ℕ} (hn : Even (n * n)) : Even n := by
  by_contra hc
  rw [← Nat.not_odd_iff_even] at hn
  apply hn
  rw [Nat.not_even_iff_odd] at hc
  apply odd_mul.2
  rw [and_self]
  exact hc

example {f : ℝ → ℝ} (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  intro a
  by_contra h'
  apply h
  use a
  intro x
  apply le_of_not_gt
  intro h''
  apply h'
  use x

example {a : ℕ} : Nat.gcd a (a + 1) = 1 := by
  by_contra hc
  have h' : Nat.gcd a (a + 1) ∣ (a + 1) - a := by
    apply Nat.dvd_sub
    linarith
    exact Nat.gcd_dvd_right a (a + 1)
    exact Nat.gcd_dvd_left a (a + 1)
  simp only [add_tsub_cancel_left, dvd_one] at h'
  exact hc h'

example (n : ℕ) (hn1 : Even n) (hn2 : Nat.Prime n) : n = 2 := by
  by_contra hc
  have h : ¬ Nat.Prime n := by
    apply (not_prime_iff_exists_dvd_ne ?_).mpr ?_
    exact Prime.two_le hn2
    use 2
    constructor
    · exact even_iff_two_dvd.mp hn1
    · constructor
      · omega
      · exact fun a => hc (id (Eq.symm a))
  exact h hn2

example (n : ℕ) (hn : 2 < n) (hpp : Nat.Prime n) : Odd n := by
  by_contra hc
  have heven : Even n := by exact not_odd_iff_even.mp hc
  have hnp : ¬ Nat.Prime n := by
    apply (Nat.not_prime_iff_exists_dvd_lt _).2
    use 2
    constructor
    · exact even_iff_two_dvd.mp heven
    · constructor
      · linarith
      · exact hn
    apply le_of_lt hn
  apply hnp hpp

example (n : ℕ) : ∃ p, n ≤ p ∧ Nat.Prime p := by
  let p := minFac (n ! + 1)
  have hpp : Nat.Prime p := by
    apply minFac_prime
    apply Nat.ne_of_gt
    apply succ_lt_succ
    apply factorial_pos _
  have hnp : n ≤ p := by
    by_contra hc
    push_neg at hc
    have h1 : p ∣ n ! := by
      simp only [p] at hc
      apply dvd_factorial (minFac_pos _)
      apply le_of_lt hc
    have h2 : p ∣ 1 := by
      apply (Nat.dvd_add_iff_right h1).2
      apply minFac_dvd _
    apply Nat.Prime.not_dvd_one hpp h2
  use p

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

example {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
    a = b := by
  by_contra abne
  have : |a - b| > 0 := by
    apply lt_of_le_of_ne
    · apply abs_nonneg
    intro h''
    apply abne
    apply eq_of_abs_sub_eq_zero h''.symm
  let ε := |a - b| / 2
  have εpos : ε > 0 := by
    change |a - b| / 2 > 0
    linarith
  rcases sa ε εpos with ⟨Na, hNa⟩
  rcases sb ε εpos with ⟨Nb, hNb⟩
  let N := max Na Nb
  have absa : |s N - a| < ε := by
    apply hNa
    apply le_max_left
  have absb : |s N - b| < ε := by
    apply hNb
    apply le_max_right
  have : |a - b| < |a - b|
  calc
    |a - b| = |(-(s N - a)) + (s N - b)| := by
      congr
      ring
    _ ≤ |(-(s N - a))| + |s N - b| := (abs_add _ _)
    _ = |s N - a| + |s N - b| := by rw [abs_neg]
    _ < ε + ε := (add_lt_add absa absb)
    _ = |a - b| := by norm_num [ε]
  exact lt_irrefl _ this
