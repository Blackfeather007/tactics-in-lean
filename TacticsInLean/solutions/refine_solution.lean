import Mathlib.Tactic

section Refine

variable {n : ℕ} [NeZero n]

/-- Successor deFined for `Fin n`. -/
def succ' (i : Fin n) := ite (i < n - 1) (i + 1 : Fin n) 0

/-- Predecessor deFined for `Fin n`. -/
def pred' (i : Fin n) := ite (0 < i) (i - 1 : Fin n) (n - 1)

/-- Neighborhood for a point `i`. -/
def nbr (i : Fin n) : Finset (Fin n) := {i, succ' i, pred' i}

/-- Neighbors of a point `i`. -/
def nbrs (i : Fin n) : Finset (Fin n) := {succ' i, pred' i}

/-- Interior of a set. -/
def int' (S : Finset (Fin n)) : Finset (Fin n) := Set.toFinset ({i | nbrs i ⊆ S})

/-- Boundary of a set. -/
def bdry (S : Finset (Fin n)) := S \ (int' (S))

-- not need to prove
lemma succ'_eq_add_one (x : Fin n) : succ' x = x + 1 := by sorry

-- exercise
lemma pred'_eq_sub_one (x : Fin n) : pred' x = x - 1 := by
  rw [pred']
  split_ifs with h
  · rfl
  · cases' n
    · simp
      refine neg_eq_of_add_eq_zero_left ?_
      ring_nf
      exact Subsingleton.eq_zero x
    · refine sub_left_inj.mpr ?_
      simp only [CharP.cast_eq_zero]
      push_neg at h
      apply Eq.symm
      exact Fin.le_zero_iff.mp h

example (x y : Fin n) : succ' x = y ↔ x = pred' y := by
  rw [succ'_eq_add_one, pred'_eq_sub_one]
  refine' ⟨λ h => _, λ h => _⟩
  · rw [← h]
    simp only [add_sub_cancel_right]
  · rw [h]
    simp only [sub_add_cancel]

example (g : ¬ 1 < n) : n = 0 ∨ n = 1 := by
  refine Nat.le_one_iff_eq_zero_or_eq_one.mp ?_
  exact Nat.not_lt.mp g

example (S : Finset (Fin n)) (hS : S ≠ Finset.univ ∧ S.Nonempty) : Sᶜ.Nonempty := by
  refine (Finset.compl_ne_univ_iff_nonempty Sᶜ).mp ?_
  simp
  exact hS.1

noncomputable local instance : Fintype ({i : ℕ | i ≠ 0 ∧ Even i ∧ i < n}) := by
  apply Set.Finite.fintype
  apply Set.finite_iff_bddAbove.mpr
  refine' ⟨n, _⟩
  rw [mem_upperBounds]
  simp
  intros x _ _ h3
  apply le_of_lt h3



variable {M : Type*}

def Submonoid.Setoid [CommMonoid M] (N : Submonoid M) : Setoid M  where
  r := fun x y ↦ ∃ w ∈ N, ∃ z ∈ N, x*w = y*z
  iseqv := {
    refl := fun x ↦ ⟨1, N.one_mem, 1, N.one_mem, rfl⟩
    symm := fun ⟨w, hw, z, hz, h⟩ ↦ ⟨z, hz, w, hw, h.symm⟩
    trans := by
      rintro a b c ⟨w, hw, z, hz, h⟩ ⟨w', hw', z', hz', h'⟩
      refine ⟨w*w', N.mul_mem hw hw', z*z', N.mul_mem hz hz', ?_⟩
      rw [← mul_assoc, h, mul_comm b, mul_assoc, h', ← mul_assoc, mul_comm z, mul_assoc]
  }

open Set Filter
open Topology Filter

variable {X : Type*} [MetricSpace X] (a b c : X)

example {u : ℕ → X} (hu : Tendsto u atTop (𝓝 a)) {s : Set X} (hs : ∀ n, u n ∈ s) : a ∈ closure s := by
  rw [Metric.tendsto_atTop] at hu
  rw [Metric.mem_closure_iff]
  intro ε ε_pos
  rcases hu ε ε_pos with ⟨N, hN⟩
  refine ⟨u N, hs _, ?_⟩
  rw [dist_comm]
  exact hN N le_rfl

theorem two_le {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  cases m; contradiction
  case succ m =>
    cases m; contradiction
    repeat apply Nat.succ_le_succ
    apply zero_le

theorem exists_prime_factor {n : Nat} (h : 2 ≤ n) : ∃ p : Nat, p.Prime ∧ p ∣ n := by
  by_cases np : n.Prime
  · use n, np
  induction' n using Nat.strong_induction_on with n ih
  rw [Nat.prime_def_lt] at np
  push_neg at np
  rcases np h with ⟨m, mltn, mdvdn, mne1⟩
  have : m ≠ 0 := by
    intro mz
    rw [mz, zero_dvd_iff] at mdvdn
    linarith
  have mgt2 : 2 ≤ m := two_le this mne1
  by_cases mp : m.Prime
  · use m, mp
  · rcases ih m mltn mgt2 mp with ⟨p, pp, pdvd⟩
    use p, pp
    apply pdvd.trans mdvdn

theorem primes_infinite : ∀ n, ∃ p > n, Nat.Prime p := by
  intro n
  have : 2 ≤ Nat.factorial (n + 1) + 1 := by
    sorry
  rcases exists_prime_factor this with ⟨p, pp, pdvd⟩
  refine ⟨p, ?_, pp⟩
  show p > n
  by_contra ple
  push_neg  at ple
  have : p ∣ Nat.factorial (n + 1) := by
    sorry
  have : p ∣ 1 := by
    sorry
  show False
  sorry


end Refine
