import Mathlib.Tactic

section Refine

/-
syntax "refine"... [Lean.Parser.Tactic.refine]
  `refine e` behaves like `exact e`, except that named (`?x`) or unnamed (`?_`)
  holes in `e` that are not solved by unification with the main goal's target type
  are converted into new goals, using the hole's name, if any, as the goal case name.

syntax "refine'"... [Lean.Parser.Tactic.refine']
  `refine' e` behaves like `refine e`, except that unsolved placeholders (`_`)
  and implicit parameters are also converted into new goals.

syntax "refine_lift"... [Lean.Parser.Tactic.tacticRefine_lift_]
  Auxiliary macro for lifting have/suffices/let/...
  It makes sure the "continuation" `?_` is the main goal after refining.

syntax "refine_lift'"... [Lean.Parser.Tactic.tacticRefine_lift'_]
  Similar to `refine_lift`, but using `refine'`

-/
#help tactic refine

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

theorem two_le {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by sorry

theorem exists_prime_factor {n : Nat} (h : 2 ≤ n) : ∃ p : Nat, p.Prime ∧ p ∣ n := by sorry

-- exercise
lemma pred'_eq_sub_one (x : Fin n) : pred' x = x - 1 := by
  rw [pred']
  split_ifs with h
  · rfl
  · cases' n
    · simp
      sorry
    · sorry

example (x y : Fin n) : succ' x = y ↔ x = pred' y := by
  rw [succ'_eq_add_one, pred'_eq_sub_one]
  sorry

example (g : ¬ 1 < n) : n = 0 ∨ n = 1 := by
  sorry

example (S : Finset (Fin n)) (hS : S ≠ Finset.univ ∧ S.Nonempty) : Sᶜ.Nonempty := by
  sorry

noncomputable local instance : Fintype ({i : ℕ | i ≠ 0 ∧ Even i ∧ i < n}) := by
  apply Set.Finite.fintype
  apply Set.finite_iff_bddAbove.mpr
  sorry



variable {M : Type*}

def Submonoid.Setoid [CommMonoid M] (N : Submonoid M) : Setoid M  where
  r := fun x y ↦ ∃ w ∈ N, ∃ z ∈ N, x*w = y*z
  iseqv := {
    refl := fun x ↦ ⟨1, N.one_mem, 1, N.one_mem, rfl⟩
    symm := fun ⟨w, hw, z, hz, h⟩ ↦ ⟨z, hz, w, hw, h.symm⟩
    trans := by
      rintro a b c ⟨w, hw, z, hz, h⟩ ⟨w', hw', z', hz', h'⟩
      sorry
  }

open Set Filter
open Topology Filter
variable {X : Type*} [MetricSpace X] (a b c : X)

example {u : ℕ → X} (hu : Tendsto u atTop (𝓝 a)) {s : Set X} (hs : ∀ n, u n ∈ s) : a ∈ closure s := by
  rw [Metric.tendsto_atTop] at hu
  rw [Metric.mem_closure_iff]
  intro ε ε_pos
  rcases hu ε ε_pos with ⟨N, hN⟩
  sorry

theorem primes_infinite : ∀ n, ∃ p > n, Nat.Prime p := by
  intro n
  have : 2 ≤ Nat.factorial (n + 1) + 1 := by
    sorry
  rcases exists_prime_factor this with ⟨p, pp, pdvd⟩
  sorry

end Refine
