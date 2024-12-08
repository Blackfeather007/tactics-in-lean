import Mathlib.Tactic


section Suffices

/-
syntax "suffices"... [Lean.Parser.Tactic.tacticSuffices_]
  Given a main goal `ctx ⊢ t`, `suffices h : t' from e` replaces the main goal with `ctx ⊢ t'`,
  `e` must have type `t` in the context `ctx, h : t'`.

  The variant `suffices h : t' by tac` is a shorthand for `suffices h : t' from by tac`.
  If `h :` is omitted, the name `this` is used.  syntax "suffices"... [Mathlib.Tactic.tacticSuffices_]
-/
#help tactic suffices

-- Exercise

example (P Q R : Prop) (h₁ : P → R) (h₂ : Q) (h₃ : Q → P) : R := by
  sorry

example (n : ℕ) : 3 ∣ n ^ 3 + 3 * n ^ 2 + 2 * n := by
  sorry


example (n : ℕ) : Odd (n ^ 2 + n + 1) := by
  sorry

example (n : ℕ) : 3 ∣ (n ^ 2 + 3 * n + 2) * (n ^ 2 + n) := by
  sorry

example (n : ℕ) : Even ((n ^ 3 + 97 * n ^ 2 + 38 * n + 8) * (n ^ 2 + n)) := by
  sorry

-- You don't have to prove it.
theorem List.Sorted.sublist_sorted {α : Type*} {r : α → α → Prop} [PartialOrder α]
  {l : List α} (h : List.Sorted r l) : ∀ l' ∈ l.sublists, List.Sorted r l' := by
    sorry

example {α : Type*} [LinearOrder α] (a b c d e : α) (h : a < b) :
  ¬List.Sorted (· < ·) [c, d, b, e, a] := by
  sorry

example (s : Set ℕ) (h : {n | 3 ∣ n} ⊆ s) : ∃ x ∈ s, Even x := by
  sorry

example (m n : ℕ) (h : ¬m.Coprime n) (nezero : m ≠ 0 ∧ n ≠ 0) : m.primeFactors ∩ n.primeFactors ≠ ∅ := by
  sorry

end Suffices
