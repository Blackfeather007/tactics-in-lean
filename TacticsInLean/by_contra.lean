import Mathlib.Tactic

#help tactic by_contra

open Nat

example (h : ¬¬Q) : Q := by sorry

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a

example {n : ℕ} (hn : Even (n * n)) : Even n := by sorry

example {f : ℝ → ℝ} (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by sorry

example {a : ℕ} : Nat.gcd a (a + 1) = 1 := by sorry

example (n : ℕ) (hn1 : Even n) (hn2 : Nat.Prime n) : n = 2 := by sorry

example (n : ℕ) (hn : 2 < n) (hpp : Nat.Prime n) : Odd n := by sorry

example (n : ℕ) : ∃ p, n ≤ p ∧ Nat.Prime p := by sorry

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

example {s : ℕ → ℝ} {a b : ℝ} (sa : ConvergesTo s a) (sb : ConvergesTo s b) : a = b := by sorry
