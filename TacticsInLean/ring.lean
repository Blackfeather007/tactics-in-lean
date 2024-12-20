import Mathlib.tactic

section Ring

/-
syntax "ring"... [Mathlib.Tactic.RingNF.ring]
  Tactic for evaluating expressions in *commutative* (semi)rings, allowing for variables in the
  exponent. If the goal is not appropriate for `ring` (e.g. not an equality) `ring_nf` will be
  suggested.

  * `ring!` will use a more aggressive reducibility setting to determine equality of atoms.
  * `ring1` fails if the target is not an equality.

  For example:


  ```lean
  example (n : ℕ) (m : ℤ) : 2^(n+1) * m = 2 * 2^n * m := by ring
  example (a b : ℤ) (n : ℕ) : (a + b)^(n + 2) = (a^2 + b^2 + a * b + b * a) * (a + b)^n := by ring
  example (x y : ℕ) : x + id y = y + id x := by ring!
  example (x : ℕ) (h : x * 2 > 5): x + x > 5 := by ring; assumption -- suggests ring_nf
  ```
-/

#help tactic ring

-- Excercise


example {x y : ℤ} : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  sorry

example {n m : ℕ} : (n + m) ^ 3 = n ^ 3 + m ^ 3 + 3 * m ^ 2 * n + 3 * m * n ^ 2 := by
  sorry

example (x y : ℝ) (f : ℝ → ℝ) : f (x + y) + f (y + x) = 2 * f (x + y) := by
  sorry

example (x y : ℤ) (h : (x - y) ^ 2 = 0) : x ^ 2 + y ^ 2 = 2 * x * y := by
  sorry

example (x y : ℕ) : x * 2 + id y = y + 2 * id x := by
  sorry

example {R : Type} [Ring R] (a b : R) : (a + b) ^ 2 = a ^ 2 + b ^ 2 + a * b + b * a := by
  sorry


open Complex

example {a : ℝ} : a ^ 2 - 6 = (a + Real.sqrt 6) * (a - Real.sqrt 6) :=
  sorry

example (x : ℝ) (hx : x ^ 2 - 5 * x + 6 = 0) :  x = 3 ∨ x = 2 :=
  sorry

example (a : ℂ) (h : (a + 2) ^ 2 = - 9) : a + 2 = 3 * I ∨ a + 2 = - (3 * I) :=
  sorry

example (a b : ℝ) : 2 * a * b ≤ a ^ 2 + b ^ 2 :=
  sorry

theorem Cauchy_Schwarz_Ineq (a b c d : ℝ) :
    (a * c + b * d) ^ 2 ≤ (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) :=
  sorry

end Ring
