import Mathlib.tactic

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
-- `ring` can be used to prove the equality in a commutative (semi)rings.


example {n m : ℕ} : (n + m) ^ 2 = n ^ 2 + 2 * n * m + m ^ 2 := by
  sorry
-- It also works for natural numbers (commuative semiring).


example (x y : ℝ) (f : ℝ → ℝ):  f (x + y) + f (y + x) = 2 * f (x + y) := by
  ring says ring_nf
-- `ring_nf` can also prove some equations that ring may not be able to,
-- because they involve ring reasoning inside a subterm.


example (x y : ℤ) (h : (x - y) ^ 2 = 0) : x ^ 2 + y ^ 2 - 2 * x * y = 0 := by
  ring_nf at h ⊢
  exact h
-- `ring_nf` can be used at hypothesis and goal.


example (x y : ℕ) : x + id y = y + id x := by
  ring! -- rw [id_eq] ; ring_nf
-- `ring!` will use a more aggressive reducibility setting to determine equality of atoms.
-- But it will not be always useful.

example {R : Type} [Ring R] (a b : R) : (a + b) ^ 2 = a ^ 2 + b ^ 2 + a * b + b * a := by
  ring says ring_nf -- nothing happened.
  sorry
-- `ring` or `ring_nf` only work for commutative (semi)rings.


example {R : Type} [Ring R] (a b : R) : (a + b) ^ 2 = a ^ 2 + b ^ 2 + a * b + b * a := by
  noncomm_ring
-- `noncomm_ring` can simplify identities in not-necessarily-commutative rings.


open Complex

example {a : ℝ} : a ^ 2 - 6 = (a + Real.sqrt 6) * (a - Real.sqrt 6) := by
  calc
   _ = a ^ 2 - (Real.sqrt 6) ^ 2 := by simp only [Nat.ofNat_nonneg, Real.sq_sqrt]
   _ = _ := by ring


example (x : ℝ) (hx : x ^ 2 - 5 * x + 6 = 0) :  x = 3 ∨ x = 2 := by
  rw [show x ^ 2 - 5 * x + 6 = (x - 3) * (x - 2) by ring, mul_eq_zero] at hx
  rw [sub_eq_zero, sub_eq_zero] at hx
  exact hx


example (a : ℂ) (h : (a + 2) ^ 2 = - 9) : a + 2 = 3 * I ∨ a + 2 = - (3 * I) := by
  rw [show - 9 = (3 * I) ^ 2 by ring_nf ; simp] at h
  rw [sq_eq_sq_iff_eq_or_eq_neg (a := a + 2) (b := 3 * I)] at h
  exact h
-- Try using `ring` to simpilify each small step.


example (a b : ℝ) : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  have h : 0 ≤ a ^ 2 - 2 * a * b + b ^ 2
  calc
    a ^ 2 - 2 * a * b + b ^ 2 = (a - b) ^ 2 := by ring
    _ ≥ 0 := pow_two_nonneg (a - b)

  calc
    2 * a * b = 2 * a * b + 0 := by ring
    _ ≤ 2 * a * b + (a ^ 2 - 2 * a * b + b ^ 2) := (add_le_add_iff_left (2 * a * b)).2 h
    _ = a ^ 2 + b ^ 2 := by ring



theorem Cauchy_Schwarz_Ineq (a b c d : ℝ) :
    a * c + b * d ≤ (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) := sorry
