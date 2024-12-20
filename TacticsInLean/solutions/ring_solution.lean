import Mathlib.Tactic

section Ring

example {x y : ℤ} : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  ring
-- `ring` can be used to prove the equality in a commutative (semi)rings.

example {n m : ℕ} : (n + m) ^ 3 = n ^ 3 + m ^ 3 + 3 * m ^ 2 * n + 3 * m * n ^ 2 := by
  ring
-- It also works for natural numbers (commuative semiring).

example (x y : ℝ) (f : ℝ → ℝ) : f (x + y) + f (y + x) = 2 * f (x + y) := by
  ring says ring_nf
-- `ring_nf` can also prove some equations that ring may not be able to,
-- because they involve ring reasoning inside a subterm.

example (x y : ℤ) (h : (x - y) ^ 2 = 0) : x ^ 2 + y ^ 2 = 2 * x * y := by
  ring_nf at h
  rw [← add_zero (2 * x * y), ← h]
  ring
-- `ring_nf` can be used non-terminally to normalize ring expressions in hypothesis.

example (x y : ℕ) : x * 2 + id y = y + 2 * id x := by
  ring! -- simp only [id_eq] ; ring
-- `ring!` will use a more aggressive reducibility setting to determine equality of atoms.
-- But it will not always be useful.

example {R : Type} [Ring R] (a b : R) : (a + b) ^ 2 = a ^ 2 + b ^ 2 + a * b + b * a := by
  ring_nf -- Nothing happened.
  sorry
-- NOTICE: `ring`, `ring_nf`, and `ring!` etc. only work for **commutative** (semi)rings.

example {R : Type} [Ring R] (a b : R) : (a + b) ^ 2 = a ^ 2 + b ^ 2 + a * b + b * a := by
  noncomm_ring
-- `noncomm_ring` can simplify identities in not-necessarily-commutative rings.


open Complex

example {a : ℝ} : a ^ 2 - 6 = (a + Real.sqrt 6) * (a - Real.sqrt 6) :=
  calc
   _ = a ^ 2 - (Real.sqrt 6) ^ 2 := by simp [Nat.ofNat_nonneg, Real.sq_sqrt]
   _ = _ := by ring

example (x : ℝ) (hx : x ^ 2 - 5 * x + 6 = 0) : x = 3 ∨ x = 2 := by
  rw [show x ^ 2 - 5 * x + 6 = (x - 3) * (x - 2) by ring, mul_eq_zero] at hx
  simp only [sub_eq_zero] at hx
  exact hx

example (a : ℂ) (h : (a + 2) ^ 2 = - 9) : a + 2 = 3 * I ∨ a + 2 = - (3 * I) := by
  rw [show - 9 = (3 * I) ^ 2 by ring_nf ; simp] at h
  rw [sq_eq_sq_iff_eq_or_eq_neg (a := a + 2) (b := 3 * I)] at h
  exact h

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
    (a * c + b * d) ^ 2 ≤ (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) := by
  have h : 0 ≤ (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) - (a * c + b * d) ^ 2
  calc
    (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) - (a * c + b * d) ^ 2 = (a * d - b * c) ^ 2 := by ring
    _ ≥ 0 := pow_two_nonneg (a * d - b * c)

  calc
    (a * c + b * d) ^ 2  = (a * c + b * d) ^ 2 + 0 := by rw [add_zero]
    _ ≤ (a * c + b * d) ^ 2 + ((a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) - (a * c + b * d) ^ 2) :=
    (add_le_add_iff_left _).2 h
    _ = (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) := by ring

end Ring
