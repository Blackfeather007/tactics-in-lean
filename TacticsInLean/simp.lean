import Mathlib
import Mathlib.Tactic

section simp
#help tactic simp

/- A lemma tagged with @[simp] is called a "simp lemma". -/

/-
When Lean’s simplifier `simp` is run, it tries to find "simp lemmas" for which the left hand side of the lemma is in the goal.
It then rewrites the lemma and continues. Ultimately what happens is that the goal ends up simplified, and, ideally, solved.
-/

-- Since following lemmas are tagged with simp, they are used by simp tactic if possible
#check add_zero
#check zero_add
example (x : ℝ) : 0 + 0 + x + 0 + 0 = (x + (0 + 0)) := by
  simp


open BigOperators List -- ∑ notation and access to `Finset.range`

example (n : ℕ) : ∑ i in Finset.range n, (i : ℝ) = n * (n - 1) / 2 := by
  induction' n with d hd
  ·  -- base case: sum over empty type is 0 * (0 - 1) / 2
    simp -- show simp?
  · -- inductive step
    rw [Finset.sum_range_succ, hd]
    simp -- tidies up and reduces the goal to
          -- ⊢ ↑d * (↑d - 1) / 2 + ↑d = (↑d + 1) * ↑d / 2
    ring -- a more appropriate tactic to finish the job

example (xs : List ℕ) : reverse (xs ++ [1, 2, 3]) = [3, 2, 1] ++ reverse xs := by
  simp

example {α : Type*} (xs ys : List α) : length (reverse (xs ++ ys)) = length xs + length ys := by
  simp [add_comm]

/-# What are "simp lemmas" are?

There are hundreds of lemmas in mathlib of the form `x + 0 = x` or `x * 0 = 0`, where one side is manifestly simpler than the other
(in the sense that a mathematician would instinctively replace the more complex side by the simpler side if they were trying to prove a theorem).
In Lean, such a lemma might be tagged with the @[simp] tag.
A tag on a lemma or definition does nothing mathematical; it is just a flag for certain tactics.
The convention for @[simp] lemmas in Lean is that the left hand side of such a lemma should be the more complicated side.

-/
/- see simp normal form in https://leanprover-community.github.io/mathlib_docs/notes.html#simp-normal%20form-/
-- @[simp]
-- lemma my_add_zero (x) : x + 0 = x := sorry

-- @[simp]
-- lemma my_zero_add' (x) : x = x + 0 := sorry
-- -- #lint only simpNF


/-# Variants of `simp`
- `simp` simplifies the main goal target using lemmas tagged with the attribute `[simp]`.
- `simp [h₁, h₂, ..., hₙ]` simplifies the main goal target using the lemmas tagged
  with the attribute `[simp]` and the given `hᵢ`'s, where the `hᵢ`'s are expressions.-
- If an `hᵢ` is a defined constant `f`, then `f` is unfolded. If `f` has equational lemmas associated
  with it (and is not a projection or a `reducible` definition), these are used to rewrite with `f`.
- `simp [*]` simplifies the main goal target using the lemmas tagged with the
  attribute `[simp]` and all hypotheses.
- `simp only [h₁, h₂, ..., hₙ]` is like `simp [h₁, h₂, ..., hₙ]` but does not use `[simp]` lemmas.
- `simp [-id₁, ..., -idₙ]` simplifies the main goal target using the lemmas tagged
  with the attribute `[simp]`, but removes the ones named `idᵢ`.
- `simp at h₁ h₂ ... hₙ` simplifies the hypotheses `h₁ : T₁` ... `hₙ : Tₙ`. If
  the target or another hypothesis depends on `hᵢ`, a new simplified hypothesis
  `hᵢ` is introduced, but the old one remains in the local context.
- `simp at *` simplifies all the hypotheses and the target.
- `simp [*] at *` simplifies target and all (propositional) hypotheses using the
  other hypotheses.

-/
end simp


section simpa

#help tactic simpa

/- If you have a goal and a hypothesis h, and if Lean’s simplifier simp, if run on both of them, will turn them into the same thing, then you could solve the goal in three lines with simp, simp at h, exact h, or even in two lines with simp at *, exact h. But you could also solve it in one line with simpa using h. In fact h doesn’t need to be a hypothesis, it can be any proof you like (e.g. a proof you made using some lemmas and some hypotheses).-/

example (x y z : ℝ) (h : x = y + z + 0) : x * 1 = y + z := by
  -- Lean's simplifier knows that a + 0 = 0 and a * 1 = a
  simpa using h

example (x y z : ℕ) (hxy : x = y) (h : z = y + 0) : z = x * 1 := by
  simpa [hxy] using h

example {a b c d : ℝ} (h1 : a < b) (h2 : b ≤ c) (h3 : c = d) : a + a < d + b := by
  refine add_lt_add ?_ h1
  simpa [h3] using (lt_of_lt_of_le h1 h2)

/- Easter egg: If your hypothesis is called this then you don’t have to write using this at all, you can just write simpa. -/

/- A hard example that only to show -/
open Filter Topology

example {a : ℝ} {f : ℝ → ℝ} (hf : ∀ x, x ≤ 0 → f x = x) (hf' : ∀ x, x > 0 → f x = x + a) (f_cont : Continuous f) : a = 0 := by
  have h1 : Tendsto f (𝓝[≤] 0) (𝓝 (f 0)) := (f_cont.tendsto 0).mono_left nhdsWithin_le_nhds
  have h2 : Tendsto f (𝓝[>] 0) (𝓝 (f 0)) := (f_cont.tendsto 0).mono_left nhdsWithin_le_nhds
  have h3 : Tendsto f (𝓝[≤] 0) (𝓝 0) := by
    apply tendsto_nhdsWithin_congr (f := id)
    simpa using (fun x hx ↦ (hf x hx).symm)
    exact (continuous_id.tendsto 0).mono_left nhdsWithin_le_nhds
  have h4 : Tendsto f (𝓝[>] 0) (𝓝 a) := by
    apply tendsto_nhdsWithin_congr (f := fun x ↦ x + a)
    simpa using (fun x hx ↦ (hf' x hx).symm)
    simpa using ((continuous_add_right a).tendsto 0).mono_left nhdsWithin_le_nhds
  rw [← tendsto_nhds_unique h1 h3, ← tendsto_nhds_unique h2 h4]

end simpa
