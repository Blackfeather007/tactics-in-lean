import Mathlib
set_option maxHeartbeats 0
section Have

#check Lean.Parser.Tactic.tacticHave_
#help  tactic have

/-
syntax "have "... [Lean.Parser.Tactic.tacticHave_]
The `have` tactic is for adding hypotheses to the local context of the main goal.
* `have h : t := e` adds the hypothesis `h : t` if `e` is a term of type `t`.
* `have h := e` uses the type of `e` for `t`.
* `have : t := e` and `have := e` use `this` for the name of the hypothesis.
* `have pat := e` for a pattern `pat` is equivalent to `match e with | pat => _`,
  where `_` stands for the tactics that follow this one.
  It is convenient for types that have only one applicable constructor.
  For example, given `h : p ∧ q ∧ r`, `have ⟨h₁, h₂, h₃⟩ := h` produces the
  hypotheses `h₁ : p`, `h₂ : q`, and `h₃ : r`.
-/

/-
Part I: Usage and basic patterns of `have` (1)
-/

-- Easy example 1: Introducing a simple proposition
example (P : Prop) (h : P) : P ∧ P := by
  have hp : P := h  -- Introduce an assumption named hp, with type P, derived from h
  exact And.intro hp h

-- Easy example 2: Type can be automatically inferred
example (P : Prop) (h : P) : P ∧ P := by
  have hp := h   -- Introduce an assumption named hp, with its type automatically inferred as P
  exact And.intro hp h

-- Easy example 3: What happens when adding parentheses?
example (P : Prop) (h : P) : P ∧ P := by
  have (hp : P) := h  -- Here, an assumption with the parameter name hp is introduced
  exact ⟨h, this h⟩

-- Easy example 4: Using the `this` keyword
example (P : Prop) (h : P) : P ∧ P := by
  have : P := h   -- Introduce an anonymous assumption of type P, with the name `this`
  exact And.intro this h

-- Easy example 5: Using the `this` keyword + automatic type inference
example (P : Prop) (h : P) : P ∧ P := by
  have := h   -- Introduce an anonymous assumption of type P, with the name `this`
  exact And.intro this h

/-
Part I: Usage and basic patterns of `have` (2)
-/

-- Easy example 6: Intersection of sets
example (S T : Set ℝ) (x : ℝ) (h : x ∈ S ∩ T) : x ∈ S := by
  -- Use pattern matching to destructure the definition of intersection
  sorry

-- Easy example 7: Ordered pairs
example (a b : ℝ) (h : (a, b) = (1, 2)) : a = 1 := by
  -- Introduce anonymous hypothesis `this : a = 1` by injecting the equality `h`.

  -- Use the hypothesis `this` to prove the goal.
  sorry

example (a b : ℝ) (h : (a, b) = (1, 2)) : a = 1 := by
  -- -- Introduce hypothesis `h1 : a = 1 ∧ h2 : b = 2` by applying the injectivity of pairs to `h`.

  -- have ?_ := by exact Prod.mk.inj_iff.mp h

  -- Use the first part of the hypothesis `h1` to prove the goal.

  sorry
 
/-
Part II: Why is it necessary to use `have`? [`have` + `apply`?]

Sometimes we know a certain theorem, but it requires certain conditions to hold. Therefore, it's necessary to use `have` to introduce an auxiliary proposition, and then use `apply?`, `rw?`, `simp?`, and `leansearch?` to prove this auxiliary proposition.
-/

-- Easy example 8: If there exists an odd number k such that a^k = 1, then the order of the group element a is odd.
example {G : Type*} [Group G] (a : G) (k : ℕ) (h : Odd k) (pow_one : a ^ k = 1): Odd (orderOf a) := by
  -- It is known that if a natural number divides an odd number, then it is also odd.
  #check Odd.of_dvd_nat
  -- Let the order of element $a$ be $n$. It suffices to prove that $n ∣ k$.
  set n := orderOf a with hn
  -- Use `have` to introduce an auxiliary proposition: $n ∣ k$.

  -- Since $k$ is odd, $n$, being a factor of the odd number $k$, is also odd.
  -- For Lean4 proof, just use `apply?` tactic.

  sorry

/-
Middle Easy example 1:
For coprime positive integers $a, b$, if positive integers $x, y$ are both less than or equal to $b$, and $x \neq y$, then the remainders of $x * a$ and $y * a$ modulo $b$ are necessarily unequal.
-/
example {a b : ℕ+} [h : Fact (a.Coprime b)]
  {x y : ℕ+} (hx : x.val ≤ b.val) (hxy : y < x) :
  ¬(x.val * a.val ≡ y.val * a.val [MOD b.val]) := by
  intro hmod
  -- First, from the condition `x.val * a.val ≡ y.val * a.val [MOD b.val]`, we can deduce that $b.val ∣ (x.val * a.val - y.val * a.val)$.
  -- have h1 : ?_ := by
  --   apply (Nat.modEq_iff_dvd' ?_).mp (Nat.ModEq.symm hmod)
  --   exact (mul_le_mul_right (a := a.val) a.2).2 hxy.le

  -- Since $a$ and $b$ are coprime, we obtain $b.val ∣ (x.val - y.val)$.
  -- have h2 : ?_ := by
  --   rw [← Nat.mul_sub_right_distrib] at h1
  --   apply (@Nat.Coprime.dvd_mul_right _ a b ?_).mp h1
  --   simp only [PNat.coprime_coe, h.out.symm]

  -- Then, from the properties of divisibility for natural numbers, we obtain $b.val ≤ (x.val - y.val)$.
  -- have h3 : ?_ :=
  --   Nat.le_of_dvd (Nat.sub_pos_iff_lt.mpr hxy) h2

  -- However, from the conditions, $x.val - y.val < b.val$, which leads to a contradiction.
  -- have h4 : ?_ :=
  --   Nat.lt_of_lt_of_le (Nat.sub_lt x.2 y.2) hx
  -- linarith!
  sorry

/-
Middle Easy example 2:
Assume we know: "If a non-negative continuous function $f$ satisfies that its integral over the closed interval $[a, b]$ is 0, then it is identically 0 on the closed interval $[a, b]$."
Prove: If a continuous function $f$ on a closed interval satisfies $∫_{0}^{1} f(x)^2 dx = 0$, then $f$ is identically 0 on that interval.
-/
lemma MEE2 {g : ℝ → ℝ} {a b : ℝ}
  (hab : a < b)
  (hg_cont : ContinuousOn g (Set.Icc a b))
  (hg_nonneg : ∀ x ∈ Set.Icc a b, 0 ≤ g x)
  (h_int_zero : ∫ (x : ℝ) in a..b, g x = 0) :
  Set.EqOn g 0 (Set.Icc a b) := by
  apply MeasureTheory.Measure.eqOn_Icc_of_ae_eq
    (@MeasureTheory.volume ℝ Real.measureSpace) hab.ne
  . rw [← MeasureTheory.restrict_Ioc_eq_restrict_Icc]
    rw [← intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae hab.le]
    . exact h_int_zero
    . apply Filter.eventuallyLE_iff_all_subsets.mpr fun s => ?_
      simp only [measurableSet_Ioc, MeasureTheory.ae_restrict_eq,
        Filter.eventually_inf_principal]
      exact Filter.univ_mem' fun y hy1 hy2 =>
        hg_nonneg y (Set.mem_Icc_of_Ioc hy1)
    . rw [← Set.uIcc_of_le hab.le] at hg_cont
      exact ContinuousOn.intervalIntegrable hg_cont
  . exact hg_cont
  . exact (Continuous.continuousOn (s := (Set.Icc a b)) continuous_zero)

example (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc 0 1)) :
  (∫ (x : ℝ) in (0)..1, f x ^ 2 = 0) → (∀ x ∈ Set.Icc 0 1, f x = 0) := by
  intro h x hx
  set g := fun (x : ℝ) => f x ^ 2 with hg
  -- The function `g` is continuous on `[0,1]`
  -- have hg_cont : ?_ := by
  --   simp only [hg]
  --   exact ContinuousOn.pow hf 2

  -- And g is eq zero on `[0,1]`.
  -- have : ?_ :=
  --   MEE2 (by norm_num) hg_cont (fun x hx => sq_nonneg (f x)) h
  -- specialize this hx
  -- rw [Pi.zero_apply, hg, pow_eq_zero_iff (by norm_num)] at this
  -- exact this
  sorry

end Have
