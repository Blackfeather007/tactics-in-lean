import Mathlib.Tactic


section Obtain

/-
syntax "obtain"... [Lean.Parser.Tactic.obtain]
  The `obtain` tactic is a combination of `have` and `rcases`. See `rcases` for
  a description of supported patterns.

  ```lean
  obtain ⟨patt⟩ : type := proof
  ```
  is equivalent to
  ```lean
  have h : type := proof
  rcases h with ⟨patt⟩
  ```

  If `⟨patt⟩` is omitted, `rcases` will try to infer the pattern.

  If `type` is omitted, `:= proof` is required.
-/
#help tactic obtain

inductive MyNat : Type
| zero : MyNat
| succ : MyNat -> MyNat

#check @MyNat.rec
/-
As you can probably imagine, when you're writing Lean tactics, Lean is secretly making some function piece by piece -- the goals that you see in tactic mode are the holes where the definition is incomplete. The cases, obtain, induction etc etc tactics are secretly applying functions called recursors, which are made automatically whenever the user creates an inductive type. For example this code

creates a new type MyNat, a new term MyNat.zero of this type, a new function MyNat.succ from MyNat to MyNat, and a secret fourth thing MyNat.rec which is the principle of recursion and induction (it works for types and props, because it has Sort u as its conclusion, and Sort u means "either Prop or Type u").

If you have some goal which is a proposition involving n : MyNat, then induction n basically does apply MyNat.rec,
lets t be n, fills in the last goal and opens two new goals corresponding to the inputs of MyNat.rec which are the zero case and the succ case.

If you look at Exists.rec though, it says something a bit different:
-/

#check Exists.rec
/-
The motive only takes values in Prop. This means in practice that if your goal isn't a theorem statement, then cases h/obtain ... := h/induction h won't work if h : \exists x, p x because Lean can't make the relevant function which tactic mode makes because things don't match up. The reason the recursor only takes values in Prop is basically because Exists itself is a Prop,
and moving from the Prop universe to the Type universe is fraught with danger in type theory; you allow it to happen and your theory can become inconsistent. Moving from Prop to Type is exactly what the type theory axiom of choice does, but this is an extra axiom in Lean's theory.
-/

/-
universe u
variable {R : Type u} [CommRing R]
variable {ι : Type u}
variable {N : ι → Type u} [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]
variable {M : Type u} [AddCommGroup M] [Module R M]

noncomputable def test  [Module.FinitePresentation R M] : Module.FinitePresentation R M := by
  have hfpB : Module.FinitePresentation R M := inferInstance
  obtain ⟨L, hL, fL, K, hK, hFree, hFinite, hFG⟩ := Module.FinitePresentation.equiv_quotient R M
  sorry
-/

-- practice

example (h : ∃ x, x > 0) : ∃ y, y > 0 := by
  sorry

example {α β : Prop} (h : α ∨ β) : α ∨ β := by
  sorry

example {α β : Prop} (h : α → β) : α → β := by
  sorry

example {x y : ℝ} (h : ∀ x, ∃ y, x + y = 0) : ∀ x, ∃ y, x + y = 0 := by
  sorry

example (h : ∃ x, ∃ y, x + y = 3) : ∃ x, ∃ y, x + y = 3 := by
  sorry

example {α β γ ζ ε δ : Prop} (h : (α ∧ β) ∨ (γ ∧ δ) ∨ (ε ∧ ζ)) : α ∧ β ∨ γ ∧ δ ∨ ε ∧ ζ := by
  sorry

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a

theorem fnUb_add {f g : ℝ → ℝ} {a b : ℝ} (hfa : FnUb f a) (hgb : FnUb g b) :
    FnUb (fun x ↦ f x + g x) (a + b) :=
  fun x ↦ add_le_add (hfa x) (hgb x)

example {f g : ℝ → ℝ} (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  sorry

-- You don't have to prove it. Only for reading.

theorem two_le {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  cases m; contradiction
  case succ m =>
    cases m; contradiction
    repeat apply Nat.succ_le_succ
    apply zero_le

theorem mod_4_eq_3_or_mod_4_eq_3 {m n : ℕ} (h : m * n % 4 = 3) : m % 4 = 3 ∨ n % 4 = 3 := by
  revert h
  rw [Nat.mul_mod]
  have : m % 4 < 4 := Nat.mod_lt m (by norm_num)
  interval_cases m % 4 <;> simp [-Nat.mul_mod_mod]
  have : n % 4 < 4 := Nat.mod_lt n (by norm_num)
  interval_cases n % 4 <;> simp

theorem two_le_of_mod_4_eq_3 {n : ℕ} (h : n % 4 = 3) : 2 ≤ n := by
  apply two_le <;>
    · intro neq
      rw [neq] at h
      norm_num at h

theorem aux {m n : ℕ} (h₀ : m ∣ n) (h₁ : 2 ≤ m) (h₂ : m < n) : n / m ∣ n ∧ n / m < n := by
  constructor
  · exact Nat.div_dvd_of_dvd h₀
  exact Nat.div_lt_self (lt_of_le_of_lt (zero_le _) h₂) h₁

theorem exists_prime_factor_mod_4_eq_3 {n : Nat} (h : n % 4 = 3) :
    ∃ p : Nat, p.Prime ∧ p ∣ n ∧ p % 4 = 3 := by
  by_cases np : n.Prime
  · use n
  induction' n using Nat.strong_induction_on with n ih
  rw [Nat.prime_def_lt] at np
  push_neg at np
  rcases np (two_le_of_mod_4_eq_3 h) with ⟨m, mltn, mdvdn, mne1⟩
  have mge2 : 2 ≤ m := by
    apply two_le _ mne1
    intro mz
    rw [mz, zero_dvd_iff] at mdvdn
    linarith
  have neq : m * (n / m) = n := Nat.mul_div_cancel' mdvdn
  have : m % 4 = 3 ∨ n / m % 4 = 3 := by
    apply mod_4_eq_3_or_mod_4_eq_3
    rw [neq, h]
  rcases this with h1 | h1
  · by_cases mp : m.Prime
    · use m
    rcases ih m mltn h1 mp with ⟨p, pp, pdvd, p4eq⟩
    use p
    exact ⟨pp, pdvd.trans mdvdn, p4eq⟩
  obtain ⟨nmdvdn, nmltn⟩ := aux mdvdn mge2 mltn
  by_cases nmp : (n / m).Prime
  · use n / m
  rcases ih (n / m) nmltn h1 nmp with ⟨p, pp, pdvd, p4eq⟩
  use p
  exact ⟨pp, pdvd.trans nmdvdn, p4eq⟩

theorem even_of_even_sqr {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m := by
  rw [pow_two, Nat.prime_two.dvd_mul] at h
  cases h <;> assumption

example {m n : ℕ} (coprime_mn : m.Coprime n) : m ^ 2 ≠ 2 * n ^ 2 := by
  intro sqr_eq
  have : 2 ∣ m := by
    apply even_of_even_sqr
    rw [sqr_eq]
    apply dvd_mul_right
  obtain ⟨k, meq⟩ := dvd_iff_exists_eq_mul_left.mp this
  have : 2 * (2 * k ^ 2) = 2 * n ^ 2 := by
    rw [← sqr_eq, meq]
    ring
  have : 2 * k ^ 2 = n ^ 2 :=
    (mul_right_inj' (by norm_num)).mp this
  have : 2 ∣ n := by
    apply even_of_even_sqr
    rw [← this]
    apply dvd_mul_right
  have : 2 ∣ m.gcd n := by
    apply Nat.dvd_gcd <;>
    assumption
  have : 2 ∣ 1 := by
    convert this
    symm
    exact coprime_mn
  norm_num at this

open BigOperators Finset
open Set Filter
open Topology Filter

variable {X : Type*} [MetricSpace X]

theorem cauchySeq_of_le_geometric_two' {u : ℕ → X}
    (hu : ∀ n : ℕ, dist (u n) (u (n + 1)) ≤ (1 / 2) ^ n) : CauchySeq u := by
  rw [Metric.cauchySeq_iff']
  intro ε ε_pos
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 1 / 2 ^ N * 2 < ε := by sorry
  use N
  intro n hn
  obtain ⟨k, rfl : n = N + k⟩ := le_iff_exists_add.mp hn
  calc
    dist (u (N + k)) (u N) = dist (u (N + 0)) (u (N + k)) := sorry
    _ ≤ ∑ i in range k, dist (u (N + i)) (u (N + (i + 1))) := sorry
    _ ≤ ∑ i in range k, (1 / 2 : ℝ) ^ (N + i) := sorry
    _ = 1 / 2 ^ N * ∑ i in range k, (1 / 2 : ℝ) ^ i := sorry
    _ ≤ 1 / 2 ^ N * 2 := sorry
    _ < ε := sorry


end Obtain
