import Mathlib.Tactic

section Rcases

/-
syntax "rcases"... [Lean.Parser.Tactic.rcases]
  `rcases` is a tactic that will perform `cases` recursively, according to a pattern. It is used to
  destructure hypotheses or expressions composed of inductive types like `h1 : a ∧ b ∧ c ∨ d` or
  `h2 : ∃ x y, trans_rel R x y`. Usual usage might be `rcases h1 with ⟨ha, hb, hc⟩ | hd` or
  `rcases h2 with ⟨x, y, _ | ⟨z, hxz, hzy⟩⟩` for these examples.

  Each element of an `rcases` pattern is matched against a particular local hypothesis (most of which
  are generated during the execution of `rcases` and represent individual elements destructured from
  the input expression). An `rcases` pattern has the following grammar:

  * A name like `x`, which names the active hypothesis as `x`.
  * A blank `_`, which does nothing (letting the automatic naming system used by `cases` name the
    hypothesis).
  * A hyphen `-`, which clears the active hypothesis and any dependents.
  * The keyword `rfl`, which expects the hypothesis to be `h : a = b`, and calls `subst` on the
    hypothesis (which has the effect of replacing `b` with `a` everywhere or vice versa).
  * A type ascription `p : ty`, which sets the type of the hypothesis to `ty` and then matches it
    against `p`. (Of course, `ty` must unify with the actual type of `h` for this to work.)
  * A tuple pattern `⟨p1, p2, p3⟩`, which matches a constructor with many arguments, or a series
    of nested conjunctions or existentials. For example if the active hypothesis is `a ∧ b ∧ c`,
    then the conjunction will be destructured, and `p1` will be matched against `a`, `p2` against `b`
    and so on.
  * A `@` before a tuple pattern as in `@⟨p1, p2, p3⟩` will bind all arguments in the constructor,
    while leaving the `@` off will only use the patterns on the explicit arguments.
  * An alternation pattern `p1 | p2 | p3`, which matches an inductive type with multiple constructors,
    or a nested disjunction like `a ∨ b ∨ c`.

  A pattern like `⟨a, b, c⟩ | ⟨d, e⟩` will do a split over the inductive datatype,
  naming the first three parameters of the first constructor as `a,b,c` and the
  first two of the second constructor `d,e`. If the list is not as long as the
  number of arguments to the constructor or the number of constructors, the
  remaining variables will be automatically named. If there are nested brackets
  such as `⟨⟨a⟩, b | c⟩ | d` then these will cause more case splits as necessary.
  If there are too many arguments, such as `⟨a, b, c⟩` for splitting on
  `∃ x, ∃ y, p x`, then it will be treated as `⟨a, ⟨b, c⟩⟩`, splitting the last
  parameter as necessary.

  `rcases` also has special support for quotient types: quotient induction into Prop works like
  matching on the constructor `quot.mk`.

  `rcases h : e with PAT` will do the same as `rcases e with PAT` with the exception that an
  assumption `h : e = PAT` will be added to the context.
-/
#help tactic rcases

example {x : ℝ} (h : x = 1 ∨ x = 2) : x ^ 2 - 3 * x + 2 = 0 := by
  sorry

example {x y : ℝ} (h : x = 2 ∨ y = -2) : x * y + 2 * x = 2 * y + 4 := by
  sorry


def f (_ : List Empty) (b : Bool) := b

@[simp]
theorem lem1 (a : Bool) : f [] a = a := rfl

@[simp]
theorem lem2 (a b : Bool) (x y : List Empty)
  (h : f x a = f y b) : x = y := by
    sorry
example : (([] : List Empty).take 0) = [] := by rfl

namespace ZMod

theorem mul_inv_of_unit' {n : ℕ} {a : ZMod n} (h : IsUnit a) : a * a⁻¹ = 1 := by
  sorry

end ZMod

/-
https://leanprover.zulipchat.com/#narrow/channel/113489-new-members/topic/Need.20help.20understanding.20a.20type.20class.20example
-/

class inductive Something where
 | oneThing : Something
 | anotherThing : Something

instance instOne : Something := Something.oneThing

@[instance]
def instAnother : Something := Something.anotherThing

example [s : Something] : s = Something.oneThing ∨ s = Something.anotherThing := by
  sorry

def mwe' := {s : String // s ∈ ({"A", "B", "C"} : Set String)}

def A : mwe' := ⟨"A", by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, String.reduceEq,
  or_false]⟩
def B : mwe' := ⟨"B", by simp only [Set.mem_insert_iff, String.reduceEq, Set.mem_singleton_iff,
  or_false, or_true]⟩
def C : mwe' := ⟨"C", by simp only [Set.mem_insert_iff, String.reduceEq, Set.mem_singleton_iff,
  or_true]⟩

example (x : mwe') : x = A ∨ x = B ∨ x = C := by
  sorry

lemma sq_mod_four {x : ℤ} :x ^ 2 % 4 = 0 ∨ x ^ 2 % 4 = 1 := by
  have hx := Int.even_or_odd x
  sorry

-- hard
theorem Int.neg_ediv_natCast (a : ℤ) (b : ℕ) : (-a) / b = - ((a + b - 1) / b) := by
  sorry

theorem Int.neg_ediv (a b : ℤ) : (-a) / b = - ((a + b.natAbs - 1) / b) := by
  sorry

@[ext]
class PFilter {X: Type*} (A: Set X) extends Filter X where
  point : Set X
  point_eq : point = A
  point_in : A ∈ sets

lemma eq {X: Type*} (A: Set X): ∀ (F G: PFilter A), F.sets = G.sets → F = G := by
  intros F G h
  sorry

open BigOperators Real Nat Topology Rat

example (a : ℝ) (h : 0 < a) (h_eq : a^3 = 6 * (a + 1)) : ¬ ∃ x : ℝ, x^2 + a * x + a^2 - 6 = 0 := by
  intro h_contra
  sorry

inductive X : Type
  | mkX : List Unit → X

abbrev X.nil : X := ⟨[]⟩

abbrev X.cons : Unit → X → X | x, ⟨xs⟩ => ⟨x :: xs⟩

inductive P : X → X → Prop
  | step (x' : X) : P x' x' → P (X.cons () x') (X.cons () x')
  | nil : P X.nil X.nil

theorem no_bug {x' y a : X} (h : P y a) (hy : y = X.cons () x' ): ∃ x'', a = X.cons () x'' := by
  sorry

theorem Real_archimedean' (x y : ℝ) : (0 < x) → (0 < y) → ∃ (n : ℕ), y < n * x := by
  intro x_pos y_pos
  have : ∃ (n : ℕ), y ≤ n • x := by
    apply Archimedean.arch y x_pos
  sorry

end Rcases
