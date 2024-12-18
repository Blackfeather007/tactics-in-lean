import Mathlib.Tactic
import Mathlib.Data.Real.Irrational

section Decide

/-
syntax "decide"... [Lean.Parser.Tactic.decide]
  `decide` attempts to prove the main goal (with target type `p`) by synthesizing an instance of `Decidable p`
  and then reducing that instance to evaluate the truth value of `p`.
  If it reduces to `isTrue h`, then `h` is a proof of `p` that closes the goal.

  Limitations:
  - The target is not allowed to contain local variables or metavariables.
    If there are local variables, you can try first using the `revert` tactic with these local variables
    to move them into the target, which may allow `decide` to succeed.
  - Because this uses kernel reduction to evaluate the term, `Decidable` instances defined
    by well-founded recursion might not work, because evaluating them requires reducing proofs.
    The kernel can also get stuck reducing `Decidable` instances with `Eq.rec` terms for rewriting propositions.
    These can appear for instances defined using tactics (such as `rw` and `simp`).
    To avoid this, use definitions such as `decidable_of_iff` instead.
-/
#help tactic decide

/-
syntax "decide!"... [Lean.Parser.Tactic.decideBang]
  `decide!` is a variant of the `decide` tactic that uses kernel reduction to prove the goal.
  It has the following properties:
  - Since it uses kernel reduction instead of elaborator reduction, it ignores transparency and can unfold everything.
  - While `decide` needs to reduce the `Decidable` instance twice (once during elaboration to verify whether the tactic succeeds,
    and once during kernel type checking), the `decide!` tactic reduces it exactly once.
-/
#help tactic decide!

example : 1 + 3 = 4 := by sorry

example : Nat.Prime 17 := by sorry

example : Nat.gcd 18 8 = 2 := by sorry

example : Nat.divisors 18 = {1, 2, 3, 6, 9, 18} := by sorry

example : Nat.primeFactors 18 = {2, 3} := by sorry

example : Irrational √2 := by sorry

example : Nat.factorial 10 = 3628800 := by sorry

inductive Color
| Red | Blue | Yellow | Green
deriving DecidableEq

example : Color.Red ≠ Color.Green := by sorry

def quickSort {α : Type*} (r : α → α → Bool) (l : List α) :=
  match l with
  | [] => []
  | x :: t =>
      let ts := List.partition (fun m => r m x) t
      quickSort r ts.1 ++ [x] ++ quickSort r ts.2
termination_by l.length
decreasing_by
· simp only [List.partition_eq_filter_filter, List.length_cons, gt_iff_lt]
  suffices (List.filter (fun m ↦ r m x) t).length ≤ t.length by
    linarith
  exact List.length_filter_le (fun m ↦ r m x) t
· simp only [List.partition_eq_filter_filter, List.length_cons, gt_iff_lt]
  suffices (List.filter (not ∘ fun m ↦ r m x) t).length ≤ t.length by
    linarith
  exact List.length_filter_le (not ∘ fun m ↦ r m x) t

example : List.insertionSort (· < ·) [3, 2, 1] = [1, 2, 3] := by
  sorry

example : quickSort (· < ·) [3, 2, 1] = [1, 2, 3] := by
  sorry

unseal quickSort in
example :  quickSort (· < ·) [3, 2, 1] = [1, 2, 3] := by
  sorry

end Decide
