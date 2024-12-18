import Mathlib.Tactic
import Mathlib.Data.Real.Irrational

section Decide

example : 1 + 3 = 4 := by decide

example : Nat.Prime 17 := by decide

example : Nat.gcd 18 8 = 2 := by decide

example : Nat.divisors 18 = {1, 2, 3, 6, 9, 18} := by decide

example : Nat.primeFactors 18 = {2, 3} := by decide!

example : Irrational √2 := by decide!

example : Nat.factorial 10 = 3628800 := by decide

inductive Color
| Red | Blue | Yellow | Green
deriving DecidableEq

example : Color.Red ≠ Color.Green := by decide

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
  decide

example : quickSort (· < ·) [3, 2, 1] = [1, 2, 3] := by
  decide!

unseal quickSort in
example :  quickSort (· < ·) [3, 2, 1] = [1, 2, 3] := by
  decide

end Decide
