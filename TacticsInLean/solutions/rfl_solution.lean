import Mathlib.Tactic

section Rfl

example {n : ℕ} : n + 0 = n := by
  rfl

-- example {a b c : ℝ} : (a + b) + c = a + (b + c) := by
--   rfl -- wrong! :(

-- example {a b c : ℝ} : a + (b + c) = a + b + c := by
--   rfl -- wrong too!

-- example {a b c : ℕ} : a * (b + c) = a * b + a * c := by
--   rfl -- wrong!

def primes_set := { n | Nat.Prime n }

instance : Infinite primes_set := Nat.infinite_setOf_prime.to_subtype

instance : DecidablePred (fun n => n ∈ primes_set) := fun n => Nat.decidablePrime n

def primes (n : ℕ) : ℕ := if (n = 0) then 0 else Nat.Subtype.ofNat primes_set (n - 1)

lemma primes_zero : primes 0 = 0 := by
  rfl

example : {s : Fin 19 → Fin 2 | ∀ n : Fin 19, 10 ≤ n.val → s n = 0}.ncard = 2 ^ 10 := by
    rw [← Set.Nat.card_coe_set_eq, Set.coe_setOf,
      Nat.card_congr <| @Equiv.subtypePiEquivPi (Fin 19) _ fun n i => 10 ≤ n.val → i = 0]
    rw [Nat.card_pi, Fin.prod_univ_add (a := 10) (b := 9)]
    simp
    rfl -- This proof works, but it breaks down when replacing 2 by 200, because the rfl at the end can't expand that much.

-- instance : HMul ℝ ℝ ℕ := ⟨fun _ _ ↦ 0⟩

-- instance : HMul ℝ ℝ Bool := ⟨fun _ _ ↦ false⟩

-- example (x y : ℝ) : HMul.hMul x y = (0 : ℕ) := by
--   rfl-- type mismatch
-- example (x y : ℝ) : HMul.hMul x y = false := by
--   rfl -- it works

inductive xNat where
  | zero : xNat
  | succ (n : xNat) : xNat

def ofxNat : (n : Nat) → xNat
  | Nat.zero   => xNat.zero
  | Nat.succ m => xNat.succ (ofxNat m)

instance (n : Nat) : OfNat xNat n where
  ofNat := ofxNat n

def xNat.add : (a b : xNat) → xNat
  | zero,    b => b
  | succ a', b => xNat.succ (xNat.add a' b)

instance : Add xNat where
  add := xNat.add

/-
def xNat.add : (a b : xNat) → xNat
  | a,   zero  => a
  | a, succ b' => xNat.succ (xNat.add a b')
-/

-- -- doesn't work
-- example (n : xNat) : n.succ = n + 1 := by rfl

-- works!!
example (n : xNat) : n.succ = 1 + n := by rfl

-- works
example (n : Nat) : n.succ = n + 1 := by rfl

universe u

theorem types_hom {α β : Type u} : (α ⟶ β) = (α → β) := by
  rfl

end Rfl
