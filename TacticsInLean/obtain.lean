import Mathlib.Tactic
import Mathlib.Algebra.Module

section Obtain

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

universe u
variable {R : Type u} [CommRing R]
variable {ι : Type u}
variable {N : ι → Type u} [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]
variable {M : Type u} [AddCommGroup M] [Module R M]

-- noncomputable def test  [Module.FinitePresentation R M] : Module.FinitePresentation R M := by
--   have hfpB : Module.FinitePresentation R M := inferInstance
--   obtain ⟨L, hL, fL, K, hK, hFree, hFinite, hFG⟩ := Module.FinitePresentation.equiv_quotient R M
--   sorry

lemma test  [Module.FinitePresentation R M] : Module.FinitePresentation R M := by
  have hfpB : Module.FinitePresentation R M := inferInstance
  obtain ⟨L, hL, fL, K, hK, hFree, hFinite, hFG⟩ := Module.FinitePresentation.equiv_quotient R M
  sorry

end Obtain
