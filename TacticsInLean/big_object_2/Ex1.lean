import Mathlib.Tactic
import Mathlib.Data.Matrix.Rank
/-
基域 R 上的 n × n 任意矩阵 A, 证明:Rank A = Rank Aᵀ A
-/

section t1

end t1

variable (a b : ℕ) (h : a < 0)

example : True := by
  #check a
  have := h

  sorry


include h
theorem t₁ : True := by

  trivial

theorem t₂ : a < b := by

  have := h
  sorry




variable (n : ℕ)--声明矩阵的维数
variable (A : Matrix (Fin n) (Fin n) ℝ)--声明矩阵


example (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) : A.rank = (A * A.transpose ).rank := by
sorry


example (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) : (A * A.transpose ).rank = A.rank := by
sorry

variable(A_transpose := A.transpose) --声明矩阵Aᵀ

variable (x : Nat := 1)
def add (y : Nat) := x + y

#eval add 2 1

def A_transpose' : Matrix (Fin n) (Fin n) ℝ := A.transpose

#check A_transpose

#check A_transpose'


variable(Zero_vec : Matrix (Fin n) (Fin 1) ℝ := 0)

example : A.rank = (A * A_transpose ).rank := by
sorry

--必要的引理
theorem Non_negative {a : Matrix (Fin n) (Fin 1) ℝ} : a.transpose * a = !![0] ↔ a = Zero_vec := by sorry

#check Non_negative

theorem Zero_mul {B : Matrix (Fin n) (Fin n) ℝ} :
B * Zero_vec =Zero_vec := by sorry

lemma Zero_mul' (B : Matrix (Fin 1) (Fin n) ℝ) :
B * Zero_vec =!![0]:= by sorry

theorem Mul_Same {α β  : Matrix (Fin n) (Fin 1) ℝ} ( C : Matrix (Fin 1) (Fin n) ℝ  ) ( h: α = β) : C * α  = C * β  := by sorry


theorem Samerank  (A B: Matrix (Fin n) (Fin n) ℝ)
(h :∀ a : Matrix (Fin n) (Fin 1) ℝ
,A * a = Zero_vec ↔ B * a = Zero_vec)
: A.rank = B.rank := by sorry

theorem Sameroot  :
∀ a : Matrix (Fin n) (Fin 1) ℝ ,
∀ B : Matrix (Fin n) (Fin n) ℝ ,
B * a = Zero_vec ↔ B.transpose * B * a = Zero_vec := by
 intro a A
 constructor
 ·intro h
  rw [ Matrix.mul_assoc ]
  rw [ h ]
  apply Zero_mul
 ·intro h1
  have h2 : a.transpose * (A.transpose * A * a) = a.transpose * Zero_vec := by
    exact Mul_Same n a.transpose h1
  rw [ Matrix.mul_assoc ] at h2
  rw [ ← Matrix.mul_assoc ] at h2
  rw [ ← Matrix.transpose_mul ] at h2
  conv at h2 =>
    enter [2]
    apply Zero_mul'
  exact (Non_negative n Zero_vec).1 h2


theorem main : A.rank = ( A.transpose * A).rank := by

 have h :
  ∀ a : Matrix (Fin n) (Fin 1) ℝ ,
  ∀ B : Matrix (Fin n) (Fin n) ℝ ,
  B * a = Zero_vec ↔ B.transpose * B * a = Zero_vec  := by
   exact fun a B ↦ Sameroot n Zero_vec a B


 have h2 :∀ (a : Matrix (Fin n) (Fin 1) ℝ) , A * a = Zero_vec ↔ A.transpose * A * a = Zero_vec := by
  exact fun a ↦ h a A

 apply Samerank n Zero_vec

 exact h2
