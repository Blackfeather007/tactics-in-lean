import Mathlib.Tactic

structure ZOmega where
  a : ℤ
  b : ℤ

def ZOmega.add (x y : ZOmega) : ZOmega :=
  { a := x.a + y.a, b := x.b + y.b }

def ZOmega.mul (x y : ZOmega) : ZOmega :=
  { a := x.a * y.a - x.b * y.b, b := x.a * y.b + x.b * y.a - x.b * y.b }

def ZOmega.zero : ZOmega :=
  { a := 0, b := 0 }

def ZOmega.one : ZOmega :=
  { a := 1, b := 0 }

def ZOmega.neg (x : ZOmega) : ZOmega :=
  { a := -x.a, b := -x.b }

def ZOmega.nsmul (n : ℕ) (x : ZOmega) : ZOmega :=
  if _ : n = 0 then ZOmega.zero
  else x.add (ZOmega.nsmul (n - 1) x)

def ZOmega.nsmul' (n : ℕ) (x : ZOmega) : ZOmega :=
  match n with
  | 0 => .zero
  | k + 1 => (ZOmega.nsmul' k x).add x -- 注意不要是x.add (ZOmega.nsmul' k x)

def ZOmega.zsmul' (n : ℤ) (x : ZOmega) : ZOmega :=
  match n with
  | .ofNat m => ZOmega.nsmul' m x
  | .negSucc m => (ZOmega.nsmul' (m + 1) x).neg

namespace ZOmega

-- theorem add_comm' (x y : ZOmega)
instance : AddCommGroup ZOmega where
  add := ZOmega.add
  add_assoc := by
    intro x y z
    have h1 : (x.add y).add z = { a := (x.a + y.a) + z.a, b := (x.b + y.b) + z.b } := rfl
    have h2 : x.add (y.add z) = { a := x.a + (y.a + z.a), b := x.b + (y.b + z.b) } := rfl
    show (x.add y).add z = x.add (y.add z)
    rw [h1, h2]
    apply congr_arg₂ ZOmega.mk
    exact Int.add_assoc x.a y.a z.a
    exact Int.add_assoc x.b y.b z.b
  zero := ZOmega.zero
  zero_add := by
    intro x
    have h : ZOmega.zero.add x = { a := 0 + x.a, b := 0 + x.b } := rfl
    show ZOmega.zero.add x = x
    rw [h]
    apply congr_arg₂ ZOmega.mk
    exact Int.zero_add x.a
    exact Int.zero_add x.b
  add_zero := by
    intro x
    have h : x.add ZOmega.zero = { a := x.a + 0, b := x.b + 0 } := rfl
    show x.add ZOmega.zero = x
    rw [h]
    apply congr_arg₂ ZOmega.mk
    exact Int.add_zero x.a
    exact Int.add_zero x.b
  nsmul := ZOmega.nsmul'
  nsmul_zero := by
    intro x
    unfold nsmul'
    rfl
  nsmul_succ := by
    intro n x
    rw [nsmul']
    rfl
  neg := .neg
  sub := sorry
  sub_eq_add_neg := sorry
  zsmul := .zsmul'
  zsmul_zero' a := rfl
  zsmul_succ' := by
    intro n a
    rw [zsmul'.eq_def, zsmul'.eq_def]
    rfl
  zsmul_neg' := by
    intro n a
    unfold zsmul'
    simp
  neg_add_cancel := sorry
  add_comm := sorry


end ZOmega


def ZOmega.zsmul (n : ℤ) (x : ZOmega) : ZOmega :=
  if _ : n = 0 then ZOmega.zero
  else if _ : n > 0 then ZOmega.nsmul n.toNat x
  else ZOmega.neg (ZOmega.nsmul (-n).toNat x)

theorem ZOmega.add_comm (x y : ZOmega) : x.add y = y.add x := by
    have h1 : x.add y = { a := x.a + y.a, b := x.b + y.b } := rfl
    have h2 : y.add x = { a := y.a + x.a, b := y.b + x.b } := rfl
    show x.add y = y.add x
    rw [h1, h2]
    apply congr_arg₂ ZOmega.mk
    exact Int.add_comm x.a y.a
    exact Int.add_comm x.b y.b

theorem ZOmega.add_assoc (x y z : ZOmega ) : (x.add y).add z = x.add (y.add z) := by
    have h1 : (x.add y).add z = { a := (x.a + y.a) + z.a, b := (x.b + y.b) + z.b } := rfl
    have h2 : x.add (y.add z) = { a := x.a + (y.a + z.a), b := x.b + (y.b + z.b) } := rfl
    show (x.add y).add z = x.add (y.add z)
    rw [h1, h2]
    apply congr_arg₂ ZOmega.mk
    exact Int.add_assoc x.a y.a z.a
    exact Int.add_assoc x.b y.b z.b

instance : AddCommGroup ZOmega where
  add := ZOmega.add
  zero := ZOmega.zero
  neg := ZOmega.neg
  nsmul := ZOmega.nsmul
  zsmul := ZOmega.zsmul
  nsmul_zero := by
    intro x
    rw [ZOmega.nsmul, dif_pos (rfl : 0 = 0)]
    exact rfl
  nsmul_succ := by
    intro n x
    rw [ZOmega.nsmul, dif_neg (Nat.zero_ne_add_one _).symm, Nat.add_sub_cancel_right]
    rw [ZOmega.add_comm]
    exact rfl
  zsmul_succ' := by
    intro n a
    -- unfold ZOmega.zsmul

    sorry
  zsmul_neg' := by

    sorry
  add_assoc := ZOmega.add_assoc
  zero_add := by
    intros x
    have h : ZOmega.zero.add x = { a := 0 + x.a, b := 0 + x.b } := rfl
    show ZOmega.zero.add x = x
    rw [h]
    apply congr_arg₂ ZOmega.mk
    exact Int.zero_add x.a
    exact Int.zero_add x.b
  add_zero := by
    intros x
    have h : x.add ZOmega.zero = { a := x.a + 0, b := x.b + 0 } := rfl
    show x.add ZOmega.zero = x
    rw [h]
    apply congr_arg₂ ZOmega.mk
    exact Int.add_zero x.a
    exact Int.add_zero x.b
  add_comm := ZOmega.add_comm
  neg_add_cancel:= by
    intros x
    have h : ZOmega.add (ZOmega.neg x) x = { a := (-x.a) + x.a, b := (-x.b) + x.b } := rfl
    show ZOmega.add (ZOmega.neg x) x = ZOmega.zero
    rw [h]
    apply congr_arg₂ ZOmega.mk
    exact Int.add_left_neg x.a
    exact Int.add_left_neg x.b

instance : MulOneClass ZOmega where
  mul := ZOmega.mul
  one := ZOmega.one
  one_mul := by
    intros x
    have h : ZOmega.one.mul x = { a := 1 * x.a - 0 * x.b, b := 1 * x.b + 0 * x.a - 0 * x.b } := rfl
    show ZOmega.one.mul x = x
    rw [h]
    apply congr_arg₂ ZOmega.mk
    simp [Int.mul_one, Int.zero_mul]
    simp [Int.mul_one, Int.zero_mul]
  mul_one := by
    intros x
    have h : x.mul ZOmega.one = { a := x.a * 1 - x.b * 0, b := x.a * 0 + x.b * 1 - x.b * 0 } := rfl
    show x.mul ZOmega.one = x
    rw [h]
    apply congr_arg₂ ZOmega.mk
    simp [Int.mul_one, Int.zero_mul]
    simp [Int.mul_one, Int.zero_mul]

instance : Distrib ZOmega where
  left_distrib := by
    intros x y z
    have h1 : x.mul (y.add z) = { a := x.a * (y.a + z.a) - x.b * (y.b + z.b), b := x.a * (y.b + z.b) + x.b * (y.a + z.a) - x.b * (y.b + z.b) } := rfl
    have h2 : ZOmega.add (x.mul y) (x.mul z) = { a := (x.a * y.a - x.b * y.b) + (x.a * z.a - x.b * z.b), b := (x.a * y.b + x.b * y.a - x.b * y.b) + (x.a * z.b + x.b * z.a - x.b * z.b) } := rfl
    show x.mul (y.add z) = ZOmega.add (x.mul y) (x.mul z)
    rw [h1, h2]
    apply congr_arg₂ ZOmega.mk
    ring
    ring
  right_distrib := by
    intros x y z
    have h1 : (x.add y).mul z = { a := (x.a + y.a) * z.a - (x.b + y.b) * z.b, b := (x.a + y.a) * z.b + (x.b + y.b) * z.a - (x.b + y.b) * z.b } := rfl
    have h2 : ZOmega.add (x.mul z) (y.mul z) = { a := (x.a * z.a - x.b * z.b) + (y.a * z.a - y.b * z.b), b := (x.a * z.b + x.b * z.a - x.b * z.b) + (y.a * z.b + y.b * z.a - y.b * z.b) } := rfl
    show (x.add y).mul z = ZOmega.add (x.mul z) (y.mul z)
    rw [h1, h2]
    apply congr_arg₂ ZOmega.mk
    ring
    ring

instance : CommRing ZOmega where
  add := ZOmega.add
  zero := ZOmega.zero
  neg := ZOmega.neg
  mul := ZOmega.mul
  one := ZOmega.one
  nsmul := ZOmega.nsmul
  zsmul := ZOmega.zsmul
  add_comm := by exact fun a b ↦ add_comm a b
  add_assoc := by exact fun a b c ↦ add_assoc a b c
  zero_add := by exact fun a ↦ zero_add a
  add_zero := by exact fun a ↦ add_zero a
  neg_add_cancel := by
    exact fun a ↦ neg_add_cancel a
  nsmul_zero := by
    intro x
    rw [ZOmega.nsmul, dif_pos (rfl : 0 = 0)]
    exact rfl
  nsmul_succ := by
    intro n x
    rw [ZOmega.nsmul, dif_neg (Nat.zero_ne_add_one _).symm, Nat.add_sub_cancel_right]
    rw [ZOmega.add_comm]
    exact rfl
  zsmul_succ' := by

    sorry
  zsmul_neg' := by
    sorry
  zero_mul := by
    sorry
  mul_zero := by

    sorry
  mul_assoc := by
    intros x y z
    have h1 : (x.mul y).mul z = { a := (x.a * y.a - x.b * y.b) * z.a - ((x.a * y.b + x.b * y.a - x.b * y.b) * z.b), b := (x.a * y.a - x.b * y.b) * z.b + ((x.a * y.b + x.b * y.a - x.b * y.b) * z.a) - ((x.a * y.b + x.b * y.a - x.b * y.b) * z.b) } := rfl
    have h2 : x.mul (y.mul z) = { a := x.a * (y.a * z.a - y.b * z.b) - (x.b * (y.a * z.b + y.b * z.a - y.b * z.b)), b := x.a * (y.a * z.b + y.b * z.a - y.b * z.b) + (x.b * (y.a * z.a - y.b * z.b)) - (x.b * (y.a * z.b + y.b * z.a - y.b * z.b)) } := rfl
    show (x.mul y).mul z = x.mul (y.mul z)
    rw [h1, h2]
    apply congr_arg₂ ZOmega.mk
    ring
    ring
  one_mul := MulOneClass.one_mul
  mul_one := MulOneClass.mul_one
  left_distrib := Distrib.left_distrib
  right_distrib := Distrib.right_distrib
  mul_comm := by
    intros x y
    have h1 : x.mul y = { a := x.a * y.a - x.b * y.b, b := x.a * y.b + x.b * y.a - x.b * y.b } := rfl
    have h2 : y.mul x = { a := y.a * x.a - y.b * x.b, b := y.a * x.b + y.b * x.a - y.b * x.b } := rfl
    show x.mul y = y.mul x
    rw [h1, h2]
    apply congr_arg₂ ZOmega.mk
    ring
    ring
