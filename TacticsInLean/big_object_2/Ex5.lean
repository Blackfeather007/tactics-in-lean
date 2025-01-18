import Mathlib.Tactic
import Mathlib.Logic.Function.Basic
import Mathlib.Topology.Separation.Basic
import Init
import Mathlib.Topology.Bases

open Function

  ------------------------------------------------------------
  ------------------------ 第二次大作业------------------------
  -- 小 组 成 员 : 丁博洋 黄瑞转 吴与同 张腾裕
  -- 对 应 习 题 : 点集拓扑部分7.1
  ------------------------------------------------------------

/-
  定义：给定拓扑空间X，Y，以及函数f : X → Y，
  f 是Homeomorphic，当且仅当：
  存在 g: Y → X，使得gf = id 以及fg = id，并且f与g均连续。
-/
def Homeomorphic {X Y : Type*}[TopologicalSpace X][TopologicalSpace Y](f : X → Y) : Prop :=
  ∃ (g : Y → X), (∀ x, g (f x) = x) ∧ (∀ y, f (g y) = y) ∧ Continuous f ∧ Continuous g

/-
  主定理：若X是紧空间(compact)，Y是Hausdorff空间(T₂)，
  且f: X → Y 连续且双射，那么f是同胚。
-/

theorem con_bij_compact_T2Space_is_homeo  {X Y : Type*}[TopologicalSpace X][CompactSpace X][TopologicalSpace Y] [T2Space Y]{f : X → Y}(hf_cont : Continuous f)(hf_bij : Bijective f) : Homeomorphic f := by
  let e := Equiv.ofBijective f hf_bij     -- e : X ≃ Y
  let g := e.symm                         -- 即 g = f⁻¹
  use g
  /-现在要证明：(∀ x, g(f x)=x) ∧ (∀ y, f(g y)=y) ∧ Continuous f ∧ Continuous g
    用 refine 一次性凑齐组装一个 ∧ 的大式子-/
  refine ⟨(fun x => e.symm_apply_apply x),   -- g(f x)=x
    (fun y => e.apply_symm_apply y),   -- f(g y)=y
    hf_cont,                           -- f 连续
    ?_⟩
  ------------------------------------------------------------
  -- 第 3 步：证明g连续: 使用“f 是闭映射 => f⁻¹ 连续”
  ------------------------------------------------------------
  have f_closed_map : IsClosedMap f := by
    apply Continuous.isClosedMap
    · exact hf_cont  -- f 连续
  have left_inv : LeftInverse g f := fun x => e.symm_apply_apply x
  have right_inv : RightInverse g f := fun y => e.apply_symm_apply y
  exact Continuous.continuous_symm_of_equiv_compact_to_t2 hf_cont


  ------------------------------------------------------------
  -- 优化简洁版 ：对上方代码的压行结果
  ------------------------------------------------------------
theorem con_bij_compact_T2Space_is_homeo' {X Y:Type*}[TopologicalSpace X][CompactSpace X][TopologicalSpace Y][T2Space Y]{f : X →Y}(hf_cont : Continuous f)(hf_bij : Bijective f) : Homeomorphic f := by
  exact ⟨ (Equiv.ofBijective f hf_bij).symm, ⟨fun x => (Equiv.ofBijective f hf_bij).symm_apply_apply x, fun y => (Equiv.ofBijective f hf_bij).apply_symm_apply y,
  hf_cont, Continuous.continuous_symm_of_equiv_compact_to_t2 hf_cont⟩⟩


  ------------------------------------------------------------
  -- 强化简洁版 ：直接使用Lean 4 中的IsHomeomorph theorem
  ------------------------------------------------------------
theorem con_bij_compact_T2Space_is_homeo'' {X Y:Type*}[TopologicalSpace X][CompactSpace X][TopologicalSpace Y][T2Space Y]{f : X → Y}(hf_cont : Continuous f)(hf_bij : Bijective f) : IsHomeomorph f := by
  exact isHomeomorph_iff_continuous_bijective.mpr ⟨hf_cont, hf_bij⟩
