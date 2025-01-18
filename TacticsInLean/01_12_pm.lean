import Mathlib.Tactic

section cases -- 假设 x 是局部上下文环境中一个具有归纳类型的变量，cases x 将主进程拆分，为归纳类型的每个构造子生成一个子进程。在这些子进程中，目标会被一个通用实例替换。如果局部上下文环境中有一个元素的类型依赖于 x ，该元素会被还原之后再重新引入。正因如此，case 的拆分也会影响到某些假设。此外，cases 还会检测那些无法访问的案例情况并自动关闭它们。

open Nat

-- 如下举例，给定一个自然数 n ，已知假设 h : P n 和要证的目标 Q n，cases n 会产生两个子进程，一个带有假设 h : P 0 和目标 Q 0 , 另一个带有假设 h : P (n✝ + 1) 和目标 Q (n✝ + 1) 。这里的通用实例 n✝ 是自动选取的且无法被直接访问或使用，你可以使用 with 为每个构造子提供单独的变量名。
example (n : ℕ) (P Q : ℕ → Prop) (h : P n) : Q n := by
  cases n

  sorry
  sorry

-- 你可以在任意表达式上使用 cases 。cases e ，其中 e 是一个表达式而非变量名，假设该表达式出现在目标中，则 cases e 将对该表达式进行泛化，引入结果中的全称量化变量，并对其进行分解。
example (p : Nat → Prop) (hz : p 0) (hs : ∀ n, p (succ n)) (m k : Nat)
        : p (m + 3 * k) := by
  cases m + 3 * k
  exact hz   -- goal is p 0
  apply hs   -- goal is a : Nat ⊢ p (succ a)

-- 可以将其理解为根据 m + 3 * k 是零还是某个数字的后继来进行分解。其结果在功能上等价于以下内容：
example (p : Nat → Prop) (hz : p 0) (hs : ∀ n, p (succ n)) (m k : Nat)
        : p (m + 3 * k) := by
  generalize m + 3 * k = n
  cases n
  exact hz   -- goal is p 0
  apply hs   -- goal is a : Nat ⊢ p (succ a)

-- 如果你分解的表达式没有出现在目标中，那么 cases 策略将把该表达式的类型加入到上下文中。以下是一个例子：
example (p : Prop) (m n : Nat)
        (h₁ : m < n → p) (h₂ : m ≥ n → p) : p := by

  cases Nat.lt_or_ge m n
  case inl hlt => exact h₁ hlt
  case inr hge => exact h₂ hge

-- 这是另一个例子，其中我们使用自然数相等性的可判定性来分解 m = n 和 m ≠ n 两种情况。
example (m n : Nat) : m - n = 0 ∨ m ≠ n := by
  cases Decidable.em (m = n) with
  | inr _ => apply Or.inr; tauto
  | inl heq => rw [heq]; apply Or.inl; exact Nat.sub_self n


#check Or

-- 给定 as : List α ，cases as with nil => tac₁ | cons a as' => tac₂ ，针对 nil 的情形使用 tac₁ 的策略，针对 cons 的情形使用 tac₂ 的情形，并且 a 和 as 被用作新引入的变量的名字。

-- cases h : e ，其中 e 是一个变量或一个表达式，则 cases h : e 同理上对 e 进行拆分，但同时对每一个子进程添加了一个假设 h : e = ... ，其中 ... 是那个特定子进程下 e 的构造子实例。

-- 注意，cases 不仅可以用来证明命题，也可以用来生成数据。
def f (n : Nat) : Nat := by
  cases n
  use 3
  use 7

-- def f' : Nat → Nat := fun a ↦ (if a = 0 then 3 else 7)

example : f 0 = 3 := rfl
example : f 5 = 7 := rfl

-- 值得再次强调的是，cases 将撤回、分解，并随后重新引入上下文中的依赖项。
def Tuple (α : Type) (n : Nat) : Type :=
  { as : List α // as.length = n }

def f' {α : Type} {n : Nat} (t : Tuple α n) : Nat := by
  cases n
  exact 3
  exact 7


-- example (f₁₁ : Nat → Prop) (n : ℕ) (h : ∀ n , f n) : 1 = 1 := by
--   sorry

def myTuple : Tuple Nat 3 :=
  ⟨[0, 1, 2], rfl⟩

example : f' myTuple = 7 :=
  rfl

-- 下面是一个含多个带参数的构造子的例子：
inductive Foo where
  | bar1 : Nat → Nat → Foo
  | bar2 : Nat → Nat → Nat → Foo

def silly (x : Foo) : Nat := by
  cases x with
  | bar2 c d e => exact d
  | bar1 a b => exact b


-- 值得注意的是，每个构造子的替代项并不需要按照构造子声明的顺序进行求解，比如你也可以这样：
def silly' (x : Foo) : Nat := by
  cases x with
  | bar2 c d e => exact e
  | bar1 a b => exact b

-- with 语法非常方便，适用于编写结构化证明。除此之外 Lean 还提供了一种补充的 case 策略，允许你专注于为目标分配变量名称
def silly'' (x : Foo) : Nat := by
  cases x
  case bar1 a b => exact b
  case bar2 c d e => exact e

-- cases' 作用和实现效果与 cases 相近，但语义不同。cases' 是一种通用策略，用于解构假设。如果 h 是一个以某种方式捆绑了两条信息的假设，那么 cases' h with h1 h2 将使假设 h 消失，并用最初构成 h 证明的两个组成部分替代它。

/-
(a) 得到一个 P ∧ Q 的证明的方法是同时使用 P 和 Q 的证明。如果你有一个假设 h : P ∧ Q ，则 cases' h 将删除假设 h ，并用 left✝ : P 和 right✝ : Q 替代。注意，这些名字中的奇怪的“匕首”符号意味着你不能显式地使用这些假设！更好的方式是输入 cases' h with hP hQ 。
(b) 得到一个 P ↔ Q 的证明的方法是同时使用 P → Q 和 Q → P 的证明。因此，当面对 h : P ↔ Q 时，你可以使用cases' h with hPQ hQP ，这样 h 会被删除，并用 hPQ: P → Q 和 hQP: Q → P 替代。然而，请注意，这可能不是最好的做法；尽管你可以使用 hPQ 和 hQP ，你失去了用 rw [h] 重写 h 的能力。如果你真的想解构 h ，但又想保留一个副本以供以后重写，你可以尝试 have h2 := h ，然后再执行 cases' h with hPQ hQP。
(c) 证明 P ∨ Q 有两种方法。你要么使用 P 的证明，要么使用 Q 的证明。因此，如果 h : P ∨ Q ，那么 cases' h with hP hQ会与前两个例子有不同的效果；在这个策略执行后，你将得到两个进程，其中一个包含新的假设 hP : P ，另一个包含 hQ : Q 。可以这样理解，Or 归纳类型有两个构造子，而 And 只有一个。
(d) 证明自然数 n 有两种方法。每个自然数要么是 0 ，要么是某个自然数 m 的后继 succ m 。因此，如果 n : N ，那么 cases' n with m 会产生两个目标；一个目标中 n 被替换为 0 ，另一个目标中 n 被替换为 succ m 。注意，这是 induction 策略的一个严格较弱的版本，因为 cases' 不会给我们归纳假设。
(e) 如果你有一个假设 h : ∃ a, a³ + a = 37 ，那么 cases' h with x hx 会给你一个数字 x 和一个证明 hx : x³ + x = 37
-/

example (h : ∃ a : ℕ , a ^ 3 + a = 37) : ∃ x : ℕ , x ^ 3 + x = 37 := by
  cases' h with x hx
  /-
  Tactic state
  1 goal
  case intro
  x : ℕ
  hx : x ^ 3 + x = 37
  ⊢ ∃ x, x ^ 3 + x = 37
  -/
  use x

-- 注意，∧ 是右结合的：P ∧ Q ∧ R 表示 P ∧ (Q ∧ R) 。因此，如果 h : P ∧ Q ∧ R ，那么 cases' h with h1 h2 会给你 h1 : P 和 h2 : Q ∧ R，然后你必须执行 cases' h2 来得到 Q 和 R 的证明。注意，cases' h with h1 h2 h3 并不起作用（h3 会被忽略）。

variable (p q r : Prop)
example (h : p ∧ q ∧ r) : q := by
  cases' h with h1 h2
  cases' h2 with h3 h4
  exact h3

-- 分别用cases和cases'证明的例子
example (h : p ∨ q) : q ∨ p := by
  cases h with
  | inl hp => exact Or.inr hp
  | inr hq => exact Or.inl hq

example (h : p ∨ q) : q ∨ p := by
  cases' h with hp hq
  · exact Or.inr hp
  · exact Or.inl hq

-- ps：除了 cases 和 cases' 之外，其实还有 cases_type ，cases_type！ 和 casesm 等小众且并不实用的 tactic ，此处仅作列举，感兴趣者可以自行了解。
end cases

section rcases -- rcases 策略可以在一行中执行多个 cases' 策略。它还可以通过 rfl 技巧进行某些变量替换。

-- 如果给定一个 ε : ℝ 和一个假设 h : ∃ δ > 0, δ^2 = ε ，那么你可以使用 cases' 策略将 h 分解，例如，你可以这样做：
example (ε : ℝ) (h : ∃ δ > 0 , δ ^ 2 = ε) : ε < 0.1 := by
  cases' h with δ h1 -- h1: δ > 0 ∧ δ ^ 2 = ε
  cases' h1 with hδ h2
  sorry

-- 然而，你可以通过以下一行代码使用 rcases 策略直接得到该状态：
example (ε : ℝ) (h : ∃ δ > 0 , δ ^ 2 = ε) : ε < 0.1 := by
  rcases h with ⟨δ, hδ, h2⟩
  sorry

-- 实际上，你可以做得更好。假设 h2 可以作为 ε 的定义或公式，而 rcases 策略还有一个额外的技巧，能够完全从策略状态中移除 ε ，并将其所有出现的地方都替换为 δ ^ 2 。你可以不再调用假设 h2 ，而是输入 rfl 。这将起到处处调用 rw [← h2] 的效果，从而将所有的 ε 替换为 δ ^ 2 。如果你的策略状态包含以下内容：
example (ε : ℝ) (h : ∃ δ > 0 , δ ^ 2 = ε) : ε < 0.1 := by
  rcases h with ⟨δ, hδ, rfl⟩
  sorry

-- 如果给定假设 h : P ∧ Q ∧ R ，那么 rcases h with ⟨hP, hQ, hR⟩ 直接将 h 分解为 hP : P 、hQ : Q 和 hR : R。同样，如果使用 cases' 策略来完成将需要两步。
variable {p q r : Prop}
example (h : p ∧ q ∧ r) : p := by
  rcases h with ⟨ hp, hq, hr⟩
  exact hp

-- 如果 h : P ∨ Q ∨ R ，则使用 rcases h with (hP | hQ | hR) 将目标分解为三个目标，一个包含 hP : P ，一个包含 hQ : Q，另一个包含 hR : R。同样，使用 cases' 策略需要两步才能完成这项操作。注意：对于 ∧ 和 ∨的语法是不同的，因为对 ∨ 进行 cases 操作会将一个目标转化为两个（因为归纳类型 Or 有两个构造子）。例子如下所示：
example (a b c d : Prop) (h1 : a ∧ b ∧ c ∨ d) (h2 : a ∧ b ∨ c ∧ d) : 1 = 1 := by
  rcases h1 with ⟨ha, hb, hc⟩ | hd
  rcases h2 with ⟨ha', hb'⟩ | ⟨hc', hd'⟩
  repeat simp

/-
更具体地，rcases 策略的每个模式元素都会与特定的局部假设进行匹配（这些假设大多在执行 rcases 时生成，并表示从输入表达式中解构出的各个元素）。rcases 模式具有以下语法：
• 一个名称，例如 x，将活动假设命名为 x。
• 一个空白 _，表示不做任何操作（让 cases 使用自动命名系统为假设命名）。
• 一个连字符 -，清除活动假设及其所有依赖项。
• 关键字 rfl，期望假设为 h : a = b，并对该假设调用 subst（这会在所有地方将 b 替换为 a，或反之亦然）。
• 类型限定符 p : ty，将假设的类型设置为 ty，然后将其与 p 匹配。（当然，ty 必须与 h 的实际类型统一才能起作用。）
• 元组模式 ⟨p1, p2, p3⟩，用于匹配具有多个参数的构造子，或一系列嵌套的合取或存在量词。例如，如果活动假设为 a ∧ b ∧ c，那么合取会被解构，p1 会匹配 a，p2 匹配 b，依此类推。
• 在元组模式前加上 @，如 @⟨p1, p2, p3⟩，会绑定构造子中的所有参数，而不加 @ 则只使用显式参数上的模式。
• 一个选择模式 p1 | p2 | p3，用于匹配具有多个构造子的归纳类型，或像 a ∨ b ∨ c 这样的嵌套析取。
一个像 ⟨a, b, c⟩|⟨d, e⟩ 的模式，会对归纳数据类型进行分割，将第一个构造子的前三个参数命名为 a、b、c，将第二个构造子的前两个参数命名为 d 和 e。如果列表的长度不如构造子的参数个数，剩余的变量将自动命名。如果存在嵌套括号，比如 ⟨⟨a⟩, b|c⟩|d，则会根据需要进行更多的分割。如果参数过多，例如对于 ∃x, ∃y, px 分割时使用⟨a, b, c⟩，则会将其视为 ⟨a, ⟨b, c⟩⟩，并根据需要分割最后一个参数。
特别的，rcases 还支持商类型：在 Prop 中的商归纳与匹配构造子 quot.mk 类似。
rcases h : e with PAT 的效果与 rcases e with PAT 相同，唯一的不同是，假设 h : e = PAT 会被添加到上下文中。这一点与 cases 类似。
其他使用 ⟨hP, hQ, hR⟩ 或 (hP | hQ | hR) 语法的策略包括 rintro 策略（intro + rcases）和 obtain 策略（have + rcases）。下面我们就来介绍它们。
-/
end rcases



section rintro -- rintro 策略是 intros 策略与 rcases 策略的结合，允许在引入变量的同时解构模式。有关支持的模式，请参见 rcases 。例如，rintro (a | ⟨b, c⟩) ⟨d, e⟩ 会引入两个变量，然后对这两个变量进行案例分割，生成两个子目标，一个包含变量 a, d, e，另一个包含变量 b, c, d, e。

-- 与 rcases 不同，rintro 还支持形式 (xy : ty)，用于一次性引入并进行类型限定多个变量，类似于限制器。

variable {p q r s : Prop}
-- 你可以使用以下策略
example : p → (q ∧ r) → s := by
  intro hP
  intro h
  cases' h with hQ hR
  sorry

-- 然而，一种一行就可以解决的方式是
example : p → (q ∧ r) → s := by
  rintro hP ⟨hQ, hR⟩
  sorry

-- 策略 rintro (hP | hQ) 相当于先 intro h 然后 cases' h with hP hQ 。特别地，在应用此策略后，将会生成两个目标，一个包含假设 hP : P ，另一个包含假设 hQ : Q。请注意，对于“或”类型的目标，使用的是圆括号
example : (p ∨ q) → r := by
  rintro (hP | hQ)
  sorry
  sorry

-- 和 rcases 一样，rintro 策略有一个 rfl 彩蛋。当然你可以使用如下策略解决它
example {a b : ℕ} : a = 2 * b → 2 * a = 4 * b := by
  intro h
  rw [h]
  ring

-- 但有一个技巧：rintro rfl 会将目标中的假设 a = 2 × b 进行处理，而不是将其作为假设加入到策略状态中。相反，它会定义 a 为 2 × b，并将目标保持为 ⊢ 2 * (2 * b) = 4 * b, 接下来只需要使用 ring 就可以轻松解决这个问题。
example {a b : ℕ} : 2 * b = a → 2 * a = 4 * b := by
  rintro rfl
  ring

-- 请注意，rintro 与 intro 一样，适用于定义等价的情况。例如，如果目标状态是 ⊢ ¬P ，那么 rintro hP 是完全可以的（因为 ⊢ ¬P 在定义上等价于 P → False），这时策略状态会变为
example : ¬ p := by
  rintro hP
  sorry

-- 另一个适用定义等价的例子如下：
example : ∀ m n : Nat, Even n → Even (m * n) := by
  -- Say `m` and `n` are natural numbers, and assume `n = 2 * k`.
  rintro m n ⟨k, hk⟩
  -- We need to prove `m * n` is twice a natural number. Let's show it's twice `m * k`.
  use m * k
  -- Substitute for `n`,
  rw [hk]
  -- and now it's obvious.
  ring

-- 这里 Even n 在定义上等价于 ∃ k : Nat, n = k + k 。
end rintro



section obtain -- obtain 策略是 have 和 rcases 的结合。有关支持的模式，请参见 rcases 部分。obtain ⟨patt⟩ : type := proof等价于 have h : type := proof ; rcases h with ⟨patt⟩ 。若省略 ⟨patt⟩ ，则 Lean 将尝试自动推断模式，若省略 type ，则需要提供 := proof 。


example (h : ∀ ε > 0, ∃ (N : ℕ), (1 : ℝ) / (N + 1) < ε) : 1 = 1 := by
  have h2 := h 0.01 (by norm_num)
  /- specialize h 0.01 (by norm_num) -/
  cases' h2 with N hN
  /- rcases h2 with ⟨N, hN⟩ -/
  rfl

example (h : ∀ ε > 0, ∃ (N : ℕ), (1 : ℝ) / (N + 1) < ε) : 1 = 1 := by
  obtain ⟨N, hN⟩ := h 0.01 (by norm_num)
  rfl

-- 为了使代码更具可读性，你可以显式地声明 ⟨N, hN⟩ 的类型。在上述示例中，你可以写：
example (h : ∀ ε > 0, ∃ (N : ℕ), (1 : ℝ) / (N + 1) < ε) : 1 = 1 := by
  obtain ⟨N, hN⟩ : ∃ (N : ℕ), 1 / ((N + 1) : ℝ) < 0.01 := h 0.01 (by norm_num)
  rfl

-- 和 rcases 还有 rintro 一样，obtain 也遵循依定义等价。
end obtain




section induction -- 假设 x 是局部上下文中的一个变量，并且它具有一个归纳类型，induction x 会对主目标应用归纳法，生成一个goal来处理每个归纳类型的构造子。对于每个构造子，目标会被替换为该构造子的一个通用实例，并且为每个递归参数添加归纳假设。如果局部上下文中的某个元素的类型依赖于 x ，该元素会被回退并在归纳后重新引入，以便归纳假设能够包含该假设。

-- 例如，给定 n : Nat ，一个假设 h : P n 和目标 Q n ，induction n 会生成两个子目标：第一个目标包含假设 h : P 0 和目标 Q 0 ；第二个目标包含假设 h : P (Nat.succ a) 和归纳假设 ih₁ : P a → Q a ，目标为 Q (Nat.succ a) 。在这里，名字 a 和 ih₁ 是自动选择的，并且不可访问。你可以使用 with 来为每个构造子提供变量名称。

-- induction e ，当 e 是一个表达式而非变量时，首先将 e 在目标中推广为一个变量，然后对该变量应用归纳法。
namespace Hidden
theorem zero_add (n : Nat) : 0 + n = n := by
  induction n
  case zero => rfl
  case succ n ih => rw [Nat.add_succ, ih]
end Hidden

-- induction e using r 允许用户指定使用的归纳原理。这里的 r 应该是一个项，其返回值必须是 C t 的形式，其中 C 是一个约束变量，t 是一个（可能为空的）约束变量序列。
#check Nat.mod.inductionOn
example (x : Nat) {y : Nat} (h : y > 0) : x % y < y := by
  induction x, y using Nat.mod.inductionOn with
  | ind x y h₁ ih =>
    rw [Nat.mod_eq_sub_mod h₁.2]
    exact ih h
  | base x y h₁ =>
    have : ¬ 0 < y ∨ ¬ y ≤ x := Iff.mp (Decidable.not_and_iff_or_not ..) h₁
    match this with
    | Or.inl h₁ => exact absurd h h₁
    | Or.inr h₁ =>
      have hgt : y > x := Nat.gt_of_not_le h₁
      rw [← Nat.mod_eq_of_lt hgt] at hgt
      assumption

-- induction e generalizing z₁ ... zₙ ，其中 z₁ ... zₙ 是局部上下文中的变量，在应用归纳法之前会将这些变量一般化，然后在每个目标中重新引入它们。换句话说，最终效果是每个归纳假设都被泛化。
example (a b c : ℕ) (ha : a ≠ 0) (h : a * b = a * c) : b = c := by
  induction' b with d hd generalizing c
  · rw [mul_zero] at h
    have := mul_eq_zero.mp h.symm
    tauto
  · cases' c with e
    · rw [mul_zero] at h
      have := mul_eq_zero.mp h
      tauto
    · repeat rw [mul_add] at h
      rw [mul_one] at h
      let g := add_right_cancel h
      let h' := hd e g
      rw [h']

-- 给定 x : Nat ，induction x with | zero => tac₁ | succ x' ih => tac₂ 会对归纳类型的两种情况分别应用不同的策略：对于 zero 情况使用 tac₁，对于 succ 情况使用 tac₂。与 cases 一样，我们可以使用 case 策略来代替 with。通过使用 case 策略，我们可以逐一处理每个构造子，类似地，归纳法中的每个构造子也可以用 case 来处理。下面是一个例子：
open Nat

example (n : ℕ) : 0 < factorial n := by
    induction n
    case zero =>
      rw [factorial_zero]
      simp
    case succ n ih =>
      rw [factorial_succ]
      apply mul_pos (succ_pos n) ih

-- induction' 策略与 Lean 4 中的 induction 策略类似，但具有略微不同的语法（例如，不需要命名构造子）。
example (n : ℕ) : 0 < factorial n := by
  induction' n with n ih
  · rw [factorial_zero]
    simp
  · rw [factorial_succ]
    apply mul_pos (succ_pos n) ih

-- 我们介绍一个平方和公式的例子：
open BigOperators -- ∑ notation

open Finset -- so I can say `range n` for the finite set `{0,1,2,...,n-1}`

-- sum from i = 0 to n - 1 of i^2 is n(n-1)(2n-1)/6
-- note that I immediately coerce into rationals in the statement to get the correct subtraction and
-- division (natural number subtraction and division are pathological functions)
example (n : ℕ) : ∑ i in range n, (i : ℚ) ^ 2 = (n : ℚ) * (n - 1) * (2 * n - 1) / 6 := by
  induction' n with d hd
  · -- base case says that an empty sum is zero times something, and this sort of goal
    -- is perfect for the simplifier
    simp
  ·  -- inductive step
    rw [sum_range_succ] -- the lemma saying
                          -- `∑ i in range (n.succ), f i = (∑ i in range n, f i) + f n`
    rw [hd] -- the inductive hypothesis
    simp -- change `d.succ` into `d + 1`
    ring

-- 实际上， Lean 中对自然数的定义如下：
inductive Nat'
| zero : Nat'
| succ (n : Nat') : Nat'

-- 当这段代码执行时，会创建四个新对象：类型 Nat，项 Nat.zero，函数 Nat.succ : Nat → Nat ，以及自然数的递归器（recursor），这是一个从定义中自动生成的语句，可以描述为：为了对所有自然数做某件事，你只需要对零和succ n 做这件事，并且在 succ n 的情况下，你可以假设你已经对 n 做过这件事。归纳法策略应用这个递归器，并进行一些整理工作。这就是为什么你最终会得到包含 n.succ 的目标，而不是更符合数学自然写法的 n + 1 。在上面的例子中，我使用 simp 来将 n.succ 转换为 n + 1（同时也尽可能地将类型转换推得更远）。
end induction



section tactic_match -- match 执行对一个或多个表达式的 case 分析。match 策略的语法与 term 模式下的 match 相同，不同之处在于，策略 match 分支是策略而不是表达式。match 策略在语法上与 cases 相近，但 match 更为灵活，如下所示：

example (n : Nat) : n = n := by
  match n with
  | 0 => rfl
  | 1 => rfl
  | n + 2 => rfl

-- 再看一个更明显的例子，我们将使用 macth 表达式来定义一个从 Weekday 到自然数的函数：
inductive Weekday where
 | sunday : Weekday
 | monday : Weekday
 | tuesday : Weekday
 | wednesday : Weekday
 | thursday : Weekday
 | friday : Weekday
 | saturday : Weekday
open Weekday

def numberOfDay (d : Weekday) : Nat :=
  match d with
  | sunday    => 1
  | monday    => 2
  | tuesday   => 3
  | wednesday => 4
  | thursday  => 5
  | friday    => 6
  | saturday  => 7

#eval numberOfDay Weekday.sunday  -- 1
#eval numberOfDay Weekday.monday  -- 2
#eval numberOfDay Weekday.tuesday -- 3

inductive Bool' where
  | true
  | false

#check Bool'.true

-- 注意，match 表达式是通过在声明归纳类型时生成的递归器 Weekday.rec 来编译的。
set_option pp.all true
#print numberOfDay
-- ... numberOfDay.match_1
#print numberOfDay.match_1
-- ... Weekday.casesOn ...
#print Weekday.casesOn
-- ... Weekday.rec ...
#check @Weekday.rec

-- 当声明一个归纳数据类型时，可以使用 deriving Repr 来指示 Lean 生成一个将 Weekday 对象转换为文本的函数。这个函数由 #eval 命令用于显示 Weekday 对象。（当 structure 中没有命题字段时，deriving Repr 可省略）
-- inductive Weekday' where
--   | sunday
--   | monday
--   | tuesday
--   | wednesday
--   | thursday
--   | friday
--   | saturday
--   deriving Repr

-- open Weekday'

-- #eval tuesday   -- Weekday.tuesday

-- 我们可以定义从 Weekday 到 Weekday 的映射：
namespace Weekday
def next (d : Weekday) : Weekday :=
  match d with
  | sunday    => monday
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => saturday
  | saturday  => sunday

def previous (d : Weekday) : Weekday :=
  match d with
  | sunday    => saturday
  | monday    => sunday
  | tuesday   => monday
  | wednesday => tuesday
  | thursday  => wednesday
  | friday    => thursday
  | saturday  => friday

#eval next (next tuesday)      -- Weekday.thursday
#eval next (previous tuesday)  -- Weekday.tuesday

example : next (previous tuesday) = tuesday :=
  rfl

end Weekday

-- 我们如何证明一般定理 next (previous d) = d 对于任意 Weekday d 都成立？您可以使用 match 为每个构造子提供该命题的证明：
def next_previous (d : Weekday) : next (previous d) = d :=
  match d with
  | sunday    => rfl
  | monday    => rfl
  | tuesday   => rfl
  | wednesday => rfl
  | thursday  => rfl
  | friday    => rfl
  | saturday  => rfl

-- 当然，我们可以用一些技巧让这个更简洁：
def next_previous' (d : Weekday) : next (previous d) = d := by
  cases d <;> rfl

-- 值得注意的是，在命题-类型对应关系下，我们可以使用 match 来证明定理以及定义函数。换句话说，在命题-类型对应关系下，按情况证明是一种按情况定义的形式，其中“定义”的是一个证明，而不是一块数据。

-- match_scalars. 给定一个目标，该目标是类型为 M （其中 M 是一个加法交换单群）的等式，可以将目标的左边（LHS）和右边（RHS）解析为某些半环 R 上的 M 基的线性组合，并将目标简化为各个基对应的 R 系数的等式。例如，这将产生目标 ⊢ a * 1 + b * 1 = (b + a) * 1 ：
example {R M : Type*} [AddCommMonoid M] [Semiring R] [Module R M] (a b : R) (x : M) : a • x + b • x = (b + a) • x := by
  match_scalars
  sorry

-- 这将产生目标 ⊢ -2 * (a * 1) = a * (-2 * 1) ：
example {R M : Type*} [AddCommGroup M] [Ring R] [Module R M] (a : R) (x : M) :
      -(2:R) • a • x = a • (-2:ℤ) • x  := by
    match_scalars
    sorry

-- 这将产生两个目标 ⊢ a * (a * 1) + b * (b * 1) = 1 （来自 x 基）和 ⊢ a * -(b * 1) + b * (a * 1) = 0 （来自 y 基）
example {R M : Type*} [AddCommGroup M] [Ring R] [Module R M] (a b : R) (x y : M) : a • (a • x - b • y) + (b • a • y + b • b • x) = x := by
  match_scalars
  sorry
  sorry

-- match_scalars 战术产生的目标的标量类型是遇到的最大标量类型。例如，如果 ℕ 、ℚ 和一个特征为零的域 K 都作为标量出现，那么产生的目标将是关于 K 的等式。match_scalars 内部使用 push_cast 的变体来将其他类型中的标量解释为这种最大类型。如果遇到的标量类型的集合不是完全有序的（即对于所有的环 R ，S ，都满足 Algebra R S或 Algebra S R ），则 match_scalars 策略会失败。
end tactic_match

section tactic_show_term -- show_term tac 会运行 tac ，然后以 exact X Y Z 或 refine X ?_ Z 的形式打印生成的项（如果还有剩余的子目标）。（对于某些战术，打印的项可能不适合人类阅读。）

open BigOperators
open Finset
example (n : ℕ) : ∑ i in range n, (i : ℚ) ^ 2 = (n : ℚ) * (n - 1) * (2 * n - 1) / 6 := by
  induction' n with d hd
  · simp
  · rw [sum_range_succ]
    rw [hd]
    simp
    ring

end tactic_show_term
