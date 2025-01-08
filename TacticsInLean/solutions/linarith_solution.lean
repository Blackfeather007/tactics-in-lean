import Mathlib.Tactic

section linarith

/- Hint: try to use `lt_of_lt_of_le` and `add_lt_add` to prove it -/
example {a b c d : ℝ} (h1 : a < b) (h2 : b ≤ c) (h3 : c = d) : a + a < d + b := by
  refine add_lt_add ?_ h1
  simpa [h3] using (lt_of_lt_of_le h1 h2)

example {x y : ℝ} (h1 : y ≤ x + 5) (h2 : x ≤ -2) : x + y < 2 := by
  linarith

example (x ε : ℝ) (hε : 0 < ε) (h1 : x < ε / 2) (h2 : -x < ε / 2) : |x| < ε := by
  rw [abs_lt] -- `⊢ -ε < x ∧ x < ε`
  constructor <;> -- <;> means "do next tactic on all the goals this tactic produces"
  linarith -- solves both goals

example {p q : ℚ} (h: (p - 1)*(q - 2) = 0): p = 1 ∨ q = 2 := by
  rw [mul_eq_zero] at h
  obtain hp | hq := h
  · left
    linarith
  · right
    linarith

example (a b : ℝ) (ha : a ≠ 0) (h : a * b - a = 0) : b = 1 :=
  mul_right_injective₀ ha (by linarith : a * b = a * 1)

example (a b c d : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (h : a * a * b * c - a * b * d = 0) : a * c = d := by
  apply mul_left_cancel₀ (by positivity : a * b ≠ 0)
  linarith

example {m n : ℚ} (hm : m ≠ 0) (h : ((3 / 4) * m) * (n - 120) = m * (n - 245)) : n = 620 := by
  have h' : ((3 / 4) * m) * (n - 120) * (1 / m) = m * (n - 245) * (1 / m) := by simp [h]
  ring_nf at h'
  simp [mul_comm m n,hm] at h'
  linarith

example {a b c : ℝ} (ha : a ≤ b + c) (hb : b ≤ a + c) (hc : c ≤ a + b) :
    ∃ x y z, x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ a = y + z ∧ b = x + z ∧ c = x + y := by
  set x := (b - a + c) / 2 with hx_def
  set y := (a - b + c) / 2 with hy_def
  set z := (a + b - c) / 2 with hz_def
  have hx : x ≥ 0 := by linarith [ha, hb, hc, hx_def, hy_def, hz_def]
  have hy : y ≥ 0 := by linarith [ha, hb, hc, hx_def, hy_def, hz_def]
  have hz : z ≥ 0 := by linarith [ha, hb, hc, hx_def, hy_def, hz_def]
  have ha_eq : a = y + z := by linarith [hy_def, hz_def]
  have hb_eq : b = x + z := by linarith [hx_def, hz_def]
  have hc_eq : c = x + y := by linarith [hx_def, hy_def]
  exact ⟨x, y, z, hx, hy, hz, ha_eq, hb_eq, hc_eq⟩

end linarith


section nlinarith

example {n : ℕ} : n ^ 2 ≠ 2 :=
match n with
| 0 => by norm_num
| 1 => by norm_num
| n + 2 => fun h ↦ by
  rw [add_sq] at h
  nlinarith

end nlinarith
