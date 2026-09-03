import Mathlib

/--
IMO 1964 Problem 2: Suppose that `a, b, c` are the sides of a triangle. Then
`a^2 (b + c - a) + b^2 (c + a - b) + c^2 (a + b - c) ≤ 3abc`.
-/
theorem imo_1964_p2 (a b c : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
    (h₁ : c < a + b) (h₂ : b < a + c) (h₃ : a < b + c) :
    a ^ 2 * (b + c - a) + b ^ 2 * (c + a - b) + c ^ 2 * (a + b - c) ≤ 3 * a * b * c := by
  obtain ⟨ha, hb, hc⟩ := h₀
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c),
    mul_pos ha hb, mul_pos hb hc, mul_pos ha hc,
    mul_nonneg (sub_nonneg.mpr h₁.le) (sq_nonneg (a - b)),
    mul_nonneg (sub_nonneg.mpr h₂.le) (sq_nonneg (a - c)),
    mul_nonneg (sub_nonneg.mpr h₃.le) (sq_nonneg (b - c))]
