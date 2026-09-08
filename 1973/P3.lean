/-
# IMO 1973, Problem 3

Let `a, b` be reals for which `x⁴ + a x³ + b x² + a x + 1 = 0` has at least one
real solution.  Over all such pairs `(a, b)`, find the minimum of `a² + b²`.

The answer is `4/5`, attained at `a = 4/5`, `b = -2/5` (with root `x = -1`).
"Find the minimum" is formalized as `IsLeast`.

## Proof

The AoPS solution substitutes `z = x + 1/x`, uses `|z| ≥ 2` and then estimates.
The version below avoids division and the case analysis on the sign of `z` by
using Cauchy–Schwarz once.

If `x` is a root then `x ≠ 0`, and the equation says exactly

  `a · ((x² + 1) x) + b · x² = -(x⁴ + 1)`.

Cauchy–Schwarz for the two vectors `(a, b)` and `((x²+1)x, x²)` gives

  `(a² + b²) · P ≥ (x⁴ + 1)²`,  where `P = x²(x²+1)² + x⁴ > 0`.

It remains to check `(x⁴ + 1)² ≥ (4/5) P`, i.e.

  `5(x⁴+1)² - 4(x²(x²+1)² + x⁴) = (x² - 1)² (5x⁴ + 6x² + 5) ≥ 0`,

which is visibly true.  Dividing by `P > 0` gives `a² + b² ≥ 4/5`.

Equality forces `x² = 1`; taking `x = -1` gives `a = 4/5`, `b = -2/5`.
-/

import Mathlib

namespace Imo1973P3

/-- **IMO 1973, Problem 3.** -/
theorem imo1973_p3 :
    IsLeast {y : ℝ | ∃ a b : ℝ,
      (∃ x : ℝ, x ^ 4 + a * x ^ 3 + b * x ^ 2 + a * x + 1 = 0) ∧ y = a ^ 2 + b ^ 2}
      (4 / 5) := by
  constructor
  · -- `a = 4/5`, `b = -2/5`, root `x = -1`
    exact ⟨4 / 5, -2 / 5, ⟨-1, by norm_num⟩, by norm_num⟩
  · rintro y ⟨a, b, ⟨x, hx⟩, rfl⟩
    -- `x ≠ 0`
    have hx0 : x ≠ 0 := by
      intro h
      rw [h] at hx
      norm_num at hx
    have hx2 : 0 < x ^ 2 := by
      rcases lt_trichotomy x 0 with h | h | h
      · nlinarith
      · exact absurd h hx0
      · nlinarith
    have hx4 : 0 < x ^ 4 := by nlinarith [mul_pos hx2 hx2]
    have hP : 0 < x ^ 2 * (x ^ 2 + 1) ^ 2 + x ^ 4 := by
      have h1 : (0:ℝ) ≤ x ^ 2 * (x ^ 2 + 1) ^ 2 := by positivity
      linarith
    -- the equation, rewritten as a scalar product
    have heq : a * ((x ^ 2 + 1) * x) + b * x ^ 2 = -(x ^ 4 + 1) := by linear_combination hx
    -- Cauchy–Schwarz
    have hCS : (a * ((x ^ 2 + 1) * x) + b * x ^ 2) ^ 2
        ≤ (a ^ 2 + b ^ 2) * (x ^ 2 * (x ^ 2 + 1) ^ 2 + x ^ 4) := by
      nlinarith [sq_nonneg (a * x ^ 2 - b * ((x ^ 2 + 1) * x))]
    rw [heq] at hCS
    -- the polynomial inequality `(x⁴+1)² ≥ (4/5) P`
    have hkey : (4 / 5) * (x ^ 2 * (x ^ 2 + 1) ^ 2 + x ^ 4) ≤ (x ^ 4 + 1) ^ 2 := by
      nlinarith [mul_nonneg (sq_nonneg (x ^ 2 - 1))
        (by positivity : (0:ℝ) ≤ 5 * x ^ 4 + 6 * x ^ 2 + 5)]
    -- divide by `P > 0`
    exact le_of_mul_le_mul_right (by nlinarith [hCS, hkey]) hP

end Imo1973P3
