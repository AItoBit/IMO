import Mathlib

/-!
# IMO 1996, Problem 5 — metric core

`ABCDEF` is a convex hexagon with `AB ∥ DE`, `BD ∥ EF`, `CD ∥ FA`; `R_A`, `R_C`, `R_E` are the
circumradii of `FAB`, `BCD`, `DEF`, and `P` is the perimeter. Prove `R_A + R_C + R_E ≥ P/2`.

## What is formalized

Write `sᵢ` for the six sides and `α₁ = ∠FAB`, `α₂ = ∠ABC`, `α₃ = ∠BCD`; the parallel conditions
give `α₁ = α₄`, `α₂ = α₅`, `α₃ = α₆`. Put `u = sin α₁`, `v = sin α₂`, `w = sin α₃`.

The geometric part of the AoPS solution produces three inequalities. For `R_A`: dropping
perpendiculars from `A` and from `D` onto the parallel lines `FE` and `BC` gives
`d₁ ≥ s₆ sin α₃ + s₁ sin α₂` and `d₁ ≥ s₃ sin α₃ + s₄ sin α₂` (where `d₁ = |FB|`), and the
extended law of sines gives `d₁ = 2 R_A sin α₁`. Adding and substituting:

  `(s₃ + s₆) w + (s₁ + s₄) v ≤ 4 R_A u`,

and cyclically for `R_C` and `R_E`. Mathlib has no API for distances between parallel lines in a
convex hexagon, so those three inequalities are the modelling input here — they are `hA`, `hC`,
`hE` below. Everything after them is proved.

## The remaining argument

Multiplying the three by `vw`, `uv`, `uw` and adding gives

  `2(x+y+z)·uvw ≤ x·w(u²+v²) + y·u(v²+w²) + z·v(u²+w²) ≤ 4(R_A+R_C+R_E)·uvw`,

where `x = s₁+s₄`, `y = s₂+s₅`, `z = s₃+s₆`; the left inequality is `(u-v)² ≥ 0` and its
companions, which is the `t + 1/t ≥ 2` step of the write-up in cleared form. Cancelling `uvw > 0`
gives `2P ≤ 4(R_A + R_C + R_E)`.
-/

namespace Imo1996P5

/-- **Metric core of IMO 1996 P5.** -/
theorem imo1996_p5 (s1 s2 s3 s4 s5 s6 u v w RA RC RE : ℝ)
    (hs1 : 0 ≤ s1) (hs2 : 0 ≤ s2) (hs3 : 0 ≤ s3)
    (hs4 : 0 ≤ s4) (hs5 : 0 ≤ s5) (hs6 : 0 ≤ s6)
    (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (hA : (s3 + s6) * w + (s1 + s4) * v ≤ 4 * RA * u)
    (hC : (s2 + s5) * v + (s3 + s6) * u ≤ 4 * RC * w)
    (hE : (s1 + s4) * u + (s2 + s5) * w ≤ 4 * RE * v) :
    (s1 + s2 + s3 + s4 + s5 + s6) / 2 ≤ RA + RC + RE := by
  have hx : (0 : ℝ) ≤ s1 + s4 := by linarith
  have hy : (0 : ℝ) ≤ s2 + s5 := by linarith
  have hz : (0 : ℝ) ≤ s3 + s6 := by linarith
  -- clear the three denominators
  have e1 : ((s3 + s6) * w + (s1 + s4) * v) * (v * w) ≤ (4 * RA * u) * (v * w) :=
    mul_le_mul_of_nonneg_right hA (by positivity)
  have e2 : ((s2 + s5) * v + (s3 + s6) * u) * (u * v) ≤ (4 * RC * w) * (u * v) :=
    mul_le_mul_of_nonneg_right hC (by positivity)
  have e3 : ((s1 + s4) * u + (s2 + s5) * w) * (u * w) ≤ (4 * RE * v) * (u * w) :=
    mul_le_mul_of_nonneg_right hE (by positivity)
  -- the three AM-GM steps, in cleared form
  have g1 : (0 : ℝ) ≤ (s1 + s4) * w * (u - v) ^ 2 :=
    mul_nonneg (mul_nonneg hx hw.le) (sq_nonneg _)
  have g2 : (0 : ℝ) ≤ (s2 + s5) * u * (v - w) ^ 2 :=
    mul_nonneg (mul_nonneg hy hu.le) (sq_nonneg _)
  have g3 : (0 : ℝ) ≤ (s3 + s6) * v * (u - w) ^ 2 :=
    mul_nonneg (mul_nonneg hz hv.le) (sq_nonneg _)
  have huvw : (0 : ℝ) < u * v * w := by positivity
  have key : (2 * (s1 + s2 + s3 + s4 + s5 + s6)) * (u * v * w)
      ≤ (4 * (RA + RC + RE)) * (u * v * w) := by
    nlinarith [e1, e2, e3, g1, g2, g3]
  have hcancel : 2 * (s1 + s2 + s3 + s4 + s5 + s6) ≤ 4 * (RA + RC + RE) :=
    le_of_mul_le_mul_right key huvw
  linarith

end Imo1996P5
