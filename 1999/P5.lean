import Mathlib

/-!
# IMO 1999, Problem 5 — metric core

Circles `G₁`, `G₂` lie inside `G` and are internally tangent to it at `M`, `N`; `G₁` passes
through the centre of `G₂`. The line through the two intersection points of `G₁` and `G₂` meets
`G` at `A`, `B`; the lines `MA`, `MB` meet `G₁` again at `C`, `D`. Prove `CD` is tangent to `G₂`.

## What is formalized

Mathlib has no API for homothety at a point of tangency, for "the second intersection of a line
with a circle", or for radical axes, so the synthetic set-up cannot be carried out. What is
formalized is the metric content, which is where the hypothesis "`G₁` passes through the centre
of `G₂`" actually does its work.

Put the centre of `G` at the origin, with radius `R`; let `O₁`, `O₂` be the centres and `r₁`,
`r₂` the radii of `G₁`, `G₂`. Internal tangency is `‖O₁‖ = R - r₁` and `‖O₂‖ = R - r₂`, and `G₁`
passing through `O₂` is `‖O₂ - O₁‖ = r₁`; writing `n` for the unit vector from `O₁` to `O₂` that
is `O₂ - O₁ = r₁ n`.

Since `AB` is the radical axis of `G₁` and `G₂`, it is perpendicular to `O₁O₂`, so it is the line
`{X | ⟪X, n⟫ = t}` for some `t`, and `X` below is any of its points. The homothety at `M` taking
`G` to `G₁` carries `A, B, O` to `C, D, O₁`, so `CD` is parallel to `AB` — the line
`{Y | ⟪Y, n⟫ = s}` — with

  `⟪O₁, n⟫ - s = (r₁/R) · (⟪O, n⟫ - t)`,

which is `hhom` below (and `⟪O, n⟫ = 0`). Those two facts are the modelling input.

## The computation

Expanding the radical-axis condition at `X` and using `‖O₁‖ = R - r₁`, `‖O₂‖ = R - r₂` collapses
everything to `r₁ t = R (r₁ - r₂)`. Then

  `⟪O₂, n⟫ - s = (⟪O₂, n⟫ - ⟪O₁, n⟫) - (r₁/R) t = r₁ - (r₁ - r₂) = r₂`,

so the distance from `O₂` to `CD` is exactly `r₂`, i.e. `CD` is tangent to `G₂`.
-/

namespace Imo1999P5

/-- The Euclidean inner product on `ℂ`. -/
noncomputable def dot (z w : ℂ) : ℝ := z.re * w.re + z.im * w.im

theorem dot_comm (z w : ℂ) : dot z w = dot w z := by
  simp only [dot]; ring

theorem dot_self (z : ℂ) : dot z z = ‖z‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  rfl

theorem dot_sub_left (z w v : ℂ) : dot (z - w) v = dot z v - dot w v := by
  simp only [dot, Complex.sub_re, Complex.sub_im]; ring

theorem dot_real_smul (r : ℝ) (z w : ℂ) : dot ((r : ℂ) * z) w = r * dot z w := by
  simp only [dot, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem norm_sub_sq (Y Z : ℂ) : ‖Y - Z‖ ^ 2 = dot Y Y - 2 * dot Y Z + dot Z Z := by
  rw [← dot_self]
  simp only [dot, Complex.sub_re, Complex.sub_im]
  ring

/-- **Metric core of IMO 1999 P5.** The distance from the centre of `G₂` to the line `CD` is
exactly the radius of `G₂`. -/
theorem imo1999_p5 (R r₁ r₂ t s : ℝ) (O₁ O₂ n X : ℂ)
    (hR : 0 < R) (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hn : ‖n‖ = 1)
    (h1 : ‖O₁‖ = R - r₁)
    (h2 : ‖O₂‖ = R - r₂)
    (h12 : O₂ - O₁ = (r₁ : ℂ) * n)
    (hXt : dot X n = t)
    (hXrad : ‖X - O₁‖ ^ 2 - r₁ ^ 2 = ‖X - O₂‖ ^ 2 - r₂ ^ 2)
    (hhom : dot O₁ n - s = (r₁ / R) * (0 - t)) :
    |dot O₂ n - s| = r₂ := by
  have hnn : dot n n = 1 := by rw [dot_self, hn]; norm_num
  have h1' : dot O₁ O₁ = (R - r₁) ^ 2 := by rw [dot_self, h1]
  have h2' : dot O₂ O₂ = (R - r₂) ^ 2 := by rw [dot_self, h2]
  -- `⟪O₂, n⟫ - ⟪O₁, n⟫ = r₁`
  have hdotdiff : dot O₂ n - dot O₁ n = r₁ := by
    have e := dot_sub_left O₂ O₁ n
    rw [h12, dot_real_smul, hnn] at e
    linarith
  -- `⟪X, O₂⟫ - ⟪X, O₁⟫ = r₁ t`
  have hXO : dot X O₂ - dot X O₁ = r₁ * t := by
    have e := dot_sub_left O₂ O₁ X
    rw [h12, dot_real_smul, dot_comm n X, hXt] at e
    rw [dot_comm X O₂, dot_comm X O₁]
    linarith
  -- the radical-axis condition pins down `t`
  rw [norm_sub_sq, norm_sub_sq, h1', h2'] at hXrad
  have ht : r₁ * t = R * (r₁ - r₂) := by nlinarith [hXrad, hXO]
  -- conclude
  have hs : s = dot O₁ n + (r₁ / R) * t := by linarith
  have h3 : (r₁ / R) * t = r₁ - r₂ := by
    rw [div_mul_eq_mul_div, div_eq_iff hR.ne']
    linarith
  have hfinal : dot O₂ n - s = r₂ := by
    rw [hs, h3]
    linarith
  rw [hfinal, abs_of_pos hr₂]

end Imo1999P5
