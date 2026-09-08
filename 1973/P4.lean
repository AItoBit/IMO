/-
# IMO 1973, Problem 4 — the geometric core

A soldier must check for mines in an equilateral triangle.  His detector has
radius equal to half the altitude, `h/2`.  He starts at a vertex.  What path of
least length accomplishes the mission?

Answer: `(√7/2 - √3/4) · s` where `s` is the side, equivalently `(√(7/3) - 1/2) · h`.

## Honest scope note

This is not a one-pass formalization, and the AoPS write-up is not a complete
proof either.  A faithful statement needs a notion of *path* and of *covering*:

```
def Covers (γ : ℝ → ℂ) (T : ℝ) (K : Set ℂ) (r : ℝ) : Prop :=
  ∀ p ∈ K, ∃ u ∈ Set.Icc (0:ℝ) T, dist p (γ u) ≤ r

theorem imo1973_p4 (s : ℝ) (hs : 0 < s) :
    IsLeast
      { L | ∃ (γ : ℝ → ℂ) (T : ℝ), 0 ≤ T ∧ ContinuousOn γ (Set.Icc 0 T) ∧
              γ 0 = A ∧ Covers γ T (triangle A B C) (h / 2) ∧
              eVariationOn γ (Set.Icc 0 T) = ENNReal.ofReal L }
      ((Real.sqrt 7 / 2 - Real.sqrt 3 / 4) * s)
```

Two things make this expensive, and the linked solution glosses over both:

* the **lower bound** is argued only against paths of the restricted shape
  "`A` → a point of `c₂` → a point of `c₁`"; that this shape is forced (any
  covering path must reach within `h/2` of `B` and of `C`, and the order can be
  fixed by symmetry) needs a real argument about arbitrary rectifiable curves;
* the **covering claim** ("this path easily covers the whole triangle") is
  asserted, not proved; proving it means bounding `dist p (segment A E ∪ segment E F)`
  by `h/2` for every `p` in the triangle.

What follows compiles with no `sorry` and proves the parts that are genuinely
the mathematical content of the solution, in coordinates
`A = (0,0)`, `B = (s,0)`, `C = (s/2, h)`, `h = (√3/2) s`, so that `D = (s/2, 0)`
is the midpoint of `AB` and `E = (s/2, h/2)` the midpoint of `CD`:

* `dist_sum_min_on_line` — the reflection step: among all points `X` on the
  horizontal line through `E`, the sum `AX + BX` is smallest at `X = E`.  This
  is exactly inequality (1) of the solution, and it is what pins the turning
  point of the optimal path to `E`.
* `path_length` — the length `AE + EF` of the proposed path, where `F` is the
  point of segment `EB` at distance `h/2` from `B`, equals `(√7/2 - √3/4) s`.
* `answer_forms` — the two closed forms of the answer agree.
-/

import Mathlib

namespace Imo1973P4

/-- The point of the plane with coordinates `(x, y)`, as a complex number. -/
noncomputable def pt (x y : ℝ) : ℂ := (x : ℂ) + (y : ℂ) * Complex.I

@[simp] lemma pt_re (x y : ℝ) : (pt x y).re = x := by
  simp only [pt, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

@[simp] lemma pt_im (x y : ℝ) : (pt x y).im = y := by
  simp only [pt, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

lemma dist_pt (x₁ y₁ x₂ y₂ : ℝ) :
    dist (pt x₁ y₁) (pt x₂ y₂) = Real.sqrt ((x₁ - x₂) ^ 2 + (y₁ - y₂) ^ 2) := by
  rw [Complex.dist_eq_re_im, pt_re, pt_re, pt_im, pt_im]

/-- **The reflection step.**  For `A = (0,0)` and `B = (s,0)`, among all points
`X = (x, t)` on a fixed horizontal line, `AX + BX` is minimal at the midpoint
`(s/2, t)`.  (Reflect `B` in the line: the sum becomes `AX + XB'`, minimised on
the segment `AB'`, whose intersection with the line is exactly `(s/2, t)`.) -/
theorem dist_sum_min_on_line (s t x : ℝ) :
    dist (pt 0 0) (pt (s / 2) t) + dist (pt s 0) (pt (s / 2) t)
      ≤ dist (pt 0 0) (pt x t) + dist (pt s 0) (pt x t) := by
  have e1 : dist (pt 0 0) (pt (s / 2) t) = Real.sqrt ((s / 2) ^ 2 + t ^ 2) := by
    rw [dist_pt]; congr 1; ring
  have e5 : dist (pt s 0) (pt (s / 2) t) = Real.sqrt ((s / 2) ^ 2 + t ^ 2) := by
    rw [dist_pt]; congr 1; ring
  have e3 : dist (pt 0 0) (pt s (2 * t)) = Real.sqrt (s ^ 2 + 4 * t ^ 2) := by
    rw [dist_pt]; congr 1; ring
  -- reflecting `B = (s, 0)` in the line `y = t` gives `B' = (s, 2t)`
  have e4 : dist (pt s 0) (pt x t) = dist (pt s (2 * t)) (pt x t) := by
    rw [dist_pt, dist_pt]; congr 1; ring
  have h4 : Real.sqrt (s ^ 2 + 4 * t ^ 2) = 2 * Real.sqrt ((s / 2) ^ 2 + t ^ 2) := by
    rw [show s ^ 2 + 4 * t ^ 2 = 2 ^ 2 * ((s / 2) ^ 2 + t ^ 2) by ring,
      Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
  calc dist (pt 0 0) (pt (s / 2) t) + dist (pt s 0) (pt (s / 2) t)
      = dist (pt 0 0) (pt s (2 * t)) := by rw [e1, e5, e3, h4]; ring
    _ ≤ dist (pt 0 0) (pt x t) + dist (pt x t) (pt s (2 * t)) := dist_triangle _ _ _
    _ = dist (pt 0 0) (pt x t) + dist (pt s 0) (pt x t) := by
        rw [dist_comm (pt x t) (pt s (2 * t)), ← e4]

/-- **The length of the proposed path.**  With `E = (s/2, h/2)` the midpoint of
`CD` and `F` the point of `EB` at distance `h/2 = (√3/4) s` from `B`, the path
`A → E → F` has length `AE + (BE - h/2) = (√7/2 - √3/4) s`. -/
theorem path_length (s : ℝ) (hs : 0 ≤ s) :
    dist (pt 0 0) (pt (s / 2) (Real.sqrt 3 / 4 * s))
      + dist (pt s 0) (pt (s / 2) (Real.sqrt 3 / 4 * s))
      - Real.sqrt 3 / 4 * s
    = (Real.sqrt 7 / 2 - Real.sqrt 3 / 4) * s := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h7 : Real.sqrt 7 ^ 2 = 7 := Real.sq_sqrt (by norm_num)
  have hnn : (0:ℝ) ≤ Real.sqrt 7 / 4 * s := mul_nonneg (by positivity) hs
  have e1 : dist (pt 0 0) (pt (s / 2) (Real.sqrt 3 / 4 * s)) = Real.sqrt 7 / 4 * s := by
    rw [dist_pt, show (0 - s / 2) ^ 2 + (0 - Real.sqrt 3 / 4 * s) ^ 2
        = (Real.sqrt 7 / 4 * s) ^ 2 from by
      linear_combination (s ^ 2 / 16) * h3 - (s ^ 2 / 16) * h7]
    exact Real.sqrt_sq hnn
  have e2 : dist (pt s 0) (pt (s / 2) (Real.sqrt 3 / 4 * s)) = Real.sqrt 7 / 4 * s := by
    rw [dist_pt, show (s - s / 2) ^ 2 + (0 - Real.sqrt 3 / 4 * s) ^ 2
        = (Real.sqrt 7 / 4 * s) ^ 2 from by
      linear_combination (s ^ 2 / 16) * h3 - (s ^ 2 / 16) * h7]
    exact Real.sqrt_sq hnn
  rw [e1, e2]
  ring

/-- The two closed forms of the answer agree: with `h = (√3/2) s`,
`(√7/2 - √3/4) s = (√(7/3) - 1/2) h`. -/
theorem answer_forms (s : ℝ) :
    (Real.sqrt 7 / 2 - Real.sqrt 3 / 4) * s
      = (Real.sqrt (7 / 3) - 1 / 2) * (Real.sqrt 3 / 2 * s) := by
  have key : Real.sqrt (7 / 3) * Real.sqrt 3 = Real.sqrt 7 := by
    rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 7 / 3)]
    norm_num
  linear_combination (-(s / 2)) * key

end Imo1973P4
