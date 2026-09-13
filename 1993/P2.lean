import Mathlib

/-!
# IMO 1993, Problem 2

`D` is inside acute triangle `ABC` with `∠ADB = ∠ACB + π/2` and `AC·BD = AD·BC`.

* (a) compute `AB·CD / (AC·BD)`;
* (b) show the tangents at `C` to the circumcircles of `ACD` and `BCD` are perpendicular.

## Modelling

Points are complex numbers `a, b, c, d`. Put

  `z = (a-c)(b-d) / ((a-d)(b-c))`.

* `AC·BD = AD·BC` says exactly `‖z‖ = 1`;
* `∠ADB = ∠ACB + π/2` says the directed angle `∠ACB - ∠ADB` is `-π/2`, i.e. `arg z = -π/2`.

Together these are the single algebraic hypothesis

  `(a-c)(b-d) = -i·(a-d)(b-c)`,

which is what `hD` below states. This packages both hypotheses of the problem, and the acuteness
and interiority conditions are not needed beyond guaranteeing this configuration.

## Part (a)

The identity `(a-b)(c-d) = (a-c)(b-d) - (a-d)(b-c)` turns `hD` into
`(a-b)(c-d) = -(1+i)(a-d)(b-c)`. Taking absolute values, `AB·CD = √2·AD·BC` while
`AC·BD = AD·BC`, so the ratio is `√2`.

## Part (b)

By the tangent–chord angle, the tangent at `c` to the circle through `p, c, d` has direction
`(d-c)(d-p)/(c-p)`; this is `tangentDir p c d` below. Mathlib has no API for tangent lines to
circumcircles, so this formula is the modelling input for part (b) — everything after it is
proved. The two directions differ by the factor `i`, hence are perpendicular.
-/

namespace Imo1993P2

/-- Direction of the tangent at `c` to the circle through `p`, `c`, `d`, given by the
tangent–chord angle: the angle from the chord `cd` to the tangent equals the inscribed angle
`∠dpc`. -/
noncomputable def tangentDir (p c d : ℂ) : ℂ := (d - c) * (d - p) / (c - p)

/-- **Part (a).** `AB·CD = √2 · AC·BD`. -/
theorem part_a (a b c d : ℂ)
    (hD : (a - c) * (b - d) = -Complex.I * ((a - d) * (b - c))) :
    ‖(a - b) * (c - d)‖ = Real.sqrt 2 * ‖(a - c) * (b - d)‖ := by
  have key : (a - b) * (c - d) = -(1 + Complex.I) * ((a - d) * (b - c)) := by
    linear_combination hD
  have h1 : ‖(1 + Complex.I : ℂ)‖ = Real.sqrt 2 := by
    rw [Complex.norm_def]
    congr 1
    simp [Complex.normSq_apply]
    norm_num
  rw [key, hD]
  simp only [norm_mul, norm_neg, h1, Complex.norm_I, one_mul]

/-- **Part (b), algebraic core.** The two tangent directions at `c` differ by a factor `i`. -/
theorem tangentDir_eq (a b c d : ℂ)
    (hD : (a - c) * (b - d) = -Complex.I * ((a - d) * (b - c)))
    (hac : c - a ≠ 0) (hbc : c - b ≠ 0) :
    tangentDir a c d = Complex.I * tangentDir b c d := by
  unfold tangentDir
  rw [← mul_div_assoc, div_eq_div_iff hac hbc]
  linear_combination (-(d - c) * Complex.I) * hD
    + ((d - c) * (a - d) * (b - c)) * Complex.I_sq

/-- **Part (b).** The tangents at `c` to the two circumcircles are perpendicular. -/
theorem part_b (a b c d : ℂ)
    (hD : (a - c) * (b - d) = -Complex.I * ((a - d) * (b - c)))
    (hac : c - a ≠ 0) (hbc : c - b ≠ 0) :
    (tangentDir a c d * (starRingEnd ℂ) (tangentDir b c d)).re = 0 := by
  rw [tangentDir_eq a b c d hD hac hbc, mul_assoc, Complex.mul_conj]
  simp

end Imo1993P2
