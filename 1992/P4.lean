import Mathlib

/-!
# IMO 1992, Problem 4

`C` is a circle, `l` a tangent line to `C`, and `M` a point on `l`. Find the locus of points `P`
for which there exist `Q, R` on `l` with `M` the midpoint of `QR` and `C` the incircle of `PQR`.

## Coordinates

Put `C : x² + y² = r²` with `r > 0`, `l : y = -r` (tangent at `D = (0,-r)`), and `M = (m,-r)`.

For `t ≠ 0`, the tangent to `C` from `(t,-r)` other than `l` is the line

  `2rt·x + (t² - r²)·y = r(t² + r²)`,

written `OnTangent r t x y` below. `tangent_is_tangent` checks it really is tangent to `C` (the
distance from the origin is `r`, in the cleared form `C² = r²(A² + B²)`), and `tangent_through`
checks it passes through `(t,-r)`.

## Encoding the incircle condition

With `Q = (q,-r)` and `R = (ρ,-r)`, saying that `C` is the *inscribed* circle of `PQR` amounts to:
`PQ` and `PR` are tangent to `C`; the point where `C` touches `QR` — namely `D = (0,-r)` — lies
strictly between `Q` and `R`, i.e. `q < 0 < ρ`; and `P` lies on the same side of `l` as `C`, i.e.
`-r < P.2`. (Without that last condition the same equations also describe the `P`-excircle, whose
apex sits below `l`.) `M` being the midpoint of `QR` is `q + ρ = 2m`.

## Answer

The locus is the open ray `{(x,y) | r·x + m·y = m·r ∧ y > r}`: the part of the line through
`(0,r)` and `(m,0)` strictly above the top of the circle. Its slope is `-r/m`.

(The AoPS page reports the slope as `-r²/(2m)`; that is an algebra slip. From its own formulas
`Pₓ = 2mr²/(m²+r²-d²)` and `P_y = r(m²-r²-d²)/(m²+r²-d²)` one gets
`(P_y - r)/Pₓ = -2r³/(2mr²) = -r/m`.)
-/

namespace Imo1992P4

/-- `P = (x,y)` lies on the tangent to `x² + y² = r²` drawn from `(t,-r)` other than `y = -r`. -/
def OnTangent (r t x y : ℝ) : Prop := 2 * r * t * x + (t ^ 2 - r ^ 2) * y = r * (t ^ 2 + r ^ 2)

/-- The line `OnTangent r t` is at distance `r` from the origin, so it is tangent to `C`.
Written in cleared form: for `A x + B y = C`, the condition is `C² = r²(A² + B²)`. -/
theorem tangent_is_tangent (r t : ℝ) :
    (r * (t ^ 2 + r ^ 2)) ^ 2 = r ^ 2 * ((2 * r * t) ^ 2 + (t ^ 2 - r ^ 2) ^ 2) := by
  ring

/-- The line `OnTangent r t` passes through `(t, -r)`. -/
theorem tangent_through (r t : ℝ) : OnTangent r t t (-r) := by
  unfold OnTangent; ring

/-- **IMO 1992 P4.** The locus is the open ray of the line `r·x + m·y = m·r` above `y = r`. -/
theorem imo1992_p4 (r m : ℝ) (hr : 0 < r) :
    {P : ℝ × ℝ | -r < P.2 ∧ ∃ q ρ : ℝ, q < 0 ∧ 0 < ρ ∧ q + ρ = 2 * m ∧
        OnTangent r q P.1 P.2 ∧ OnTangent r ρ P.1 P.2}
      = {P : ℝ × ℝ | r * P.1 + m * P.2 = m * r ∧ r < P.2} := by
  ext ⟨x, y⟩
  simp only [Set.mem_ofPred_eq]
  unfold OnTangent
  constructor
  · rintro ⟨hy, q, ρ, hq0, hρ0, hsum, hq, hρ⟩
    -- the two tangents meet on the line `r x + m y = m r`
    have hne : q - ρ ≠ 0 := by intro h; linarith [sub_eq_zero.1 h]
    have hfac : (q - ρ) * (2 * r * x + (q + ρ) * y - r * (q + ρ)) = 0 := by
      linear_combination hq - hρ
    have hzero : 2 * r * x + (q + ρ) * y - r * (q + ρ) = 0 := by
      rcases mul_eq_zero.1 hfac with h | h
      · exact absurd h hne
      · exact h
    have hline : r * x + m * y = m * r := by
      rw [hsum] at hzero; linarith
    refine ⟨hline, ?_⟩
    -- the tangent-length parameter `u = -qρ` is positive
    have hu : 0 < q ^ 2 - 2 * q * m := by nlinarith
    have hkey : (q ^ 2 - 2 * q * m) * (y - r) = r ^ 2 * (y + r) := by
      linear_combination hq - 2 * q * hline
    by_contra hcon
    rw [not_lt] at hcon
    have hpos : 0 < r ^ 2 * (y + r) := mul_pos (pow_pos hr 2) (by linarith)
    have hnp : 0 ≤ (q ^ 2 - 2 * q * m) * (r - y) := mul_nonneg hu.le (by linarith)
    nlinarith [hkey, hpos, hnp]
  · rintro ⟨hline, hy⟩
    have h1 : 0 < y - r := by linarith
    have h2 : 0 < y + r := by linarith
    set u : ℝ := r ^ 2 * (y + r) / (y - r) with hudef
    have hu0 : 0 < u := div_pos (mul_pos (pow_pos hr 2) h2) h1
    have hukey : u * (y - r) = r ^ 2 * (y + r) := by
      rw [hudef]; field_simp
    set s : ℝ := Real.sqrt (m ^ 2 + u) with hsdef
    have hs : s ^ 2 = m ^ 2 + u := Real.sq_sqrt (by nlinarith [sq_nonneg m])
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hms : m < s := by nlinarith
    have hms' : -m < s := by nlinarith
    refine ⟨by linarith, m - s, m + s, by linarith, by linarith, by ring, ?_, ?_⟩
    · have hq2 : (m - s) ^ 2 - 2 * (m - s) * m = u := by linear_combination hs
      linear_combination (y - r) * hq2 + 2 * (m - s) * hline + hukey
    · have hr2 : (m + s) ^ 2 - 2 * (m + s) * m = u := by linear_combination hs
      linear_combination (y - r) * hr2 + 2 * (m + s) * hline + hukey

end Imo1992P4
