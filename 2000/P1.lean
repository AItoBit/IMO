import Mathlib

/-!
# IMO 2000, Problem 1

`G₁`, `G₂` meet at `M`, `N`; `AB` is their common tangent (`A ∈ G₁`, `B ∈ G₂`), with `M` nearer
to `AB`. The parallel to `AB` through `M` meets `G₁` again at `C` and `G₂` again at `D`. Lines
`AC`, `BD` meet at `E`; `AN`, `CD` meet at `P`; `BN`, `CD` meet at `Q`. Show `EP = EQ`.

## Set-up

Take `AB` as the `x`-axis (this is a genuine WLOG: it is a choice of Euclidean frame). Then `G₁`
is tangent to it at `A = (a, 0)`, so `G₁` has centre `(a, r₁)` and radius `|r₁|`, and a point
`(x, y)` lies on `G₁` exactly when `(x - a)² + y² = 2 r₁ y`. Likewise `G₂` has centre `(b, r₂)`.
`M = (m₁, m₂)` and `N = (n₁, n₂)` are the two common points, and `CD` is the horizontal line
`y = m₂`. `C` and `D` are recorded through `E`'s collinearity conditions, and `P`, `Q` through
theirs; all of these are the literal incidence statements, cleared of denominators.

## Proof

Two facts do all the work.

* **`M` is the midpoint of `PQ`.** Subtracting the two circle equations at `M` gives
  `(b - a)(2m₁ - a - b) = 2 m₂ (r₁ - r₂)`, and at `N` gives `(b - a)(2n₁ - a - b) = 2 n₂ (r₁ - r₂)`.
  Cross-multiplying eliminates `r₁ - r₂` and, since `a ≠ b`, leaves
  `n₂ (2m₁ - a - b) = m₂ (2n₁ - a - b)`. Adding the incidence relations for `P` and `Q` and
  cancelling `n₂` turns this into `px + qx = 2 m₁`.
  (Geometrically: `MN` meets `AB` at its midpoint, because the power of that point is `(x-a)²`
  for `G₁` and `(x-b)²` for `G₂`; the homothety at `N` carrying `AB` to `CD` sends `A, B` to
  `P, Q` and the midpoint to `M`.)
* **`E` is the reflection of `M` in `AB`**, i.e. `E = (m₁, -m₂)`. Subtracting the two
  collinearity conditions gives `(a - b)(ey + m₂) = 0`, hence `ey = -m₂`; feeding that back gives
  `m₂ (ex - m₁) = 0`, hence `ex = m₁`.

So `E` lies on the perpendicular to `CD` through the midpoint of `PQ`, and `EP = EQ`.

## A warning about the AoPS "Solution 2"

That solution asserts `E`, `M`, `N` are collinear ("the lines `EAC` and `EMN` are secant lines
drawn from the external point `E`") and deduces `EA·EC = EM·EN = EB·ED`, concluding `EA = EB`.
Both are false. With `A = (0,0)`, `B = (2.2, 0)`, `r₁ = 1`, `r₂ = 2` one gets `EA ≈ 1.0065` but
`EB ≈ 1.4234`, and `E` is off line `MN`. `EA = EB` holds only when `r₁ = r₂`, where the whole
picture is symmetric. The conclusion `EP = EQ` is of course still true — but by the route above,
which is Solution 1's.
-/

namespace Imo2000P1

/-- **IMO 2000 P1.** -/
theorem imo2000_p1
    (a b r₁ r₂ m₁ m₂ n₁ n₂ ex ey px qx : ℝ)
    (hab : a ≠ b) (hm₂ : m₂ ≠ 0) (hn₂ : n₂ ≠ 0)
    -- `M` lies on `G₁` (centre `(a, r₁)`, tangent to the `x`-axis at `A = (a,0)`) and on `G₂`
    (hM1 : (m₁ - a) ^ 2 + m₂ ^ 2 = 2 * r₁ * m₂)
    (hM2 : (m₁ - b) ^ 2 + m₂ ^ 2 = 2 * r₂ * m₂)
    -- `N` lies on `G₁` and on `G₂`
    (hN1 : (n₁ - a) ^ 2 + n₂ ^ 2 = 2 * r₁ * n₂)
    (hN2 : (n₁ - b) ^ 2 + n₂ ^ 2 = 2 * r₂ * n₂)
    -- `E` is on line `AC`, where `A = (a,0)` and `C = (2a - m₁, m₂)` is the second meet of
    -- `G₁` with `CD`
    (hE1 : (a - m₁) * ey - m₂ * (ex - a) = 0)
    -- `E` is on line `BD`, where `B = (b,0)` and `D = (2b - m₁, m₂)`
    (hE2 : (b - m₁) * ey - m₂ * (ex - b) = 0)
    -- `P = (px, m₂)` is on line `AN`, and `Q = (qx, m₂)` is on line `BN`
    (hP : (n₁ - a) * m₂ = n₂ * (px - a))
    (hQ : (n₁ - b) * m₂ = n₂ * (qx - b)) :
    dist (⟨ex, ey⟩ : ℂ) (⟨px, m₂⟩ : ℂ) = dist (⟨ex, ey⟩ : ℂ) (⟨qx, m₂⟩ : ℂ) := by
  -- eliminating `r₁ - r₂` between the `M`-relations and the `N`-relations
  have hstar : n₂ * (2 * m₁ - a - b) = m₂ * (2 * n₁ - a - b) := by
    have h1 : (b - a) * (n₂ * (2 * m₁ - a - b) - m₂ * (2 * n₁ - a - b)) = 0 := by
      linear_combination n₂ * hM1 - n₂ * hM2 - m₂ * hN1 + m₂ * hN2
    rcases mul_eq_zero.1 h1 with h | h
    · exact absurd (by linarith : a = b) hab
    · linarith
  -- `M` is the midpoint of `PQ`
  have hkey : px + qx = 2 * m₁ := by
    have h2 : n₂ * (px + qx - a - b) = n₂ * (2 * m₁ - a - b) := by
      linear_combination -hP - hQ - hstar
    have h3 := mul_left_cancel₀ hn₂ h2
    linarith
  -- `E` is the reflection of `M` in `AB`
  have hey : ey = -m₂ := by
    have h1 : (a - b) * (ey + m₂) = 0 := by linear_combination hE1 - hE2
    rcases mul_eq_zero.1 h1 with h | h
    · exact absurd (by linarith : a = b) hab
    · linarith
  have hex : ex = m₁ := by
    have h1 : m₂ * (ex - m₁) = 0 := by
      rw [hey] at hE1
      linear_combination -hE1
    rcases mul_eq_zero.1 h1 with h | h
    · exact absurd h hm₂
    · linarith
  -- hence the two distances agree
  have hsq : Complex.normSq ((⟨ex, ey⟩ : ℂ) - (⟨px, m₂⟩ : ℂ))
      = Complex.normSq ((⟨ex, ey⟩ : ℂ) - (⟨qx, m₂⟩ : ℂ)) := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, hex, hey]
    linear_combination (px - qx) * hkey
  rw [Complex.dist_eq, Complex.dist_eq, Complex.norm_def, Complex.norm_def, hsq]

end Imo2000P1
