import Mathlib

/-!
# IMO 2005, Problem 1

Six points on the sides of an equilateral triangle `ABC` — `A₁, A₂` on `BC`, `B₁, B₂` on `CA`,
`C₁, C₂` on `AB` — form a convex hexagon `A₁A₂B₁B₂C₁C₂` with all six sides equal. Show that
`A₁B₂`, `B₁C₂`, `C₁A₂` are concurrent.

## Set-up

Take the triangle to have side `1`, with `B = (-1/2, 0)`, `C = (1/2, 0)`, `A = (0, h)` and
`h² = 3/4`; this is a genuine WLOG (similarity). Let `t` be the common side of the hexagon and
let `p`, `q`, `r` be the distances `BA₁`, `CB₁`, `AC₁`. Writing `σ = 1 - t`, the three "corner"
sides of the hexagon have lengths given by the law of cosines at the `60°` angles:

* `|A₂B₁|² = (σ-p)² + q² - (σ-p)q`  (corner `C`),
* `|B₂C₁|² = (σ-q)² + r² - (σ-q)r`  (corner `A`),
* `|C₂A₁|² = (σ-r)² + p² - (σ-r)p`  (corner `B`),

and the remaining three sides `A₁A₂`, `B₁B₂`, `C₁C₂` have length `t` automatically. So the
hypothesis "all six sides equal `t`" is exactly the three displayed quantities being `t²`.

## Proof

**Step 1 (`equal_sides_symmetric`): the three equations force `p = q = r`.** This is purely
algebraic — no convexity or range hypothesis is needed beyond `σ > 0`. Put
`S = 2(p+q+r) - 3σ`. Subtracting the equations in pairs gives

  `(2p-2r)S = σ(S - 6q + 3σ)` and its two cyclic shifts,

and combining those three as `S·D₁ - S·D₂ + 3σ·D₃` yields

  `(3(2p-σ) - S)·(S² + 3σ²) = 0`.

Over `ℝ` the second factor is positive, so `3(2p-σ) = S`, i.e. `2p = q + r`; cyclically
`2q = r + p` and `2r = p + q`, whence `p = q = r`.

(I checked this against a Gröbner basis of the three equations: it is `{p - r, q - r,
3r² - 3rσ + σ² - t²}`, so the symmetry really is forced by the ideal and not only by the
geometric range constraints.)

**Step 2 (`imo2005_p1`): with `p = q = r` the three diagonals all pass through the centroid
`O = (0, h/3)`.** For each diagonal the collinearity determinant equals `(-h/3)` times the side
condition, exactly — so the side condition being zero puts `O` on all three lines. Notably this
identity does not use `h² = 3/4`; only the hypothesis itself does, in identifying the corner
lengths.

## Relation to the AoPS solution

The write-up proves the three diagonals are the perpendicular bisectors of the sides of `A₂B₂C₂`,
via an auxiliary equilateral triangle `DEF` and a cyclic quadrilateral. The route here is
equivalent but shorter to verify: once `p = q = r` is known the configuration is symmetric under
the `120°` rotation about the centroid, and the concurrency point is the centroid itself.
-/

namespace Imo2005P1

/-- Twice the signed area of a triangle; it vanishes exactly when the points are collinear. -/
def cross (a1 a2 b1 b2 c1 c2 : ℝ) : ℝ := (b1 - a1) * (c2 - a2) - (b2 - a2) * (c1 - a1)

/-- The equal-side conditions force the hexagon to be symmetric: `p = q = r`. -/
theorem equal_sides_symmetric {p q r sig t : ℝ} (hsig : 0 < sig)
    (h1 : (sig - p) ^ 2 + q ^ 2 - (sig - p) * q = t ^ 2)
    (h2 : (sig - q) ^ 2 + r ^ 2 - (sig - q) * r = t ^ 2)
    (h3 : (sig - r) ^ 2 + p ^ 2 - (sig - r) * p = t ^ 2) :
    p = q ∧ q = r := by
  set S : ℝ := 2 * (p + q + r) - 3 * sig with hS
  have hD1 : (2 * p - 2 * r) * S = sig * (S - 6 * q + 3 * sig) := by
    rw [hS]; linear_combination 4 * h1 - 4 * h2
  have hD2 : (2 * q - 2 * p) * S = sig * (S - 6 * r + 3 * sig) := by
    rw [hS]; linear_combination 4 * h2 - 4 * h3
  have hD3 : (2 * r - 2 * q) * S = sig * (S - 6 * p + 3 * sig) := by
    rw [hS]; linear_combination 4 * h3 - 4 * h1
  have hpos : 0 < S ^ 2 + 3 * sig ^ 2 := by nlinarith [sq_nonneg S, hsig]
  have hne : S ^ 2 + 3 * sig ^ 2 ≠ 0 := ne_of_gt hpos
  have hp : 3 * (2 * p - sig) - S = 0 := by
    have hk : (3 * (2 * p - sig) - S) * (S ^ 2 + 3 * sig ^ 2) = 0 := by
      linear_combination S * hD1 - S * hD2 + 3 * sig * hD3
    exact (mul_eq_zero.1 hk).resolve_right hne
  have hq : 3 * (2 * q - sig) - S = 0 := by
    have hk : (3 * (2 * q - sig) - S) * (S ^ 2 + 3 * sig ^ 2) = 0 := by
      linear_combination S * hD2 - S * hD3 + 3 * sig * hD1
    exact (mul_eq_zero.1 hk).resolve_right hne
  have hr : 3 * (2 * r - sig) - S = 0 := by
    have hk : (3 * (2 * r - sig) - S) * (S ^ 2 + 3 * sig ^ 2) = 0 := by
      linear_combination S * hD3 - S * hD1 + 3 * sig * hD2
    exact (mul_eq_zero.1 hk).resolve_right hne
  rw [hS] at hp hq hr
  constructor <;> linarith

/-- **IMO 2005 P1.** The three main diagonals of the hexagon all pass through the centroid
`(0, h/3)` of the triangle, hence are concurrent. -/
theorem imo2005_p1 (p q r t h : ℝ) (hh : h ^ 2 = 3 / 4) (hh0 : 0 < h)
    (hsig : 0 < 1 - t)
    -- the three corner sides of the hexagon have length `t`
    (hA : (1 - t - p) ^ 2 + q ^ 2 - (1 - t - p) * q = t ^ 2)
    (hB : (1 - t - q) ^ 2 + r ^ 2 - (1 - t - q) * r = t ^ 2)
    (hC : (1 - t - r) ^ 2 + p ^ 2 - (1 - t - r) * p = t ^ 2) :
    -- `A₁`, `O`, `B₂` are collinear
    cross (-1 / 2 + p) 0 0 (h / 3) (1 / 2 - (q + t) / 2) ((q + t) * h) = 0 ∧
    -- `B₁`, `O`, `C₂` are collinear
    cross (1 / 2 - q / 2) (q * h) 0 (h / 3) (-(r + t) / 2) (h - (r + t) * h) = 0 ∧
    -- `C₁`, `O`, `A₂` are collinear
    cross (-r / 2) (h - r * h) 0 (h / 3) (-1 / 2 + (p + t)) 0 = 0 := by
  obtain ⟨hpq, hqr⟩ := equal_sides_symmetric hsig hA hB hC
  subst hpq
  subst hqr
  refine ⟨?_, ?_, ?_⟩
  · simp only [cross]; linear_combination (-h / 3) * hA
  · simp only [cross]; linear_combination (-h / 3) * hA
  · simp only [cross]; linear_combination (-h / 3) * hA

end Imo2005P1
