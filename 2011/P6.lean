import Mathlib

/-!
# IMO 2011 Problem 6 — coordinate tangency core

The source solution normalizes the original circumcircle to the unit
circle centered at the origin.

Its final observation is:

* the circumcircle Ω of the triangle determined by the three reflected
  lines intersects the unit circle Γ at a point `P`;
* the center of Ω, `P`, and the origin are collinear.

For two nondegenerate circles, this means that their common point lies
on the line joining their centers, hence the circles are tangent there.

The theorem below proves this final analytic statement algebraically.

We represent a point by a pair of real coordinates.
-/

namespace IMO2011P6

abbrev Point := ℝ × ℝ

/-! ## Elementary coordinate operations -/

/-- Squared Euclidean norm. -/
def sqNorm (P : Point) : ℝ :=
  P.1 ^ 2 + P.2 ^ 2

/-- Dot product. -/
def dot (P Q : Point) : ℝ :=
  P.1 * Q.1 + P.2 * Q.2

/-- Scalar multiplication of a point/vector. -/
def scale (t : ℝ) (P : Point) : Point :=
  (t * P.1, t * P.2)

/-- Squared Euclidean distance. -/
def sqDist (P Q : Point) : ℝ :=
  (P.1 - Q.1) ^ 2 + (P.2 - Q.2) ^ 2

/-- Membership in the unit circle centered at `(0,0)`. -/
def OnUnitCircle (P : Point) : Prop :=
  sqNorm P = 1

/--
Membership in a circle specified by its center and squared radius.
-/
def OnCircleSq
    (C : Point)
    (r2 : ℝ)
    (P : Point) : Prop :=
  sqDist P C = r2

/-!
## The normalized tangent `y = 1`
-/

/--
The horizontal line `y = 1` meets the unit circle only at `(0,1)`.

Thus in the normalized coordinates used by the source it is tangent
to the unit circle.
-/
lemma unitCircle_inter_y_one
    {P : Point}
    (hP : OnUnitCircle P)
    (hy : P.2 = 1) :
    P = (0, 1) := by

  rcases P with ⟨x, y⟩

  simp only [OnUnitCircle, sqNorm] at hP
  simp only at hy

  have hx :
      x = 0 := by
    nlinarith [sq_nonneg x]

  ext

  · exact hx

  · exact hy

/-!
## Circle with center on the radial line OP
-/

/--
Suppose `P` lies on the unit circle.

If the center of a second circle is

    C = lam P,

then the squared radius required for that second circle to pass
through `P` is

    (1 - lam)^2.
-/
lemma point_on_radial_circle
    (P : Point)
    (lam : ℝ)
    (hP : OnUnitCircle P) :
    OnCircleSq
      (scale lam P)
      ((1 - lam) ^ 2)
      P := by

  rcases P with ⟨x, y⟩

  simp only [
    OnUnitCircle,
    OnCircleSq,
    sqNorm,
    sqDist,
    scale
  ] at hP ⊢

  nlinarith [hP]

/--
Core tangency lemma.

Let `P` lie on the unit circle and let `lam ≠ 0`.

Consider the circle centered at `lam P` and passing through `P`.
Then `P` is the only common point of this circle and the unit circle.
-/
lemma radial_circle_unique_intersection
    (P : Point)
    (lam : ℝ)
    (hlam : lam ≠ 0)
    (hP : OnUnitCircle P) :
    ∀ Q : Point,
      OnUnitCircle Q →
      OnCircleSq
        (scale lam P)
        ((1 - lam) ^ 2)
        Q →
      Q = P := by

  intro Q hQ hQ₂

  rcases P with ⟨px, py⟩
  rcases Q with ⟨qx, qy⟩

  simp only [
    OnUnitCircle,
    OnCircleSq,
    sqNorm,
    sqDist,
    scale
  ] at hP hQ hQ₂ ⊢

  /-
  From the second circle equation:
      (qx - lam*px)^2 + (qy - lam*py)^2 = (1-lam)^2.
  -/
  have hzero :
      ((qx - lam * px) ^ 2 +
          (qy - lam * py) ^ 2) -
        (1 - lam) ^ 2 = 0 := by
    linarith [hQ₂]

  /-
  Expand the difference polynomially.
  -/
  have hexpand :
      ((qx - lam * px) ^ 2 +
          (qy - lam * py) ^ 2) -
        (1 - lam) ^ 2
        =
      (qx ^ 2 + qy ^ 2 - 1)
        + lam ^ 2 * (px ^ 2 + py ^ 2 - 1)
        - 2 * lam *
            (qx * px + qy * py - 1) := by
    ring

  rw [hexpand] at hzero
  rw [hQ, hP] at hzero

  /-
  Hence

      lam * (Q·P - 1) = 0.
  -/
  have hprod :
      lam * (qx * px + qy * py - 1) = 0 := by
    nlinarith

  /-
  Since `lam ≠ 0`, we get

      Q·P = 1.
  -/
  have hdot :
      qx * px + qy * py = 1 := by

    rcases mul_eq_zero.mp hprod with hLam | hDot

    · exact False.elim (hlam hLam)

    · linarith

  /-
  Since both P and Q are unit vectors and have dot product 1,

      ||Q-P||² = 0.
  -/
  have hdist :
      (qx - px) ^ 2 +
        (qy - py) ^ 2 = 0 := by
    nlinarith [hP, hQ, hdot]

  have hxzero :
      (qx - px) ^ 2 = 0 := by

    have hxnonneg :
        0 ≤ (qx - px) ^ 2 :=
      sq_nonneg (qx - px)

    have hynonneg :
        0 ≤ (qy - py) ^ 2 :=
      sq_nonneg (qy - py)

    nlinarith [hdist]

  have hyzero :
      (qy - py) ^ 2 = 0 := by

    have hxnonneg :
        0 ≤ (qx - px) ^ 2 :=
      sq_nonneg (qx - px)

    have hynonneg :
        0 ≤ (qy - py) ^ 2 :=
      sq_nonneg (qy - py)

    nlinarith [hdist]

  have hx :
      qx = px := by
    nlinarith [hxzero]

  have hy :
      qy = py := by
    nlinarith [hyzero]

  exact Prod.ext hx hy

/-!
## Tangency predicate
-/

/--
Two circles are tangent at `P` in the set-theoretic sense used here
if `P` lies on both circles and is their unique common point.
-/
def TangentToUnitAt
    (C : Point)
    (r2 : ℝ)
    (P : Point) : Prop :=
  OnUnitCircle P ∧
  OnCircleSq C r2 P ∧
  ∀ Q : Point,
    OnUnitCircle Q →
    OnCircleSq C r2 Q →
    Q = P

/--
A circle whose center is a nonzero scalar multiple of a common unit
point is tangent to the unit circle there.
-/
theorem tangent_of_radial_center
    (P : Point)
    (lam : ℝ)
    (hlam : lam ≠ 0)
    (hP : OnUnitCircle P) :
    TangentToUnitAt
      (scale lam P)
      ((1 - lam) ^ 2)
      P := by

  refine ⟨hP, ?_, ?_⟩

  · exact
      point_on_radial_circle
        P lam hP

  · intro Q hQU hQC

    exact
      radial_circle_unique_intersection
        P lam hlam hP Q hQU hQC

/-!
## Final coordinate core corresponding to IMO 2011 P6
-/

/--
Suppose the coordinate computation for the three reflected lines has
produced:

* `P`, a common point of the original unit circle and the new circle;
* a nonzero real `lam` such that the new circumcenter is `lam P`.

Then the new circumcircle is tangent to the original unit circle.
-/
theorem imo2011_p6_coordinate_core
    (P : Point)
    (lam : ℝ)
    (hlam : lam ≠ 0)
    (hP : OnUnitCircle P) :
    TangentToUnitAt
      (scale lam P)
      ((1 - lam) ^ 2)
      P := by

  exact
    tangent_of_radial_center
      P lam hlam hP

end IMO2011P6
