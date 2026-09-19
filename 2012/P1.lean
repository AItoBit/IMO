import Mathlib

/-!
# IMO 2012 Problem 1 — final metric core

The geometric proof establishes:

* `S`, `M`, `T` lie on `BC`;
* `JM ⟂ BC`;
* `J` is the circumcenter of triangle `AST`.

Choose Cartesian coordinates with `BC` as the x-axis.

Then write

    S = (s, 0)
    M = (m, 0)
    T = (t, 0)
    J = (m, j).

Since `J` is the circumcenter of triangle `AST`,

    JS = JT.

Squaring gives

    (m-s)^2 + j^2 = (m-t)^2 + j^2.

Since `S ≠ T`, this implies

    2m = s+t,

so `M` is the midpoint of `ST`.

No `sorry`, `admit`, or additional axioms are used.
-/

namespace IMO2012P1

abbrev Point := ℝ × ℝ

/-!
## Basic coordinate geometry
-/

/-- Squared Euclidean distance. -/
def sqDist (P Q : Point) : ℝ :=
  (P.1 - Q.1) ^ 2 + (P.2 - Q.2) ^ 2

/--
Euclidean midpoint in coordinates.

This is `noncomputable` because division on real numbers is
noncomputable in Lean.
-/
noncomputable def midpoint (P Q : Point) : Point :=
  ((P.1 + Q.1) / 2, (P.2 + Q.2) / 2)

/-!
## One-dimensional midpoint lemma
-/

/--
If two distinct real numbers `s,t` are equally far from `m`,
then `m` is their midpoint.
-/
lemma midpoint_coord_of_sq_eq
    {s m t : ℝ}
    (hst : s ≠ t)
    (h :
      (m - s) ^ 2 =
        (m - t) ^ 2) :
    m = (s + t) / 2 := by

  have hfactor :
      (t - s) * (2 * m - s - t) = 0 := by
    nlinarith [h]

  rcases mul_eq_zero.mp hfactor with hts | hmid

  · have hst' :
        s = t := by
      linarith

    exact False.elim (hst hst')

  · linarith

/--
The same result with an arbitrary common perpendicular component.

If

    (m-s)^2 + j^2 = (m-t)^2 + j^2,

then `m` is the midpoint coordinate of `s` and `t`.
-/
lemma midpoint_coord_of_equal_dist
    {s m t j : ℝ}
    (hst : s ≠ t)
    (h :
      (m - s) ^ 2 + j ^ 2 =
        (m - t) ^ 2 + j ^ 2) :
    m = (s + t) / 2 := by

  have hsquares :
      (m - s) ^ 2 =
        (m - t) ^ 2 := by
    linarith

  exact
    midpoint_coord_of_sq_eq
      hst
      hsquares

/-!
## Point-level formulation
-/

/--
Let

    S = (s,0)
    M = (m,0)
    T = (t,0)
    J = (m,j).

If `S ≠ T` and `JS² = JT²`, then `M` is the midpoint of `ST`.
-/
theorem midpoint_of_perpendicular_bisector_coordinates
    (s m t j : ℝ)
    (hst : s ≠ t)
    (heq :
      sqDist (m, j) (s, 0) =
        sqDist (m, j) (t, 0)) :
    ((m, 0) : Point) =
      midpoint (s, 0) (t, 0) := by

  have heq' :
      (m - s) ^ 2 + j ^ 2 =
        (m - t) ^ 2 + j ^ 2 := by
    simpa [sqDist] using heq

  have hm :
      m = (s + t) / 2 :=
    midpoint_coord_of_equal_dist
      hst
      heq'

  unfold midpoint

  apply Prod.ext

  · simpa using hm

  · norm_num

/-!
## Circumcenter formulation
-/

/--
The part of "J is the circumcenter of AST" needed for the
final step: J is equally distant from S and T.
-/
def EquidistantFromST
    (J S T : Point) : Prop :=
  sqDist J S = sqDist J T

/--
The exact final metric implication used in IMO 2012 Problem 1.
-/
theorem imo2012_p1_metric_core
    (s m t j : ℝ)
    (hst : s ≠ t)
    (hJ :
      EquidistantFromST
        (m, j)
        (s, 0)
        (t, 0)) :
    ((m, 0) : Point) =
      midpoint (s, 0) (t, 0) := by

  apply
    midpoint_of_perpendicular_bisector_coordinates
      s m t j hst

  exact hJ

/-!
## Segment-length consequences
-/

/--
Once

    m = (s+t)/2,

the directed differences to the endpoints are equal.
-/
lemma midpoint_differences
    {s m t : ℝ}
    (hm :
      m = (s + t) / 2) :
    m - s = t - m := by

  linarith

/--
Therefore the ordinary distances `SM` and `MT` are equal.
-/
lemma midpoint_abs_distances
    {s m t : ℝ}
    (hm :
      m = (s + t) / 2) :
    |m - s| = |t - m| := by

  have h :
      m - s = t - m :=
    midpoint_differences hm

  rw [h]

/-!
## Final theorem
-/

/--
Coordinate form of the final step of IMO 2012 Problem 1.

If

    J = (m,j),
    S = (s,0),
    T = (t,0),

with `S ≠ T`, and J is equally distant from S and T,
then

    m = (s+t)/2,

so `M = (m,0)` is the midpoint of ST.
-/
theorem imo2012_p1
    (s m t j : ℝ)
    (hst : s ≠ t)
    (hJ :
      sqDist (m, j) (s, 0) =
        sqDist (m, j) (t, 0)) :
    m = (s + t) / 2 := by

  have heq :
      (m - s) ^ 2 + j ^ 2 =
        (m - t) ^ 2 + j ^ 2 := by
    simpa [sqDist] using hJ

  exact
    midpoint_coord_of_equal_dist
      hst
      heq

/--
Point-valued final conclusion: `M` itself equals the midpoint of `ST`.
-/
theorem imo2012_p1_midpoint
    (s m t j : ℝ)
    (hst : s ≠ t)
    (hJ :
      sqDist (m, j) (s, 0) =
        sqDist (m, j) (t, 0)) :
    ((m, 0) : Point) =
      midpoint (s, 0) (t, 0) := by

  exact
    midpoint_of_perpendicular_bisector_coordinates
      s m t j hst hJ

end IMO2012P1
