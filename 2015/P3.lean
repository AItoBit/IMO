import Mathlib

namespace IMO2015P3

/-!
# IMO 2015 Problem 3 — final tangency core

The source reduces the problem by inversion to the following
elementary fact.

Let `O` be the circumcenter of triangle `ALQ`.

If

    LA = LQ

and

    ML ∥ AQ,

then both `O` and `L` lie on the perpendicular bisector of `AQ`.
Consequently

    OL ⟂ AQ.

Since

    ML ∥ AQ,

we obtain

    OL ⟂ ML.

Thus `ML` is tangent at `L` to the circumcircle of `ALQ`.

We prove this using Cartesian coordinates.

No `sorry`, `admit`, or additional axioms are used.
-/

abbrev Point := ℝ × ℝ

/-!
## Basic vector operations
-/

def vec (P Q : Point) : Point :=
  (Q.1 - P.1, Q.2 - P.2)

def dot (u v : Point) : ℝ :=
  u.1 * v.1 + u.2 * v.2

def distSq (P Q : Point) : ℝ :=
  (Q.1 - P.1) ^ 2 +
  (Q.2 - P.2) ^ 2

/-!
## Perpendicularity
-/

def Perpendicular
    (P Q R S : Point) : Prop :=
  dot (vec P Q) (vec R S) = 0

/-!
## Parallelism

For the proof we use the scalar-multiple formulation:
the directed vector `PQ` is a real multiple of `RS`.
-/

def Parallel
    (P Q R S : Point) : Prop :=
  ∃ c : ℝ,
    Q.1 - P.1 =
      c * (S.1 - R.1) ∧
    Q.2 - P.2 =
      c * (S.2 - R.2)

/-!
## Circumcenter
-/

/--
`O` is the circumcenter of `A,L,Q`.
-/
def IsCircumcenter
    (O A L Q : Point) : Prop :=
  distSq O A = distSq O L ∧
  distSq O L = distSq O Q

/-!
## Tangency

A line `LM` is tangent at `L` to a circle centered at `O`
when the radius `OL` is perpendicular to `LM`.
-/

def TangentAt
    (O L M : Point) : Prop :=
  Perpendicular O L L M

/-!
## Equal distances
-/

/--
If `O` is the circumcenter of `A,L,Q`, then

    OA² = OQ².
-/
lemma circumcenter_AQ
    {O A L Q : Point}
    (hO :
      IsCircumcenter O A L Q) :
    distSq O A = distSq O Q := by

  exact hO.1.trans hO.2

/-!
## Perpendicular-bisector calculation
-/

/--
If both `O` and `L` are equidistant from `A` and `Q`,
then `OL` is perpendicular to `AQ`.

This is the analytic form of:

"two points on the perpendicular bisector of AQ determine
the perpendicular-bisector line."
-/
lemma perpendicular_of_two_equidistant_points
    {O L A Q : Point}
    (hO :
      distSq O A = distSq O Q)
    (hL :
      distSq L A = distSq L Q) :
    Perpendicular O L A Q := by

  unfold Perpendicular dot vec distSq at *

  ring_nf at hO hL ⊢

  nlinarith [hO, hL]

/-!
## Perpendicularity transfers across parallel lines
-/

/--
If `OL ⟂ AQ` and `LM ∥ AQ`, then `OL ⟂ LM`.
-/
lemma perpendicular_of_parallel
    {O L M A Q : Point}
    (hperp :
      Perpendicular O L A Q)
    (hparallel :
      Parallel L M A Q) :
    Perpendicular O L L M := by

  rcases hparallel with
    ⟨c, hx, hy⟩

  unfold Perpendicular dot vec at hperp ⊢

  rw [hx, hy]

  calc
    (L.1 - O.1) *
          (c * (Q.1 - A.1)) +
        (L.2 - O.2) *
          (c * (Q.2 - A.2))
        =
      c *
        ((L.1 - O.1) * (Q.1 - A.1) +
         (L.2 - O.2) * (Q.2 - A.2)) := by
          ring

    _ = 0 := by
      rw [hperp]
      ring

/-!
## The exact final lemma used after the source's angle chasing
-/

/--
If

* `O` is the circumcenter of `ALQ`,
* `LA = LQ`,
* `ML ∥ AQ`,

then `ML` is tangent at `L` to the circumcircle of `ALQ`.
-/
theorem tangent_of_isosceles_and_parallel
    {O A L Q M : Point}
    (hcenter :
      IsCircumcenter O A L Q)
    (hisos :
      distSq L A = distSq L Q)
    (hparallel :
      Parallel L M A Q) :
    TangentAt O L M := by

  have hOAQ :
      distSq O A = distSq O Q :=
    circumcenter_AQ hcenter

  have hOLperp :
      Perpendicular O L A Q :=
    perpendicular_of_two_equidistant_points
      hOAQ
      hisos

  have hOLML :
      Perpendicular O L L M :=
    perpendicular_of_parallel
      hOLperp
      hparallel

  exact hOLML

/-!
## Midpoint machinery from the source
-/

def IsMidpoint
    (M A B : Point) : Prop :=
  M.1 = (A.1 + B.1) / 2 ∧
  M.2 = (A.2 + B.2) / 2

/--
If `T` is the midpoint of `HA` and `N` is the midpoint
of `HQ`, then

    2 * TN = AQ

coordinatewise.
-/
lemma midpoint_segment_double
    {H A Q T N : Point}
    (hT :
      IsMidpoint T H A)
    (hN :
      IsMidpoint N H Q) :
    2 * (N.1 - T.1) =
        Q.1 - A.1 ∧
    2 * (N.2 - T.2) =
        Q.2 - A.2 := by

  rcases hT with ⟨hTx, hTy⟩
  rcases hN with ⟨hNx, hNy⟩

  constructor

  · rw [hTx, hNx]
    ring

  · rw [hTy, hNy]
    ring

/-!
## Rectangle/parallelogram relation
-/

/--
For the source's rectangle `TNML`, the opposite directed
sides `TN` and `LM` agree.
-/
def OppositeSidesEqual
    (T N M L : Point) : Prop :=
  M.1 - L.1 = N.1 - T.1 ∧
  M.2 - L.2 = N.2 - T.2

/--
The midpoint relation together with the rectangle relation
implies

    LM ∥ AQ.

In fact,

    LM = (1/2) AQ.
-/
lemma parallel_AQ_of_midpoints_rectangle
    {H A Q T N M L : Point}
    (hT :
      IsMidpoint T H A)
    (hN :
      IsMidpoint N H Q)
    (hrect :
      OppositeSidesEqual T N M L) :
    Parallel L M A Q := by

  have hdouble :
      2 * (N.1 - T.1) =
          Q.1 - A.1 ∧
      2 * (N.2 - T.2) =
          Q.2 - A.2 :=
    midpoint_segment_double hT hN

  rcases hdouble with
    ⟨hx2, hy2⟩

  rcases hrect with
    ⟨hxrect, hyrect⟩

  refine ⟨(1 : ℝ) / 2, ?_, ?_⟩

  · rw [hxrect]
    linarith

  · rw [hyrect]
    linarith

/-!
## Source-style final package
-/

/--
This packages the final portion of the source proof.

The source has already established:

* `T` is the midpoint of `HA`;
* `N` is the midpoint of `HQ`;
* `TNML` is a rectangle;
* `L` lies on the perpendicular bisector of `AQ`.

The first three imply `ML ∥ AQ`, and the fourth gives
`LA = LQ`.

Hence `ML` is tangent to the circumcircle of `ALQ`.
-/
theorem imo2015_p3_inversion_target
    {H A Q T N M L O : Point}
    (hT :
      IsMidpoint T H A)
    (hN :
      IsMidpoint N H Q)
    (hrect :
      OppositeSidesEqual T N M L)
    (hcenter :
      IsCircumcenter O A L Q)
    (hLbisector :
      distSq L A = distSq L Q) :
    TangentAt O L M := by

  have hparallel :
      Parallel L M A Q :=
    parallel_AQ_of_midpoints_rectangle
      hT
      hN
      hrect

  exact
    tangent_of_isosceles_and_parallel
      hcenter
      hLbisector
      hparallel

/-!
## Explicit dot-product form
-/

/--
Expanded version of the final perpendicularity statement.
-/
lemma tangent_dot_product
    {O A L Q M : Point}
    (hcenter :
      IsCircumcenter O A L Q)
    (hisos :
      distSq L A = distSq L Q)
    (hparallel :
      Parallel L M A Q) :
    (L.1 - O.1) * (M.1 - L.1) +
      (L.2 - O.2) * (M.2 - L.2)
      =
    0 := by

  have h :
      TangentAt O L M :=
    tangent_of_isosceles_and_parallel
      hcenter
      hisos
      hparallel

  exact h

/-!
## A useful independent geometric identity
-/

/--
Equal squared distances are equivalent to the usual
equal-distance condition after squaring; this is the form
that is easiest for polynomial automation.
-/
lemma equidistant_difference
    {P A Q : Point}
    (h :
      distSq P A =
        distSq P Q) :
    2 * P.1 * (Q.1 - A.1) +
        2 * P.2 * (Q.2 - A.2)
      =
    (Q.1 ^ 2 + Q.2 ^ 2) -
      (A.1 ^ 2 + A.2 ^ 2) := by

  unfold distSq at h

  ring_nf at h ⊢

  linarith

end IMO2015P3
