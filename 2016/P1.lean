import Mathlib

namespace IMO2016P1

/-!
# IMO 2016 Problem 1 — symmetry/concurrency core

The source eventually proves:

* `B` and `X` are symmetric with respect to `ME`;
* `D` and `F` are symmetric with respect to `ME`.

Thus reflection in `ME` sends line `BD` to line `FX`.

We choose coordinates so that `ME` is the y-axis.

No `sorry`, `admit`, or additional axioms are used.
-/

abbrev Point := ℝ × ℝ

/-!
## Reflection
-/

/--
Reflection in the y-axis.
-/
def reflectAxis (P : Point) : Point :=
  (-P.1, P.2)

/--
A point lies on the symmetry axis.
-/
def OnAxis (P : Point) : Prop :=
  P.1 = 0

/-!
## Collinearity
-/

/--
Three points are collinear when their determinant vanishes.
-/
def Collinear
    (P Q R : Point) : Prop :=
  (Q.1 - P.1) * (R.2 - P.2) -
    (Q.2 - P.2) * (R.1 - P.1) = 0

/-!
## Affine points on a line
-/

def affinePoint
    (P Q : Point)
    (t : ℝ) : Point :=
  ((1 - t) * P.1 + t * Q.1,
   (1 - t) * P.2 + t * Q.2)

/--
Every affine combination of `P,Q` lies on line `PQ`.
-/
lemma collinear_affinePoint
    (P Q : Point)
    (t : ℝ) :
    Collinear P Q (affinePoint P Q t) := by

  unfold Collinear affinePoint
  dsimp
  ring

/-!
## Reflection properties
-/

/--
Reflection is an involution.
-/
lemma reflectAxis_involutive
    (P : Point) :
    reflectAxis (reflectAxis P) = P := by

  ext <;> simp [reflectAxis]

/--
A point on the y-axis is fixed by reflection.
-/
lemma reflectAxis_fixed
    {P : Point}
    (hP : OnAxis P) :
    reflectAxis P = P := by

  unfold OnAxis at hP

  ext

  · simp [reflectAxis, hP]

  · simp [reflectAxis]

/--
Reflection commutes with affine combinations.
-/
lemma reflectAxis_affinePoint
    (P Q : Point)
    (t : ℝ) :
    reflectAxis (affinePoint P Q t)
      =
    affinePoint
      (reflectAxis P)
      (reflectAxis Q)
      t := by

  ext

  · simp [reflectAxis, affinePoint]
    ring

  · simp [reflectAxis, affinePoint]

/--
Reflection preserves collinearity.
-/
lemma collinear_reflectAxis
    {P Q R : Point}
    (h : Collinear P Q R) :
    Collinear
      (reflectAxis P)
      (reflectAxis Q)
      (reflectAxis R) := by

  unfold Collinear at h ⊢

  simp [reflectAxis]

  ring_nf at h ⊢

  linarith

/-!
## Constructing the intersection with the axis
-/

/--
If the x-coordinates of `B,D` are different,
then line `BD` intersects the y-axis.
-/
lemma exists_axis_point_on_line
    {B D : Point}
    (hBD :
      B.1 ≠ D.1) :
    ∃ P : Point,
      OnAxis P ∧
      Collinear B D P := by

  have hden :
      B.1 - D.1 ≠ 0 := by

    exact
      sub_ne_zero.mpr
        hBD

  let t : ℝ :=
    B.1 / (B.1 - D.1)

  let P : Point :=
    affinePoint B D t

  have hPx :
      P.1 = 0 := by

    dsimp [P, t, affinePoint]

    field_simp [hden]

    ring

  refine ⟨P, ?_, ?_⟩

  · exact hPx

  · exact
      collinear_affinePoint
        B
        D
        t

/-!
## A line and its reflection
-/

/--
The line `BD` and its reflected line have a common point
on the reflection axis.
-/
theorem symmetric_lines_concurrent_on_axis
    (B D : Point)
    (hBD :
      B.1 ≠ D.1) :
    ∃ P : Point,
      Collinear B D P ∧
      Collinear
        (reflectAxis B)
        (reflectAxis D)
        P ∧
      OnAxis P := by

  obtain ⟨P, haxis, hBDP⟩ :=
    exists_axis_point_on_line
      hBD

  have href :
      reflectAxis P = P :=
    reflectAxis_fixed
      haxis

  have hrefcol :
      Collinear
        (reflectAxis B)
        (reflectAxis D)
        (reflectAxis P) :=
    collinear_reflectAxis
      hBDP

  rw [href] at hrefcol

  exact
    ⟨P,
     hBDP,
     hrefcol,
     haxis⟩

/-!
## Swapping the first two points
-/

/--
Collinearity is preserved when the first two points are swapped.
-/
lemma collinear_swap_first
    {P Q R : Point}
    (h :
      Collinear P Q R) :
    Collinear Q P R := by

  unfold Collinear at h ⊢

  ring_nf at h ⊢

  linarith

/-!
## Matching the IMO notation
-/

/--
Assume

    X = reflection(B)
    F = reflection(D).

Then `BD` and `FX` meet on the symmetry axis.
-/
theorem imo2016_p1_symmetry_core
    (B D F X : Point)
    (hBD :
      B.1 ≠ D.1)
    (hX :
      X = reflectAxis B)
    (hF :
      F = reflectAxis D) :
    ∃ P : Point,
      Collinear B D P ∧
      Collinear F X P ∧
      OnAxis P := by

  obtain ⟨P, hBDP, hrefP, haxis⟩ :=
    symmetric_lines_concurrent_on_axis
      B
      D
      hBD

  have hFXP :
      Collinear
        (reflectAxis D)
        (reflectAxis B)
        P :=
    collinear_swap_first
      hrefP

  rw [hF, hX]

  exact
    ⟨P,
     hBDP,
     hFXP,
     haxis⟩

/-!
## Reflection maps lines to reflected lines
-/

/--
If `P` lies on `BD`, then its reflection lies on the line
through the reflections of `B,D`.
-/
lemma reflected_line_contains_reflection
    {B D P : Point}
    (hP :
      Collinear B D P) :
    Collinear
      (reflectAxis B)
      (reflectAxis D)
      (reflectAxis P) := by

  exact
    collinear_reflectAxis
      hP

/-!
## A common point of genuinely distinct reflected lines
-/

/--
Suppose `P` lies on both `BD` and its reflected line.

If `B.2 ≠ D.2`, then the original and reflected lines
cannot coincide as one horizontal line. Hence their common
point must lie on the symmetry axis.
-/
lemma intersection_fixed_by_reflection
    {B D P : Point}
    (hBDy :
      B.2 ≠ D.2)
    (h₁ :
      Collinear B D P)
    (h₂ :
      Collinear
        (reflectAxis B)
        (reflectAxis D)
        P) :
    OnAxis P := by

  unfold Collinear at h₁ h₂
  unfold OnAxis

  simp [reflectAxis] at h₂

  have hproduct :
      P.1 * (D.2 - B.2) = 0 := by

    nlinarith [h₁, h₂]

  have hdiff :
      D.2 - B.2 ≠ 0 := by

    exact
      sub_ne_zero.mpr
        (Ne.symm hBDy)

  exact
    (mul_eq_zero.mp hproduct).resolve_right
      hdiff

/-!
## Coordinate form of the constructed concurrency point
-/

/--
Explicit parameter used to intersect `BD` with the y-axis.
-/
noncomputable def axisParameter
    (B D : Point) : ℝ :=
  B.1 / (B.1 - D.1)

/--
Explicit point on `BD` used in the construction.
-/
noncomputable def axisIntersection
    (B D : Point) : Point :=
  affinePoint B D (axisParameter B D)

/--
When `B.1 ≠ D.1`, the explicit intersection really lies
on the symmetry axis.
-/
lemma axisIntersection_onAxis
    {B D : Point}
    (hBD :
      B.1 ≠ D.1) :
    OnAxis (axisIntersection B D) := by

  unfold axisIntersection axisParameter OnAxis affinePoint

  dsimp

  have hden :
      B.1 - D.1 ≠ 0 :=
    sub_ne_zero.mpr hBD

  field_simp [hden]

  ring

/--
The explicit intersection also lies on `BD`.
-/
lemma axisIntersection_onLine
    (B D : Point) :
    Collinear
      B
      D
      (axisIntersection B D) := by

  unfold axisIntersection

  exact
    collinear_affinePoint
      B
      D
      (axisParameter B D)

/-!
## Source-style final theorem
-/

/--
Final concurrency theorem corresponding to the last step of
Solution 2 of IMO 2016 Problem 1.

If reflection in `ME` exchanges

    B ↔ X
    D ↔ F,

then `BD`, `FX`, and `ME` are concurrent.

The coordinate system is chosen so that `ME` is the y-axis.
-/
theorem imo2016_p1_final
    (B D F X : Point)
    (hB_X :
      X = reflectAxis B)
    (hD_F :
      F = reflectAxis D)
    (hBD :
      B.1 ≠ D.1) :
    ∃ P : Point,
      Collinear B D P ∧
      Collinear F X P ∧
      OnAxis P := by

  exact
    imo2016_p1_symmetry_core
      B
      D
      F
      X
      hBD
      hB_X
      hD_F

end IMO2016P1
