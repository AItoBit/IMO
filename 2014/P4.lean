import Mathlib

namespace IMO2014P4

/-!
# IMO 2014 Problem 4 — barycentric algebraic core



In barycentric coordinates with respect to triangle ABC:

    A = (1 : 0 : 0)
    B = (0 : 1 : 0)
    C = (0 : 0 : 1)

The source obtains

    M = (-a² : 2a² - 2c² : 2c²)
    N = (-a² : 2b² : 2a² - 2b²)

and claims that BM and CN intersect at

    D = (-a² : 2b² : 2c²).

The circumcircle of ABC has barycentric equation

    a² y z + b² z x + c² x y = 0.

We verify algebraically:

* B, M, D are collinear;
* C, N, D are collinear;
* D lies on the circumcircle.

Thus the common point of BM and CN lies on the circumcircle.
-/

/-!
## Barycentric points
-/

structure BaryPoint where
  x : ℝ
  y : ℝ
  z : ℝ

/-!
## Basic triangle vertices
-/

def pointA : BaryPoint :=
  ⟨1, 0, 0⟩

def pointB : BaryPoint :=
  ⟨0, 1, 0⟩

def pointC : BaryPoint :=
  ⟨0, 0, 1⟩

/-!
## Points M, N, D from the source
-/

def pointM
    (a c : ℝ) :
    BaryPoint :=
  ⟨-(a ^ 2),
   2 * a ^ 2 - 2 * c ^ 2,
   2 * c ^ 2⟩

def pointN
    (a b : ℝ) :
    BaryPoint :=
  ⟨-(a ^ 2),
   2 * b ^ 2,
   2 * a ^ 2 - 2 * b ^ 2⟩

def pointD
    (a b c : ℝ) :
    BaryPoint :=
  ⟨-(a ^ 2),
   2 * b ^ 2,
   2 * c ^ 2⟩

/-!
## Collinearity in homogeneous coordinates
-/

/--
The determinant of three homogeneous coordinate triples.
-/
def det3
    (P Q R : BaryPoint) : ℝ :=
  P.x * (Q.y * R.z - Q.z * R.y)
  - P.y * (Q.x * R.z - Q.z * R.x)
  + P.z * (Q.x * R.y - Q.y * R.x)

/--
Three barycentric points are collinear when their
3 × 3 determinant vanishes.
-/
def Collinear
    (P Q R : BaryPoint) : Prop :=
  det3 P Q R = 0

/-!
## D lies on BM
-/

lemma D_on_BM
    (a b c : ℝ) :
    Collinear
      pointB
      (pointM a c)
      (pointD a b c) := by

  unfold Collinear det3
  simp [pointB, pointM, pointD]
  ring

/-!
## D lies on CN
-/

lemma D_on_CN
    (a b c : ℝ) :
    Collinear
      pointC
      (pointN a b)
      (pointD a b c) := by

  unfold Collinear det3
  simp [pointC, pointN, pointD]
  ring

/-!
## Circumcircle equation
-/

/--
The barycentric equation of the circumcircle of ABC:

    a² y z + b² z x + c² x y = 0.
-/
def OnCircumcircle
    (a b c : ℝ)
    (P : BaryPoint) : Prop :=
  a ^ 2 * P.y * P.z
  + b ^ 2 * P.z * P.x
  + c ^ 2 * P.x * P.y
  = 0

/-!
## D lies on the circumcircle
-/

/--
Substitution of

    D = (-a² : 2b² : 2c²)

into

    a²yz + b²zx + c²xy = 0

gives

    4a²b²c²
      - 2a²b²c²
      - 2a²b²c²
    = 0.
-/
lemma D_on_circumcircle
    (a b c : ℝ) :
    OnCircumcircle
      a b c
      (pointD a b c) := by

  unfold OnCircumcircle pointD
  simp
  ring

/-!
## Combined result
-/

/--
The barycentric core of IMO 2014 Problem 4.

The point

    D = (-a² : 2b² : 2c²)

lies simultaneously on BM, on CN, and on the
circumcircle of ABC.
-/
theorem imo2014_p4_barycentric_core
    (a b c : ℝ) :
    Collinear
        pointB
        (pointM a c)
        (pointD a b c)
    ∧
    Collinear
        pointC
        (pointN a b)
        (pointD a b c)
    ∧
    OnCircumcircle
        a b c
        (pointD a b c) := by

  constructor

  · exact D_on_BM a b c

  · constructor

    · exact D_on_CN a b c

    · exact D_on_circumcircle a b c

/-!
## An explicit substitution identity
-/

/--
The exact polynomial cancellation appearing when D is
substituted into the circumcircle equation.
-/
lemma circumcircle_substitution_identity
    (a b c : ℝ) :
    a ^ 2 * (2 * b ^ 2) * (2 * c ^ 2)
      +
    b ^ 2 * (2 * c ^ 2) * (-(a ^ 2))
      +
    c ^ 2 * (-(a ^ 2)) * (2 * b ^ 2)
      =
    0 := by
  ring

/-!
## Explicit line determinant identities
-/

/--
The determinant for B, M, D vanishes identically.
-/
lemma BM_determinant
    (a b c : ℝ) :
    det3
      pointB
      (pointM a c)
      (pointD a b c)
      =
    0 := by

  simp [det3, pointB, pointM, pointD]
  ring

/--
The determinant for C, N, D vanishes identically.
-/
lemma CN_determinant
    (a b c : ℝ) :
    det3
      pointC
      (pointN a b)
      (pointD a b c)
      =
    0 := by

  simp [det3, pointC, pointN, pointD]
  ring

/-!
## Abstract final form
-/

/--
If a point `D` is simultaneously on `BM`, on `CN`,
and on the circumcircle, then the intersection represented
by `D` lies on the circumcircle.

This packages the final incidence statement.
-/
theorem common_point_on_circumcircle
    {a b c : ℝ}
    {B C M N D : BaryPoint}
    (hBM :
      Collinear B M D)
    (hCN :
      Collinear C N D)
    (hcircle :
      OnCircumcircle a b c D) :
    Collinear B M D ∧
    Collinear C N D ∧
    OnCircumcircle a b c D := by

  exact ⟨hBM, hCN, hcircle⟩

/-!
## Final packaged theorem
-/

theorem imo2014_p4
    (a b c : ℝ) :
    let B := pointB
    let C := pointC
    let M := pointM a c
    let N := pointN a b
    let D := pointD a b c

    Collinear B M D ∧
    Collinear C N D ∧
    OnCircumcircle a b c D := by

  dsimp

  exact
    imo2014_p4_barycentric_core
      a b c

end IMO2014P4
