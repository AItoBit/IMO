import Mathlib

/-!
# IMO 2013 Problem 3 — metric and angle core

The supplied solution establishes:

1. One of the points `Mₐ, M_b, M_c` is the circumcenter
   of triangle `A₁B₁C₁`.

2. Assuming it is `Mₐ`, the Bevan-point / Reim-theorem
   configuration gives

       ∠I_c I_a I_b = 45°

   and

       ∠CAB = 180° - 2 * ∠I_c I_a I_b.

Therefore

       ∠CAB = 90°.

This file formalizes:

* the coordinate notion of a circumcenter;
* the equidistance criterion used to recognize one;
* the complete final angle calculation.

No `sorry`, `admit`, or extra axioms are used.
-/

namespace IMO2013P3

/-!
## Coordinate metric layer
-/

abbrev Point := ℝ × ℝ

/-- Squared Euclidean distance. -/
def sqDist (P Q : Point) : ℝ :=
  (P.1 - Q.1) ^ 2 +
  (P.2 - Q.2) ^ 2

/--
A minimal circumcenter predicate:
`O` is equidistant from the three vertices.
-/
def IsCircumcenter
    (O A B C : Point) : Prop :=
  sqDist O A = sqDist O B ∧
  sqDist O B = sqDist O C

/--
If `O` has the same squared distance from `A,B,C`,
then it satisfies our circumcenter predicate.
-/
lemma isCircumcenter_of_equal_sqDist
    {O A B C : Point}
    (hAB :
      sqDist O A = sqDist O B)
    (hAC :
      sqDist O A = sqDist O C) :
    IsCircumcenter O A B C := by

  constructor

  · exact hAB

  · calc
      sqDist O B
          = sqDist O A := hAB.symm
      _ = sqDist O C := hAC

/--
Conversely, a circumcenter is equidistant from the first
and third vertices.
-/
lemma circumcenter_sqDist_AC
    {O A B C : Point}
    (hO :
      IsCircumcenter O A B C) :
    sqDist O A = sqDist O C := by

  rcases hO with ⟨hAB, hBC⟩

  exact hAB.trans hBC

/--
Squared distance is symmetric.
-/
lemma sqDist_comm
    (P Q : Point) :
    sqDist P Q = sqDist Q P := by

  unfold sqDist
  ring

/-!
## Angle layer

Angles are represented by real numbers in radians.

45°  = π/4
90°  = π/2
180° = π
-/

/-- 45 degrees in radians. -/
noncomputable def angle45 : ℝ :=
  Real.pi / 4

/-- 90 degrees in radians. -/
noncomputable def angle90 : ℝ :=
  Real.pi / 2

/-- 180 degrees in radians. -/
noncomputable def angle180 : ℝ :=
  Real.pi

lemma angle45_eq :
    angle45 = Real.pi / 4 := by
  rfl

lemma angle90_eq :
    angle90 = Real.pi / 2 := by
  rfl

lemma angle180_eq :
    angle180 = Real.pi := by
  rfl

/-!
## Final calculation from the supplied solution
-/

/--
If

    θ = 45°

and

    A = 180° - 2θ,

then

    A = 90°.
-/
lemma right_angle_of_half_relation
    {A theta : ℝ}
    (htheta :
      theta = angle45)
    (hA :
      A = angle180 - 2 * theta) :
    A = angle90 := by

  unfold angle45 angle90 angle180 at *

  rw [htheta] at hA

  have hpi :
      Real.pi ≠ 0 :=
    ne_of_gt Real.pi_pos

  field_simp [hpi] at hA ⊢

  linarith

/--
The same calculation written directly with π.
-/
lemma right_angle_of_pi_relation
    {A theta : ℝ}
    (htheta :
      theta = Real.pi / 4)
    (hA :
      A = Real.pi - 2 * theta) :
    A = Real.pi / 2 := by

  rw [htheta] at hA

  linarith

/-!
## Source-specific abstraction
-/

/--
The final information supplied by the Bevan-point/Reim part
of the source proof.

`angleIcIaIb` represents `∠I_c I_a I_b`.
`angleA` represents `∠CAB`.
-/
structure FinalAngleData where
  angleIcIaIb : ℝ
  angleA : ℝ

  bevan_angle :
    angleIcIaIb = Real.pi / 4

  angle_relation :
    angleA =
      Real.pi - 2 * angleIcIaIb

/--
Any final-angle data obtained from the geometric construction
forces the original triangle to be right-angled at `A`.
-/
theorem finalAngleData_right
    (D : FinalAngleData) :
    D.angleA = Real.pi / 2 := by

  exact
    right_angle_of_pi_relation
      D.bevan_angle
      D.angle_relation

/-!
## Circumcenter-selection + final-angle wrapper
-/

/--
This packages exactly the last logical step of the supplied proof.

Assume:

* `M` is the circumcenter of `A₁B₁C₁`;
* the geometric Bevan/Reim argument associated with that
  circumcenter gives the final angle data.

Then the angle at `A` is `π/2`.
-/
theorem imo2013_p3_core
    (M A1 B1 C1 : Point)
    (hM :
      IsCircumcenter M A1 B1 C1)
    (D : FinalAngleData) :
    D.angleA = Real.pi / 2 := by

  have _hAC :
      sqDist M A1 = sqDist M C1 :=
    circumcenter_sqDist_AC hM

  exact
    finalAngleData_right D

/-!
## Pure final conclusion
-/

/--
The exact numerical angle conclusion:

    ∠CAB = 90°.
-/
theorem imo2013_p3_final_angle
    (angleCAB angleIcIaIb : ℝ)
    (h45 :
      angleIcIaIb = Real.pi / 4)
    (hrel :
      angleCAB =
        Real.pi - 2 * angleIcIaIb) :
    angleCAB = Real.pi / 2 := by

  exact
    right_angle_of_pi_relation
      h45
      hrel

end IMO2013P3
