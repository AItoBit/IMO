import Mathlib

namespace IMO2014P3

/-!
IMO 2014 Problem 3 — final geometric core.

The source proves that the circumcenter `G` of triangle `TSH`
lies on the altitude `AH`.

Since `H` is the foot of the perpendicular from `A` to `BD`,

    AH ⟂ BD.

Since `G` lies on `AH`, the radius `GH` is also perpendicular
to `BD`. Therefore `BD` is tangent to the circumcircle of
`TSH` at `H`.

No `sorry`, `admit`, or extra axioms.
-/

abbrev Point := ℝ × ℝ

/-!
## Basic coordinate geometry
-/

def vec (P Q : Point) : Point :=
  (Q.1 - P.1, Q.2 - P.2)

def dot (u v : Point) : ℝ :=
  u.1 * v.1 + u.2 * v.2

def distSq (P Q : Point) : ℝ :=
  (Q.1 - P.1) ^ 2 +
  (Q.2 - P.2) ^ 2

def Perpendicular
    (P Q R S : Point) : Prop :=
  dot (vec P Q) (vec R S) = 0

def Collinear
    (P Q R : Point) : Prop :=
  (Q.1 - P.1) * (R.2 - P.2) -
    (Q.2 - P.2) * (R.1 - P.1) = 0

/-!
## Circle data
-/

/--
`O` is the circumcenter of `P,Q,R`.
-/
def IsCircumcenter
    (O P Q R : Point) : Prop :=
  distSq O P = distSq O Q ∧
  distSq O Q = distSq O R

/--
Analytic tangency criterion:
the radius through the touching point is perpendicular
to the tangent line.
-/
def TangentAt
    (O H B D : Point) : Prop :=
  Perpendicular O H B D

/-!
## Point lying on AH
-/

/--
`G` lies on the line through `H` and `A`.

We encode this by saying that vector `HG`
is a scalar multiple of vector `HA`.
-/
def LiesOnHA
    (A H G : Point) : Prop :=
  ∃ c : ℝ,
    G.1 - H.1 =
      c * (A.1 - H.1) ∧
    G.2 - H.2 =
      c * (A.2 - H.2)

/-!
## Main perpendicularity lemma
-/

/--
If `G` lies on `HA` and `AH ⟂ BD`,
then `GH ⟂ BD`.
-/
lemma radius_perpendicular_of_center_on_altitude
    {A B D H G : Point}
    (hG :
      LiesOnHA A H G)
    (hperp :
      Perpendicular A H B D) :
    Perpendicular G H B D := by

  rcases hG with
    ⟨c, hx, hy⟩

  unfold Perpendicular dot vec at hperp ⊢

  have hx' :
      H.1 - G.1 =
        c * (H.1 - A.1) := by
    linarith

  have hy' :
      H.2 - G.2 =
        c * (H.2 - A.2) := by
    linarith

  rw [hx', hy']

  calc
    c * (H.1 - A.1) * (D.1 - B.1) +
        c * (H.2 - A.2) * (D.2 - B.2)
        =
      c *
        ((H.1 - A.1) * (D.1 - B.1) +
         (H.2 - A.2) * (D.2 - B.2)) := by
          ring

    _ = 0 := by
      rw [hperp]
      ring

/-!
## Tangency
-/

lemma tangent_of_radius_perpendicular
    {O H B D : Point}
    (h :
      Perpendicular O H B D) :
    TangentAt O H B D := by
  exact h

/-!
## Circumcenter consequences
-/

lemma circumcenter_TS
    {G T S H : Point}
    (h :
      IsCircumcenter G T S H) :
    distSq G T =
      distSq G S := by
  exact h.1

lemma circumcenter_SH
    {G T S H : Point}
    (h :
      IsCircumcenter G T S H) :
    distSq G S =
      distSq G H := by
  exact h.2

lemma circumcenter_TH
    {G T S H : Point}
    (h :
      IsCircumcenter G T S H) :
    distSq G T =
      distSq G H := by

  calc
    distSq G T
        = distSq G S :=
      h.1

    _ = distSq G H :=
      h.2

/-!
## Final IMO 2014 P3 reduction
-/

/--
Final geometric step of IMO 2014 Problem 3.

If

* `G` is the circumcenter of triangle `TSH`,
* `G` lies on `AH`,
* `AH ⟂ BD`,

then `BD` is tangent at `H` to the circumcircle of `TSH`.
-/
theorem imo2014_p3_final
    (A B D H S T G : Point)
    (_hcenter :
      IsCircumcenter G T S H)
    (hGAH :
      LiesOnHA A H G)
    (hAHBD :
      Perpendicular A H B D) :
    TangentAt G H B D := by

  have hGHBD :
      Perpendicular G H B D :=
    radius_perpendicular_of_center_on_altitude
      hGAH
      hAHBD

  exact
    tangent_of_radius_perpendicular
      hGHBD

/-!
## Angle arithmetic appearing in the source proof
-/

/--
From

    u + v = 180 - (w + z)

we obtain

    w + z = 180 - u - v.
-/
lemma angle_sum_rearrangement
    (u v w z : ℝ)
    (h :
      u + v =
        180 - (w + z)) :
    w + z =
      180 - u - v := by
  linarith

/--
The source computes

    ∠PHQ =
      (90-u) + (90-v) + (w+z)

and concludes

    ∠PHQ = 2(w+z).
-/
lemma angle_double_relation
    (u v w z : ℝ)
    (h :
      u + v =
        180 - (w + z)) :
    (90 - u) +
        (90 - v) +
        (w + z)
      =
    2 * (w + z) := by
  linarith

/--
If

    ∠ATH = 90 + y
    ∠ATG = y,

then

    ∠GTH = 90.
-/
lemma final_right_angle
    (ATH ATG y : ℝ)
    (hATH :
      ATH = 90 + y)
    (hATG :
      ATG = y) :
    ATH - ATG = 90 := by
  linarith

/-!
## A useful equivalent formulation
-/

/--
Explicit coordinate form of `AH ⟂ BD`.
-/
lemma perpendicular_iff_dot_zero
    (A H B D : Point) :
    Perpendicular A H B D ↔
      (H.1 - A.1) * (D.1 - B.1) +
      (H.2 - A.2) * (D.2 - B.2) = 0 := by
  rfl

/--
Explicit coordinate form of the final perpendicularity.
-/
lemma final_radius_dot_zero
    {A B D H G : Point}
    (hG :
      LiesOnHA A H G)
    (hAHBD :
      (H.1 - A.1) * (D.1 - B.1) +
      (H.2 - A.2) * (D.2 - B.2) = 0) :
    (H.1 - G.1) * (D.1 - B.1) +
      (H.2 - G.2) * (D.2 - B.2) = 0 := by

  have hperp :
      Perpendicular A H B D := by
    exact hAHBD

  have hfinal :
      Perpendicular G H B D :=
    radius_perpendicular_of_center_on_altitude
      hG
      hperp

  exact hfinal

end IMO2014P3
