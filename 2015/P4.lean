import Mathlib

namespace IMO2015P4

/-!
# IMO 2015 Problem 4 — final metric core

The source's Solution 2 reduces the problem to:

* `AF = AG`, since F and G lie on the circle Γ centered at A;
* `OF = OG`, since F and G lie on the circumcircle Ω centered at O;
* after the angle chase, `XF = XG`.

Thus A, O, and X all lie on the perpendicular bisector of FG.
Since `F ≠ G`, this perpendicular bisector is a genuine line,
hence A, O, X are collinear.

No `sorry`, `admit`, or extra axioms are used.
-/

abbrev Point := ℝ × ℝ

/-!
## Squared distance
-/

def distSq (P Q : Point) : ℝ :=
  (P.1 - Q.1) ^ 2 +
  (P.2 - Q.2) ^ 2

/-!
## Collinearity
-/

def Collinear
    (P Q R : Point) : Prop :=
  (Q.1 - P.1) * (R.2 - P.2) -
    (Q.2 - P.2) * (R.1 - P.1) = 0

/-!
## Equal-distance equation
-/

/--
If `P` is equidistant from `F` and `G`, then `P`
satisfies the linear equation of the perpendicular bisector.
-/
lemma equidistant_linear
    {P F G : Point}
    (h :
      distSq P F = distSq P G) :
    2 * P.1 * (G.1 - F.1) +
        2 * P.2 * (G.2 - F.2)
      =
    (G.1 ^ 2 + G.2 ^ 2) -
      (F.1 ^ 2 + F.2 ^ 2) := by

  unfold distSq at h

  ring_nf at h ⊢

  linarith

/-!
## Difference of two equidistant points
-/

/--
If `P` and `Q` are both equidistant from `F,G`,
then vector `PQ` is perpendicular to vector `FG`.
-/
lemma two_equidistant_points
    {P Q F G : Point}
    (hP :
      distSq P F = distSq P G)
    (hQ :
      distSq Q F = distSq Q G) :
    (Q.1 - P.1) * (G.1 - F.1) +
      (Q.2 - P.2) * (G.2 - F.2)
      =
    0 := by

  have hp :=
    equidistant_linear hP

  have hq :=
    equidistant_linear hQ

  linarith

/-!
## Main perpendicular-bisector lemma
-/

/--
If `F ≠ G` and `A`, `O`, `X` are all equidistant
from `F,G`, then `A,O,X` are collinear.
-/
lemma collinear_of_three_equidistant
    {A O X F G : Point}
    (hFG :
      F ≠ G)
    (hA :
      distSq A F = distSq A G)
    (hO :
      distSq O F = distSq O G)
    (hX :
      distSq X F = distSq X G) :
    Collinear A O X := by

  have hAO_perp :
      (O.1 - A.1) * (G.1 - F.1) +
        (O.2 - A.2) * (G.2 - F.2)
        =
      0 :=
    two_equidistant_points
      hA
      hO

  have hAX_perp :
      (X.1 - A.1) * (G.1 - F.1) +
        (X.2 - A.2) * (G.2 - F.2)
        =
      0 :=
    two_equidistant_points
      hA
      hX

  unfold Collinear

  by_cases hx :
      G.1 - F.1 = 0

  · have hy :
        G.2 - F.2 ≠ 0 := by

      intro hy0

      have hFG_eq :
          F = G := by

        apply Prod.ext

        · linarith

        · linarith

      exact
        hFG
        hFG_eq

    have hOy :
        O.2 - A.2 = 0 := by

      rw [hx] at hAO_perp

      have hzero :
          (O.2 - A.2) *
            (G.2 - F.2) = 0 := by

        simpa using hAO_perp

      exact
        (mul_eq_zero.mp hzero).resolve_right hy

    have hXy :
        X.2 - A.2 = 0 := by

      rw [hx] at hAX_perp

      have hzero :
          (X.2 - A.2) *
            (G.2 - F.2) = 0 := by

        simpa using hAX_perp

      exact
        (mul_eq_zero.mp hzero).resolve_right hy

    rw [hOy, hXy]

    ring

  · have hdet :
        ((O.1 - A.1) * (X.2 - A.2) -
          (O.2 - A.2) * (X.1 - A.1)) *
            (G.1 - F.1)
          =
        0 := by

      calc
        ((O.1 - A.1) * (X.2 - A.2) -
          (O.2 - A.2) * (X.1 - A.1)) *
            (G.1 - F.1)
            =
          (X.2 - A.2) *
              ((O.1 - A.1) * (G.1 - F.1))
            -
          (O.2 - A.2) *
              ((X.1 - A.1) * (G.1 - F.1)) := by
                ring

        _ =
          (X.2 - A.2) *
              (-(O.2 - A.2) * (G.2 - F.2))
            -
          (O.2 - A.2) *
              (-(X.2 - A.2) * (G.2 - F.2)) := by

                have h₁ :
                    (O.1 - A.1) *
                        (G.1 - F.1)
                      =
                    -(O.2 - A.2) *
                        (G.2 - F.2) := by

                  linarith [hAO_perp]

                have h₂ :
                    (X.1 - A.1) *
                        (G.1 - F.1)
                      =
                    -(X.2 - A.2) *
                        (G.2 - F.2) := by

                  linarith [hAX_perp]

                rw [h₁, h₂]

        _ = 0 := by
          ring

    exact
      (mul_eq_zero.mp hdet).resolve_right hx

/-!
## Circle-center formulation
-/

/--
`O` is equidistant from `F,G`.
-/
def EquidistantCenter
    (O F G : Point) : Prop :=
  distSq O F = distSq O G

/-!
## Final theorem
-/

/--
Final metric reduction for IMO 2015 Problem 4.

Since A is the center of Γ,

    AF = AG.

Since O is the center of Ω,

    OF = OG.

The source's angle chase proves

    XF = XG.

Since F and G are distinct, A, O and X lie on the same
perpendicular bisector of FG, hence are collinear.
-/
theorem imo2015_p4_final
    (A O F G X : Point)
    (hFG :
      F ≠ G)
    (hA :
      EquidistantCenter A F G)
    (hO :
      EquidistantCenter O F G)
    (hX :
      distSq X F = distSq X G) :
    Collinear A O X := by

  exact
    collinear_of_three_equidistant
      hFG
      hA
      hO
      hX

/-!
## Equal radii wrappers
-/

lemma equal_radii_A
    {A F G : Point}
    (h :
      distSq A F = distSq A G) :
    EquidistantCenter A F G := by

  exact h

lemma equal_radii_O
    {O F G : Point}
    (h :
      distSq O F = distSq O G) :
    EquidistantCenter O F G := by

  exact h

/-!
## Angle-arithmetic core from Solution 2
-/

/--
The source obtains

    ∠AFK = 90 - 1/2 ∠FAD - ∠ABC

and

    ∠AGL = 90 - 1/2 ∠GAE - ∠ACB.

Therefore the relation

    FAD + 2 ABC = GAE + 2 ACB

implies `AFK = AGL`.
-/
lemma angle_reduction
    (AFK AGL FAD GAE ABC ACB : ℝ)
    (hAFK :
      AFK =
        90 - FAD / 2 - ABC)
    (hAGL :
      AGL =
        90 - GAE / 2 - ACB)
    (hmain :
      FAD + 2 * ABC =
        GAE + 2 * ACB) :
    AFK = AGL := by

  linarith

/--
Equivalent rearrangement:

    FAD - GAE = 2(ACB - ABC)

implies

    FAD + 2 ABC = GAE + 2 ACB.
-/
lemma angle_relation_rearrange
    (FAD GAE ABC ACB : ℝ)
    (h :
      FAD - GAE =
        2 * (ACB - ABC)) :
    FAD + 2 * ABC =
      GAE + 2 * ACB := by

  linarith

/--
Expansion used in the source:

    FAD - GAE
      =
    (BAD - CAE) + (BAE - CAD).
-/
lemma angle_difference_expand
    (FAD GAE BAD CAE BAE CAD : ℝ)
    (h₁ :
      FAD = BAD + BAE)
    (h₂ :
      GAE = CAE + CAD) :
    FAD - GAE =
      (BAD - CAE) +
      (BAE - CAD) := by

  linarith

/-!
## Final packaged version
-/

/--
A compact wrapper matching the final logic of Solution 2.
-/
theorem imo2015_p4_metric_core
    (A O F G X : Point)
    (hFG :
      F ≠ G)
    (hAFAG :
      distSq A F = distSq A G)
    (hOFOG :
      distSq O F = distSq O G)
    (hXFXG :
      distSq X F = distSq X G) :
    Collinear A O X := by

  have hA :
      EquidistantCenter A F G :=
    equal_radii_A
      hAFAG

  have hO :
      EquidistantCenter O F G :=
    equal_radii_O
      hOFOG

  exact
    imo2015_p4_final
      A
      O
      F
      G
      X
      hFG
      hA
      hO
      hXFXG

end IMO2015P4
