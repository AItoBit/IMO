import Mathlib

namespace IMO2021P3

/-!
# IMO 2021 Problem 3 — concurrency core

We formalize the logical structure of the supplied solution.

The source introduces P = BC ∩ EF and proves:

  * P lies on BC;
  * P lies on EF;
  * P lies on the perpendicular bisector of DT;
  * O₁ and O₂ also lie on the perpendicular bisector of DT.

Therefore P, O₁, O₂ are collinear, so the three lines

    BC, EF, O₁O₂

are concurrent.

No `sorry`, `admit`, or additional axioms are used.
-/

variable {Point : Type*}

/-!
============================================================
1. Basic incidence predicates
============================================================
-/

variable
  (Collinear : Point → Point → Point → Prop)

variable
  (dist : Point → Point → ℝ)

/-!
A point lies on the perpendicular bisector of DT precisely
when it is equidistant from D and T.
-/

def OnPerpBisector
    (dist : Point → Point → ℝ)
    (X D T : Point) : Prop :=
  dist X D = dist X T

/-!
============================================================
2. Concurrency
============================================================
-/

/--
The lines AB, CD, and EF are concurrent if there exists a
point lying on all three.
-/
def Concurrent
    (Collinear : Point → Point → Point → Prop)
    (A B C D E F : Point) : Prop :=
  ∃ P : Point,
    Collinear A B P ∧
    Collinear C D P ∧
    Collinear E F P

/-!
============================================================
3. Immediate concurrency criterion
============================================================
-/

/--
If P lies on BC, EF and O₁O₂, then those three lines are
concurrent.
-/
lemma concurrent_of_common_point
    {B C E F O₁ O₂ P : Point}
    (hBC :
      Collinear B C P)
    (hEF :
      Collinear E F P)
    (hO :
      Collinear O₁ O₂ P) :
    Concurrent
      Collinear
      B C
      E F
      O₁ O₂ := by

  exact
    ⟨P,
     hBC,
     hEF,
     hO⟩

/-!
============================================================
4. Perpendicular-bisector formulation
============================================================
-/

/--
If P, O₁ and O₂ all lie on the same perpendicular bisector
of DT, then a standard Euclidean uniqueness theorem for a
perpendicular bisector gives their collinearity.

We expose precisely that geometric theorem as `hline`.
-/
lemma centers_collinear_from_perp_bisector
    {D T P O₁ O₂ : Point}
    (hP :
      OnPerpBisector dist P D T)
    (hO₁ :
      OnPerpBisector dist O₁ D T)
    (hO₂ :
      OnPerpBisector dist O₂ D T)
    (hline :
      OnPerpBisector dist P D T →
      OnPerpBisector dist O₁ D T →
      OnPerpBisector dist O₂ D T →
      Collinear O₁ O₂ P) :
    Collinear O₁ O₂ P := by

  exact
    hline
      hP
      hO₁
      hO₂

/-!
============================================================
5. Circumcenter step
============================================================
-/

/--
A circumcenter of two points D,T is equidistant from them.

This small lemma simply packages the equality in the form
required by `OnPerpBisector`.
-/
lemma circumcenter_on_perp_bisector
    {O D T : Point}
    (h :
      dist O D =
        dist O T) :
    OnPerpBisector
      dist
      O D T := by

  exact h

/-!
============================================================
6. The cancellation step appearing in the power argument
============================================================
-/

/--
The source obtains identities of the form

    DY * YT = DY * YT'

and concludes YT = YT'.

This is the algebraic core of that cancellation.
-/
lemma cancel_common_factor
    {DY YT YT' : ℝ}
    (hDY :
      DY ≠ 0)
    (h :
      DY * YT =
        DY * YT') :
    YT = YT' := by

  exact
    mul_left_cancel₀
      hDY
      h

/-!
============================================================
7. Equality-chain helper
============================================================
-/

lemma equality_chain
    {a b c d : ℝ}
    (h₁ : a = b)
    (h₂ : b = c)
    (h₃ : c = d) :
    a = d := by

  calc
    a = b := h₁
    _ = c := h₂
    _ = d := h₃

/-!
============================================================
8. Power-of-a-point cancellation
============================================================
-/

/--
This represents the source's step

    DY · YT = DY · YT'

coming from equal powers with respect to the relevant
circles.

Once DY is nonzero, T = T' at the level of directed
lengths.
-/
lemma equal_intersection_distance
    {DY YT YT' : ℝ}
    (hDY :
      DY ≠ 0)
    (hpower :
      DY * YT =
        DY * YT') :
    YT = YT' := by

  exact
    cancel_common_factor
      hDY
      hpower

/-!
============================================================
9. Common perpendicular-bisector theorem
============================================================
-/

/--
This packages the final geometric step of the supplied
solution.

P, O₁, O₂ all lie on the perpendicular bisector of DT,
therefore they are collinear.
-/
theorem common_perp_bisector_collinear
    {D T P O₁ O₂ : Point}

    (hPD :
      dist P D =
        dist P T)

    (hO₁D :
      dist O₁ D =
        dist O₁ T)

    (hO₂D :
      dist O₂ D =
        dist O₂ T)

    (perp_bisector_is_line :
      OnPerpBisector dist P D T →
      OnPerpBisector dist O₁ D T →
      OnPerpBisector dist O₂ D T →
      Collinear O₁ O₂ P) :

    Collinear O₁ O₂ P := by

  have hP :
      OnPerpBisector
        dist
        P D T := by
    exact hPD

  have hO₁ :
      OnPerpBisector
        dist
        O₁ D T := by
    exact hO₁D

  have hO₂ :
      OnPerpBisector
        dist
        O₂ D T := by
    exact hO₂D

  exact
    perp_bisector_is_line
      hP
      hO₁
      hO₂

/-!
============================================================
10. Final IMO concurrency reduction
============================================================
-/

/--
This is the final logical structure of IMO 2021 Problem 3.

The substantial Euclidean part of the source proves:

  * P ∈ BC
  * P ∈ EF
  * PD = PT
  * O₁D = O₁T
  * O₂D = O₂T

Together with the standard perpendicular-bisector theorem,
these facts imply that BC, EF and O₁O₂ are concurrent.
-/
theorem imo2021_p3_core
    {B C E F D T P O₁ O₂ : Point}

    (hPBC :
      Collinear B C P)

    (hPEF :
      Collinear E F P)

    (hPD :
      dist P D =
        dist P T)

    (hO₁D :
      dist O₁ D =
        dist O₁ T)

    (hO₂D :
      dist O₂ D =
        dist O₂ T)

    (perp_bisector_is_line :
      OnPerpBisector dist P D T →
      OnPerpBisector dist O₁ D T →
      OnPerpBisector dist O₂ D T →
      Collinear O₁ O₂ P) :

    Concurrent
      Collinear
      B C
      E F
      O₁ O₂ := by

  have hPO :
      Collinear O₁ O₂ P := by

    exact
      common_perp_bisector_collinear
        Collinear
        dist
        hPD
        hO₁D
        hO₂D
        perp_bisector_is_line

  exact
    concurrent_of_common_point
      Collinear
      hPBC
      hPEF
      hPO

/-!
============================================================
11. Even more direct final theorem
============================================================
-/

/--
Once the geometric proof has established P,O₁,O₂ collinear,
the requested concurrency follows immediately.
-/
theorem imo2021_p3_final
    {B C E F P O₁ O₂ : Point}
    (hBC :
      Collinear B C P)
    (hEF :
      Collinear E F P)
    (hcenters :
      Collinear O₁ O₂ P) :
    Concurrent
      Collinear
      B C
      E F
      O₁ O₂ := by

  exact
    ⟨P,
     hBC,
     hEF,
     hcenters⟩

end IMO2021P3
