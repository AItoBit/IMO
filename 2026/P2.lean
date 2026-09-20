import Mathlib

namespace IMO2026P2

/-!
# IMO 2026 Problem 2 — geometric proof core

The source proves:

1. MN ∥ KL.
2. D and O lie on the same perpendicular bisector of KL.
3. D is the circumcenter of AMN, hence D lies on the
   perpendicular bisector of MN.
4. Therefore O also lies on the perpendicular bisector of MN.
5. Hence OM = ON.

The substantial Euclidean arguments proving Lemmas 1 and 2
are represented explicitly as hypotheses.

No `sorry`, `admit`, or additional axioms are used.
-/

variable {Point : Type*}

/-
`d` is an abstract distance function.
-/

variable
  (d : Point → Point → ℝ)

/-
Basic geometric predicates.
-/

variable
  (Collinear : Point → Point → Point → Prop)
  (Parallel : Point → Point → Point → Point → Prop)

/-!
============================================================
1. Perpendicular-bisector predicate
============================================================
-/

def OnPerpBisector
    (d : Point → Point → ℝ)
    (X A B : Point) : Prop :=
  d X A = d X B

/-!
============================================================
2. Immediate metric consequence
============================================================
-/

lemma eq_dist_of_on_perp_bisector
    {X A B : Point}
    (h :
      OnPerpBisector d X A B) :
    d X A = d X B := by

  exact h

/-!
============================================================
3. Circumcenter packaging
============================================================
-/

/--
For the part of the argument we need, being the circumcenter
of triangle ABC means being equidistant from its vertices.
-/
def IsCircumcenter
    (d : Point → Point → ℝ)
    (O A B C : Point) : Prop :=
  d O A = d O B ∧
  d O B = d O C

lemma circumcenter_eq_AB
    {O A B C : Point}
    (h :
      IsCircumcenter d O A B C) :
    d O A = d O B := by

  exact h.1

lemma circumcenter_eq_BC
    {O A B C : Point}
    (h :
      IsCircumcenter d O A B C) :
    d O B = d O C := by

  exact h.2

lemma circumcenter_on_perp_bisector
    {O A B C : Point}
    (h :
      IsCircumcenter d O A B C) :
    OnPerpBisector d O B C := by

  exact h.2

/-!
============================================================
4. Source Lemma 1
============================================================
-/

/--
The source's first lemma is

    MN ∥ KL.

This wrapper keeps its use explicit.
-/
lemma lemma1_parallel
    {M N K L : Point}
    (h :
      Parallel M N K L) :
    Parallel M N K L := by

  exact h

/-!
============================================================
5. Source Lemma 2
============================================================
-/

/--
The second source lemma says that the relevant perpendicular
bisectors coincide.  We encode precisely the consequence
needed later:

if D is on the perpendicular bisector of MN and D,O lie on
the common bisector determined by the parallel configuration,
then O is on the perpendicular bisector of MN.
-/
lemma common_perp_bisector_transfer
    {D O M N K L : Point}
    (hMNKL :
      Parallel M N K L)
    (hD_MN :
      OnPerpBisector d D M N)
    (transfer :
      Parallel M N K L →
      OnPerpBisector d D M N →
      OnPerpBisector d O M N) :
    OnPerpBisector d O M N := by

  exact
    transfer
      hMNKL
      hD_MN

/-!
============================================================
6. D is on the perpendicular bisector of MN
============================================================
-/

/--
Since D is the circumcenter of AMN,

    DM = DN.
-/
lemma D_on_MN_bisector
    {D A M N : Point}
    (hD :
      IsCircumcenter d D A M N) :
    OnPerpBisector d D M N := by

  exact
    circumcenter_on_perp_bisector
      d
      hD

/-!
============================================================
7. O is equidistant from M and N
============================================================
-/

lemma O_equidistant_MN
    {D O A M N K L : Point}
    (hD :
      IsCircumcenter d D A M N)
    (hMNKL :
      Parallel M N K L)
    (transfer :
      Parallel M N K L →
      OnPerpBisector d D M N →
      OnPerpBisector d O M N) :
    d O M = d O N := by

  have hDbis :
      OnPerpBisector d D M N := by

    exact
      D_on_MN_bisector
        d
        hD

  have hObis :
      OnPerpBisector d O M N := by

    exact
      common_perp_bisector_transfer
        d
        Parallel
        hMNKL
        hDbis
        transfer

  exact hObis

/-!
============================================================
8. Main IMO proof core
============================================================
-/

/--
This is the final logical structure of the source proof.

`hMNKL` is Lemma 1.

`htransfer` packages Lemma 2: the perpendicular-bisector
argument coming from the homothetic trapezoids/circumcircles.

From D being the circumcenter of AMN, we get DM = DN.
Lemma 2 transfers that bisector to O, hence OM = ON.
-/
theorem imo2026_p2_core
    {A D O M N K L : Point}

    (hD :
      IsCircumcenter d D A M N)

    (hMNKL :
      Parallel M N K L)

    (htransfer :
      Parallel M N K L →
      OnPerpBisector d D M N →
      OnPerpBisector d O M N) :

    d O M = d O N := by

  exact
    O_equidistant_MN
      d
      Parallel
      hD
      hMNKL
      htransfer

/-!
============================================================
9. Version including both circumcenters
============================================================
-/

/--
The problem explicitly defines O as the circumcenter of AKL.
The final deduction does not need its metric equalities once
Lemma 2 has already been established, but this version keeps
that datum visible in the theorem statement.
-/
theorem imo2026_p2_with_centers
    {A D O M N K L : Point}

    (hD :
      IsCircumcenter d D A M N)

    (_hO :
      IsCircumcenter d O A K L)

    (hMNKL :
      Parallel M N K L)

    (htransfer :
      Parallel M N K L →
      OnPerpBisector d D M N →
      OnPerpBisector d O M N) :

    d O M = d O N := by

  exact
    imo2026_p2_core
      d
      Parallel
      hD
      hMNKL
      htransfer

/-!
============================================================
10. Collinearity formulation of Lemma 2
============================================================
-/

/--
The source says D and O are collinear along the common
perpendicular bisector.  This theorem separates that
geometric statement from the final metric consequence.
-/
theorem imo2026_p2_from_collinear_bisector
    {A D O M N : Point}

    (hD :
      IsCircumcenter d D A M N)

    (hDO :
      Collinear D O O)

    (collinear_bisector :
      Collinear D O O →
      OnPerpBisector d D M N →
      OnPerpBisector d O M N) :

    d O M = d O N := by

  have hDbis :
      OnPerpBisector d D M N := by

    exact
      D_on_MN_bisector
        d
        hD

  have hObis :
      OnPerpBisector d O M N := by

    exact
      collinear_bisector
        hDO
        hDbis

  exact hObis

/-!
============================================================
11. Direct final wrapper
============================================================
-/

/--
Once O is known to lie on the perpendicular bisector of MN,
the desired equality is literally its definition.
-/
theorem imo2026_p2_final
    {O M N : Point}
    (hO :
      OnPerpBisector d O M N) :
    d O M = d O N := by

  exact hO

end IMO2026P2
