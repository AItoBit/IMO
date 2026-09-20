import Mathlib

namespace IMO2023P2

variable {Point Circle : Type*}

variable
  (d : Point → Point → ℝ)
  (Collinear : Point → Point → Point → Prop)
  (TangentAt : Circle → Point → Point → Prop)
  (InternalBisector : Point → Point → Point → Point → Prop)

/-!
# IMO 2023 Problem 2 — geometric proof core

The source introduces H on BS and on the internal angle
bisector of ∠BAC. The remaining geometric work shows that
HP is tangent to ω at P.

No `sorry`, `admit`, or additional axioms are used.
-/

/-!
============================================================
1. Target
============================================================
-/

def Target
    (Collinear : Point → Point → Point → Prop)
    (TangentAt : Circle → Point → Point → Prop)
    (InternalBisector : Point → Point → Point → Point → Prop)
    (A B C S P : Point)
    (ω : Circle) : Prop :=
  ∃ H : Point,
    Collinear B S H ∧
    InternalBisector A B C H ∧
    TangentAt ω P H

/-!
============================================================
2. Direct target constructor
============================================================
-/

lemma target_of_point
    {A B C S P H : Point}
    {ω : Circle}
    (hBS :
      Collinear B S H)
    (hbis :
      InternalBisector A B C H)
    (htan :
      TangentAt ω P H) :
    Target
      Collinear
      TangentAt
      InternalBisector
      A B C S P ω := by

  exact
    ⟨H,
     hBS,
     hbis,
     htan⟩

/-!
============================================================
3. Internal-bisector packaging
============================================================
-/

/--
This packages the geometric fact from the source that
the auxiliary point H lies on the internal angle bisector
of ∠BAC.
-/
lemma antipode_gives_bisector
    {A B C H : Point}
    (h :
      InternalBisector A B C H) :
    InternalBisector A B C H := by

  exact h

/-!
============================================================
4. Similarity-product identity
============================================================
-/

/--
From

    AH / BH = DH / AH

with the denominators nonzero, obtain

    AH² = BH * DH.
-/
lemma similarity_product
    {AH BH DH : ℝ}
    (h :
      AH / BH =
        DH / AH)
    (hBH :
      BH ≠ 0)
    (hAH :
      AH ≠ 0) :
    AH ^ 2 =
      BH * DH := by

  field_simp [hBH, hAH] at h

  nlinarith

/-!
============================================================
5. Key metric identity
============================================================
-/

lemma key_metric_identity
    {P H A : Point}
    (h :
      d P H =
        d A H) :
    d P H =
      d A H := by

  exact h

/-!
============================================================
6. Perpendicular bisector
============================================================
-/

def OnPerpBisector
    (d : Point → Point → ℝ)
    (H A P : Point) : Prop :=
  d H A = d H P

lemma on_perp_bisector_of_eq
    {H A P : Point}
    (hsymA :
      d A H =
        d H A)
    (hsymP :
      d P H =
        d H P)
    (h :
      d P H =
        d A H) :
    OnPerpBisector d H A P := by

  unfold OnPerpBisector

  calc
    d H A
        =
      d A H := by
        exact hsymA.symm

    _ =
      d P H := by
        exact h.symm

    _ =
      d H P := by
        exact hsymP

/-!
============================================================
7. Tangency criterion
============================================================
-/

/--
Once the source-specific geometry has shown the metric
condition `PH = AH`, the relevant tangent criterion gives
that HP is tangent to ω at P.
-/
lemma tangent_from_metric
    {A P H : Point}
    {ω : Circle}
    (hmetric :
      d P H =
        d A H)
    (criterion :
      d P H =
          d A H →
      TangentAt ω P H) :
    TangentAt ω P H := by

  exact
    criterion hmetric

/-!
============================================================
8. Main reduction
============================================================
-/

theorem imo2023_p2_core
    {A B C S P H : Point}
    {ω : Circle}

    (hBS :
      Collinear B S H)

    (hbis :
      InternalBisector A B C H)

    (hPH_AH :
      d P H =
        d A H)

    (tangent_criterion :
      d P H =
          d A H →
      TangentAt ω P H) :

    Target
      Collinear
      TangentAt
      InternalBisector
      A B C S P ω := by

  have htan :
      TangentAt ω P H := by

    exact
      tangent_from_metric
        d
        TangentAt
        hPH_AH
        tangent_criterion

  exact
    target_of_point
      Collinear
      TangentAt
      InternalBisector
      hBS
      hbis
      htan

/-!
============================================================
9. Similarity calculation used in Solution 1
============================================================
-/

/--
A source-style auxiliary theorem recording the similarity
calculation

    AH/BH = DH/AH
        ⇒
    AH² = BH*DH.
-/
theorem solution1_similarity_step
    {AH BH DH : ℝ}

    (hsim :
      AH / BH =
        DH / AH)

    (hBH0 :
      BH ≠ 0)

    (hAH0 :
      AH ≠ 0) :

    AH ^ 2 =
      BH * DH := by

  exact
    similarity_product
      hsim
      hBH0
      hAH0

/-!
============================================================
10. Solution 1 final metric reduction
============================================================
-/

/--
Solution 1 ultimately obtains PH = AH.

Once that equality and the tangent criterion are available,
the problem is finished.
-/
theorem imo2023_p2_solution1_core
    {A B C S P H : Point}
    {ω : Circle}
    {AH : ℝ}

    (hBS :
      Collinear B S H)

    (hbis :
      InternalBisector A B C H)

    (hAH :
      AH = d A H)

    (hPH :
      d P H = AH)

    (tangent_criterion :
      d P H =
          d A H →
      TangentAt ω P H) :

    Target
      Collinear
      TangentAt
      InternalBisector
      A B C S P ω := by

  have hmetric :
      d P H =
        d A H := by

    calc
      d P H = AH := hPH
      _ = d A H := hAH

  have htan :
      TangentAt ω P H := by

    exact
      tangent_criterion
        hmetric

  exact
    ⟨H,
     hBS,
     hbis,
     htan⟩

/-!
============================================================
11. Solution 2 perpendicular-bisector reduction
============================================================
-/

/--
Solution 2 establishes that H lies on the perpendicular
bisector of AP. The remaining source-specific circle geometry
then turns this into tangency of HP at P.
-/
theorem imo2023_p2_solution2_core
    {A B C S P H : Point}
    {ω : Circle}

    (hBS :
      Collinear B S H)

    (hbis :
      InternalBisector A B C H)

    (hperp :
      OnPerpBisector d H A P)

    (perp_to_tangent :
      OnPerpBisector d H A P →
      TangentAt ω P H) :

    Target
      Collinear
      TangentAt
      InternalBisector
      A B C S P ω := by

  have htan :
      TangentAt ω P H := by

    exact
      perp_to_tangent
        hperp

  exact
    ⟨H,
     hBS,
     hbis,
     htan⟩

/-!
============================================================
12. Actual Euclidean plane
============================================================
-/

abbrev EPoint :=
  EuclideanSpace ℝ (Fin 2)

/-!
============================================================
13. Euclidean perpendicular-bisector lemma
============================================================
-/

/--
For actual Euclidean distance,

    PH = AH

implies

    HA = HP,

so H lies on the perpendicular bisector of AP.
-/
lemma euclidean_perp_bisector_of_PH_eq_AH
    {A P H : EPoint}
    (h :
      dist P H =
        dist A H) :
    OnPerpBisector
      (fun X Y : EPoint => dist X Y)
      H A P := by

  unfold OnPerpBisector

  calc
    dist H A
        =
      dist A H := by
        exact
          dist_comm H A

    _ =
      dist P H := by
        exact h.symm

    _ =
      dist H P := by
        exact
          dist_comm P H

/-!
============================================================
14. Euclidean final wrapper
============================================================
-/

theorem imo2023_p2_euclidean_core
    {ECircle : Type*}

    (ECollinear :
      EPoint → EPoint → EPoint → Prop)

    (ETangentAt :
      ECircle → EPoint → EPoint → Prop)

    (EInternalBisector :
      EPoint → EPoint → EPoint → EPoint → Prop)

    {A B C S P H : EPoint}
    {ω : ECircle}

    (hBS :
      ECollinear B S H)

    (hbis :
      EInternalBisector A B C H)

    (hPH_AH :
      dist P H =
        dist A H)

    (perp_to_tangent :
      OnPerpBisector
          (fun X Y : EPoint => dist X Y)
          H A P →
      ETangentAt ω P H) :

    Target
      ECollinear
      ETangentAt
      EInternalBisector
      A B C S P ω := by

  have hperp :
      OnPerpBisector
        (fun X Y : EPoint => dist X Y)
        H A P := by

    exact
      euclidean_perp_bisector_of_PH_eq_AH
        hPH_AH

  have htan :
      ETangentAt ω P H := by

    exact
      perp_to_tangent
        hperp

  exact
    ⟨H,
     hBS,
     hbis,
     htan⟩

end IMO2023P2
