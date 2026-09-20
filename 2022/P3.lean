import Mathlib

namespace IMO2022P4

variable {Point : Type*}

variable
  (ang : Point → Point → Point → ℝ)
  (dist : Point → Point → ℝ)

variable
  (Concyclic : Point → Point → Point → Point → Prop)

/-!
============================================================
1. Equality-chain helpers
============================================================
-/

lemma angle_chain₃
    {A B C D E F G H I : Point}
    (h₁ :
      ang A B C =
        ang D E F)
    (h₂ :
      ang D E F =
        ang G H I) :
    ang A B C =
      ang G H I := by

  calc
    ang A B C = ang D E F := h₁
    _ = ang G H I := h₂

lemma angle_chain₄
    {A₁ B₁ C₁
     A₂ B₂ C₂
     A₃ B₃ C₃
     A₄ B₄ C₄ : Point}
    (h₁ :
      ang A₁ B₁ C₁ =
        ang A₂ B₂ C₂)
    (h₂ :
      ang A₂ B₂ C₂ =
        ang A₃ B₃ C₃)
    (h₃ :
      ang A₃ B₃ C₃ =
        ang A₄ B₄ C₄) :
    ang A₁ B₁ C₁ =
      ang A₄ B₄ C₄ := by

  calc
    ang A₁ B₁ C₁ = ang A₂ B₂ C₂ := h₁
    _ = ang A₃ B₃ C₃ := h₂
    _ = ang A₄ B₄ C₄ := h₃

/-!
============================================================
2. Product identity from the similarity ratio
============================================================
-/

/--
From

    QT / ST = TB / TE,

together with TE = TC and TB = TD,

derive

    QT * TC = ST * TD.

We expose nonzero denominators explicitly.
-/
lemma product_identity
    (QT ST TB TE TC TD : ℝ)
    (hST : ST ≠ 0)
    (hTE : TE ≠ 0)
    (hratio :
      QT / ST =
        TB / TE)
    (hTC :
      TE = TC)
    (hTD :
      TB = TD) :
    QT * TC =
      ST * TD := by

  field_simp [hST, hTE] at hratio

  rw [hTC, hTD] at hratio

  nlinarith

/-!
============================================================
3. Similarity consequence packaging
============================================================
-/

/--
The source obtains the ratio QT/ST = TB/TE from
triangle similarity.
-/
lemma similarity_ratio
    {Q T S B E : Point}
    (h :
      dist Q T / dist S T =
        dist T B / dist T E) :
    dist Q T / dist S T =
      dist T B / dist T E := by

  exact h

/-!
============================================================
4. Product consequence in geometric notation
============================================================
-/

lemma geometric_product_identity
    {Q T S B C D E : Point}
    (hST :
      dist S T ≠ 0)
    (hTE :
      dist T E ≠ 0)
    (hratio :
      dist Q T / dist S T =
        dist T B / dist T E)
    (hTC :
      dist T E =
        dist T C)
    (hTD :
      dist T B =
        dist T D) :
    dist Q T * dist T C =
      dist S T * dist T D := by

  exact
    product_identity
      (dist Q T)
      (dist S T)
      (dist T B)
      (dist T E)
      (dist T C)
      (dist T D)
      hST
      hTE
      hratio
      hTC
      hTD

/-!
============================================================
5. Cyclicity of C,D,Q,S
============================================================
-/

/--
The product equality is the source's power-of-point criterion
for C,D,Q,S to be concyclic.

The geometric implication is supplied explicitly.
-/
lemma cdqs_concyclic
    {C D Q S T : Point}
    (hprod :
      dist Q T * dist T C =
        dist S T * dist T D)
    (cyclic_of_product :
      dist Q T * dist T C =
          dist S T * dist T D →
      Concyclic C D Q S) :
    Concyclic C D Q S := by

  exact
    cyclic_of_product
      hprod

/-!
============================================================
6. Angle consequence from cyclicity
============================================================
-/

/--
For cyclic C,D,Q,S, the source uses

    ∠QCD = ∠QSD.
-/
lemma angle_from_cdqs
    {C D Q S : Point}
    (hcyc :
      Concyclic C D Q S)
    (cyclic_angle :
      Concyclic C D Q S →
      ang Q C D =
        ang Q S D) :
    ang Q C D =
      ang Q S D := by

  exact
    cyclic_angle hcyc

/-!
============================================================
7. Final angle chase
============================================================
-/

/--
The source's last chain is

    ∠QPR
      = ∠QPC
      = ∠QCD - ∠PQC
      = ∠QSD - ∠EST
      = ∠QSR.

Once these equalities are available, we conclude

    ∠QPR = ∠QSR.
-/
lemma final_angle_chain
    {Q P R C D S E T : Point}
    (h₁ :
      ang Q P R =
        ang Q P C)
    (h₂ :
      ang Q P C =
        ang Q C D - ang P Q C)
    (h₃ :
      ang Q C D =
        ang Q S D)
    (h₄ :
      ang P Q C =
        ang E S T)
    (h₅ :
      ang Q S D - ang E S T =
        ang Q S R) :
    ang Q P R =
      ang Q S R := by

  calc
    ang Q P R
        =
      ang Q P C :=
      h₁

    _ =
      ang Q C D - ang P Q C :=
      h₂

    _ =
      ang Q S D - ang P Q C := by
      rw [h₃]

    _ =
      ang Q S D - ang E S T := by
      rw [h₄]

    _ =
      ang Q S R :=
      h₅

/-!
============================================================
8. Final cyclicity criterion
============================================================
-/

/--
Equal subtended angles imply P,Q,R,S are cyclic.
-/
lemma pqrs_concyclic
    {P Q R S : Point}
    (hangle :
      ang Q P R =
        ang Q S R)
    (cyclic_of_equal_angle :
      ang Q P R =
          ang Q S R →
      Concyclic P Q R S) :
    Concyclic P Q R S := by

  exact
    cyclic_of_equal_angle
      hangle

/-!
============================================================
9. Full source-style core theorem
============================================================
-/

theorem imo2022_p4_core
    {B C D E T P Q R S : Point}

    (hST :
      dist S T ≠ 0)

    (hTE :
      dist T E ≠ 0)

    (hratio :
      dist Q T / dist S T =
        dist T B / dist T E)

    (hTC :
      dist T E =
        dist T C)

    (hTD :
      dist T B =
        dist T D)

    (cyclic_of_product :
      dist Q T * dist T C =
          dist S T * dist T D →
      Concyclic C D Q S)

    (cyclic_angle :
      Concyclic C D Q S →
      ang Q C D =
        ang Q S D)

    (hQPR_QPC :
      ang Q P R =
        ang Q P C)

    (hQPC :
      ang Q P C =
        ang Q C D - ang P Q C)

    (hPQC_EST :
      ang P Q C =
        ang E S T)

    (hfinal :
      ang Q S D - ang E S T =
        ang Q S R)

    (cyclic_of_equal_angle :
      ang Q P R =
          ang Q S R →
      Concyclic P Q R S) :

    Concyclic P Q R S := by

  have hprod :
      dist Q T * dist T C =
        dist S T * dist T D := by

    exact
      geometric_product_identity
        dist
        hST
        hTE
        hratio
        hTC
        hTD

  have hCDQS :
      Concyclic C D Q S := by

    exact
      cdqs_concyclic
        dist
        Concyclic
        hprod
        cyclic_of_product

  have hQCD_QSD :
      ang Q C D =
        ang Q S D := by

    exact
      angle_from_cdqs
        ang
        Concyclic
        hCDQS
        cyclic_angle

  have hangle :
      ang Q P R =
        ang Q S R := by

    exact
      final_angle_chain
        ang
        hQPR_QPC
        hQPC
        hQCD_QSD
        hPQC_EST
        hfinal

  exact
    pqrs_concyclic
      ang
      Concyclic
      hangle
      cyclic_of_equal_angle

/-!
============================================================
10. Very direct final wrapper
============================================================
-/

/--
Once the source has established ∠QPR = ∠QSR,
the desired cyclicity follows immediately.
-/
theorem imo2022_p4_final
    {P Q R S : Point}
    (h :
      ang Q P R =
        ang Q S R)
    (criterion :
      ang Q P R =
          ang Q S R →
      Concyclic P Q R S) :
    Concyclic P Q R S := by

  exact criterion h

end IMO2022P4
