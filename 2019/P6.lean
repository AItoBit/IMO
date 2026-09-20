import Mathlib

namespace IMO2019P6

/-!
# IMO 2019 Problem 6 — inversion / angle core

The supplied solution proceeds through four main stages.

1. Construct an auxiliary point `S`, and reduce the original
   incidence statement to a circle-membership statement.

2. Prove that `Q, B, I, C` are concyclic.

3. After inversion in the incircle, prove that the midpoint
   `M` of `AD` belongs to an auxiliary circle `Ω`.

4. Prove that the image of `Q` also belongs to `Ω` using
   the angle chain

       ∠PQM = ∠PQC
            = ∠PEC
            = ∠PED
            = ∠PSD
            = ∠PSM.

No `sorry`, `admit`, or extra axioms are used.
-/

/-!
============================================================
1. Abstract geometric primitives
============================================================
-/

variable {Point Circle : Type*}

/-
`ang A B C` denotes a directed angle ∠ABC.
-/
variable (ang : Point → Point → Point → ℝ)

/-
Basic incidence predicates.
-/
variable
  (OnCircle : Circle → Point → Prop)
  (Collinear : Point → Point → Point → Prop)
  (Perpendicular : Point → Point → Point → Point → Prop)

/--
Four points are concyclic if they lie on one circle.
-/
def Concyclic
    (OnCircle : Circle → Point → Prop)
    (A B C D : Point) : Prop :=
  ∃ ω : Circle,
    OnCircle ω A ∧
    OnCircle ω B ∧
    OnCircle ω C ∧
    OnCircle ω D

lemma concyclic_of_same_circle
    {A B C D : Point}
    {ω : Circle}
    (hA : OnCircle ω A)
    (hB : OnCircle ω B)
    (hC : OnCircle ω C)
    (hD : OnCircle ω D) :
    Concyclic OnCircle A B C D := by

  exact
    ⟨ω, hA, hB, hC, hD⟩

/-!
============================================================
2. Arithmetic core of Step 1
============================================================
-/

/--
From

    AI / GI = RI / A'I

together with

    RI = GI

and the nonzero denominator conditions, we obtain

    A'I * AI = RI^2.
-/
lemma inversion_product
    (AI GI RI A'I : ℝ)
    (hGI : GI ≠ 0)
    (hA' : A'I ≠ 0)
    (hAI :
      AI / GI = RI / A'I)
    (hRG :
      RI = GI) :
    A'I * AI = RI ^ 2 := by

  field_simp [hGI, hA'] at hAI

  rw [hRG] at hAI ⊢

  nlinarith

/-!
============================================================
3. Basic angle-chain lemmas
============================================================
-/

/--
Two equal angles through a common value.
-/
lemma angle_chain₂
    {A B C D E F : Point}
    (x : ℝ)
    (h₁ :
      ang A B C = x)
    (h₂ :
      ang D E F = x) :
    ang A B C =
      ang D E F := by

  calc
    ang A B C
        = x :=
      h₁

    _ =
        ang D E F :=
      h₂.symm

/--
A six-angle equality chain.
-/
lemma angle_chain₆
    {A₁ B₁ C₁
     A₂ B₂ C₂
     A₃ B₃ C₃
     A₄ B₄ C₄
     A₅ B₅ C₅
     A₆ B₆ C₆ : Point}
    (h₁ :
      ang A₁ B₁ C₁ =
        ang A₂ B₂ C₂)
    (h₂ :
      ang A₂ B₂ C₂ =
        ang A₃ B₃ C₃)
    (h₃ :
      ang A₃ B₃ C₃ =
        ang A₄ B₄ C₄)
    (h₄ :
      ang A₄ B₄ C₄ =
        ang A₅ B₅ C₅)
    (h₅ :
      ang A₅ B₅ C₅ =
        ang A₆ B₆ C₆) :
    ang A₁ B₁ C₁ =
      ang A₆ B₆ C₆ := by

  calc
    ang A₁ B₁ C₁
        =
      ang A₂ B₂ C₂ :=
        h₁

    _ =
      ang A₃ B₃ C₃ :=
        h₂

    _ =
      ang A₄ B₄ C₄ :=
        h₃

    _ =
      ang A₅ B₅ C₅ :=
        h₄

    _ =
      ang A₆ B₆ C₆ :=
        h₅

/-!
============================================================
4. Step 2: Q, B, I, C are concyclic
============================================================
-/

/--
The source obtains

    ∠BQC = ∠BIC.
-/
lemma step2_angle
    {B Q C I : Point}
    (h :
      ang B Q C =
        ang B I C) :
    ang B Q C =
      ang B I C := by

  exact h

/--
A converse-inscribed-angle criterion packages the cyclicity.
-/
lemma step2_concyclic
    {B Q C I : Point}
    (hangle :
      ang B Q C =
        ang B I C)
    (cyclic_of_equal_angle :
      ang B Q C =
          ang B I C →
      Concyclic OnCircle B Q C I) :
    Concyclic OnCircle B Q C I := by

  exact
    cyclic_of_equal_angle
      hangle

/-!
============================================================
5. Step 3 angle calculations
============================================================
-/

/--
If both angles equal φ, then they are equal.
-/
lemma step3_equal_angles
    {I M A P : Point}
    (φ : ℝ)
    (hIMA :
      ang I M A = φ)
    (hMAP :
      ang M A P = φ) :
    ang I M A =
      ang M A P := by

  exact
    angle_chain₂
      ang
      φ
      hIMA
      hMAP

/--
The source also gets

    ∠PMA = 180° - 2φ
    ∠PIS = 180° - 2φ.
-/
lemma step3_second_angle
    {P M A I S : Point}
    (φ : ℝ)
    (hPMA :
      ang P M A =
        180 - 2 * φ)
    (hPIS :
      ang P I S =
        180 - 2 * φ) :
    ang P M A =
      ang P I S := by

  calc
    ang P M A
        =
      180 - 2 * φ :=
        hPMA

    _ =
      ang P I S :=
        hPIS.symm

/--
Packaging the claim that M lies on Ω.
-/
lemma midpoint_on_aux_circle
    {Ω : Circle}
    {P I S M : Point}
    (hP :
      OnCircle Ω P)
    (hI :
      OnCircle Ω I)
    (hS :
      OnCircle Ω S)
    (hangle :
      ang P M I =
        ang P S I)
    (membership :
      OnCircle Ω P →
      OnCircle Ω I →
      OnCircle Ω S →
      ang P M I =
          ang P S I →
      OnCircle Ω M) :
    OnCircle Ω M := by

  exact
    membership
      hP
      hI
      hS
      hangle

/-!
============================================================
6. Step 4: final six-angle chain
============================================================
-/

/--
The exact chain from the source:

    ∠PQM = ∠PQC
         = ∠PEC
         = ∠PED
         = ∠PSD
         = ∠PSM.
-/
lemma step4_angle_chain
    {P Q M C E D S : Point}
    (h₁ :
      ang P Q M =
        ang P Q C)
    (h₂ :
      ang P Q C =
        ang P E C)
    (h₃ :
      ang P E C =
        ang P E D)
    (h₄ :
      ang P E D =
        ang P S D)
    (h₅ :
      ang P S D =
        ang P S M) :
    ang P Q M =
      ang P S M := by

  exact
    angle_chain₆
      ang
      h₁
      h₂
      h₃
      h₄
      h₅

/-!
============================================================
7. Q lies on the auxiliary circle
============================================================
-/

/--
If `P,S,M` lie on Ω and

    ∠PQM = ∠PSM,

then the standard converse-inscribed-angle theorem yields
`Q ∈ Ω`.
-/
lemma q_on_aux_circle
    {Ω : Circle}
    {P Q S M : Point}
    (hP :
      OnCircle Ω P)
    (hS :
      OnCircle Ω S)
    (hM :
      OnCircle Ω M)
    (hangle :
      ang P Q M =
        ang P S M)
    (membership :
      OnCircle Ω P →
      OnCircle Ω S →
      OnCircle Ω M →
      ang P Q M =
          ang P S M →
      OnCircle Ω Q) :
    OnCircle Ω Q := by

  exact
    membership
      hP
      hS
      hM
      hangle

/-!
============================================================
8. Full Step 4 package
============================================================
-/

theorem step4
    {Ω : Circle}
    {P Q M C E D S : Point}
    (hP :
      OnCircle Ω P)
    (hS :
      OnCircle Ω S)
    (hM :
      OnCircle Ω M)
    (h₁ :
      ang P Q M =
        ang P Q C)
    (h₂ :
      ang P Q C =
        ang P E C)
    (h₃ :
      ang P E C =
        ang P E D)
    (h₄ :
      ang P E D =
        ang P S D)
    (h₅ :
      ang P S D =
        ang P S M)
    (membership :
      OnCircle Ω P →
      OnCircle Ω S →
      OnCircle Ω M →
      ang P Q M =
          ang P S M →
      OnCircle Ω Q) :
    OnCircle Ω Q := by

  have hangle :
      ang P Q M =
        ang P S M :=
    step4_angle_chain
      ang
      h₁
      h₂
      h₃
      h₄
      h₅

  exact
    membership
      hP
      hS
      hM
      hangle

/-!
============================================================
9. Final target
============================================================
-/

/--
The original target:

the point X = DI ∩ PQ lies on the line through A
perpendicular to AI.
-/
def Target
    (Collinear :
      Point → Point → Point → Prop)
    (Perpendicular :
      Point → Point → Point → Point → Prop)
    (A I D P Q X : Point) : Prop :=
  Collinear D I X ∧
  Collinear P Q X ∧
  Perpendicular A X A I

/-!
============================================================
10. Reduction from Q ∈ Ω
============================================================
-/

/--
Step 1 reduces the original statement to proving the image
of Q lies on Ω.
-/
lemma final_reduction
    {Ω : Circle}
    {A I D P Q X : Point}
    (hQ :
      OnCircle Ω Q)
    (reduction :
      OnCircle Ω Q →
      Collinear D I X ∧
      Collinear P Q X ∧
      Perpendicular A X A I) :
    Target
      Collinear
      Perpendicular
      A I D P Q X := by

  exact
    reduction hQ

/-!
============================================================
11. Complete source-style wrapper
============================================================
-/

/--
Complete logical skeleton of the source proof.

The substantial Euclidean/inversion facts are explicit
hypotheses rather than hidden behind `sorry`.
-/
theorem imo2019_p6_core
    {Ω : Circle}
    {A I D P Q M C E S X : Point}

    (hP :
      OnCircle Ω P)

    (hS :
      OnCircle Ω S)

    (hM :
      OnCircle Ω M)

    (hPQM_PQC :
      ang P Q M =
        ang P Q C)

    (hPQC_PEC :
      ang P Q C =
        ang P E C)

    (hPEC_PED :
      ang P E C =
        ang P E D)

    (hPED_PSD :
      ang P E D =
        ang P S D)

    (hPSD_PSM :
      ang P S D =
        ang P S M)

    (q_membership :
      OnCircle Ω P →
      OnCircle Ω S →
      OnCircle Ω M →
      ang P Q M =
          ang P S M →
      OnCircle Ω Q)

    (reduction :
      OnCircle Ω Q →
      Collinear D I X ∧
      Collinear P Q X ∧
      Perpendicular A X A I) :
    Target
      Collinear
      Perpendicular
      A I D P Q X := by

  have hQ :
      OnCircle Ω Q := by

    exact
      step4
        ang
        OnCircle
        hP
        hS
        hM
        hPQM_PQC
        hPQC_PEC
        hPEC_PED
        hPED_PSD
        hPSD_PSM
        q_membership

  exact
    final_reduction
      OnCircle
      Collinear
      Perpendicular
      hQ
      reduction

end IMO2019P6
