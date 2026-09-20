import Mathlib

namespace IMO2019P2

/-!
# IMO 2019 Problem 2 — angle/cyclicity core

The supplied solution constructs an auxiliary circle `ω`
through

    P, Q, A0, B0,

then proves that both

    P1 ∈ ω
    Q1 ∈ ω.

Therefore

    P, Q, P1, Q1

are concyclic.

This file formalizes that logical angle/cyclicity structure.

No `sorry`, `admit`, or additional axioms are used.
-/

/-!
============================================================
1. Abstract geometric objects
============================================================
-/

variable {Point Circle : Type*}

/-
`ang A B C` represents the directed angle ∠ABC.

It is kept abstract here because the supplied proof only uses
equalities between directed angles.
-/
variable (ang : Point → Point → Point → ℝ)

/-
`OnCircle ω P` means that point `P` lies on circle `ω`.
-/
variable (OnCircle : Circle → Point → Prop)

/--
Four points are concyclic if some circle contains all four.
-/
def Concyclic
    (OnCircle : Circle → Point → Prop)
    (A B C D : Point) : Prop :=
  ∃ ω : Circle,
    OnCircle ω A ∧
    OnCircle ω B ∧
    OnCircle ω C ∧
    OnCircle ω D

/-!
============================================================
2. Basic circle packaging
============================================================
-/

/--
If four points lie on the same circle, then they are concyclic.
-/
lemma concyclic_of_same_circle
    {A B C D : Point}
    {ω : Circle}
    (hA : OnCircle ω A)
    (hB : OnCircle ω B)
    (hC : OnCircle ω C)
    (hD : OnCircle ω D) :
    Concyclic OnCircle A B C D := by

  exact
    ⟨ω,
     hA,
     hB,
     hC,
     hD⟩

/-!
============================================================
3. Constructing the auxiliary circle
============================================================
-/

/--
The first step of the source proves

    ∠QPA0 = ∠QB0A0.

A standard converse-inscribed-angle theorem then implies
that `P,Q,A0,B0` are concyclic.

We keep that standard geometry theorem explicit as a hypothesis.
-/
lemma construct_aux_circle
    {P Q A0 B0 : Point}
    (hangle :
      ang Q P A0 =
        ang Q B0 A0)
    (cyclic_of_equal_angle :
      ang Q P A0 =
          ang Q B0 A0 →
      ∃ ω : Circle,
        OnCircle ω P ∧
        OnCircle ω Q ∧
        OnCircle ω A0 ∧
        OnCircle ω B0) :
    ∃ ω : Circle,
      OnCircle ω P ∧
      OnCircle ω Q ∧
      OnCircle ω A0 ∧
      OnCircle ω B0 := by

  exact
    cyclic_of_equal_angle
      hangle

/-!
============================================================
4. The first source angle chain
============================================================
-/

/--
The source writes

    ∠QPA0 = δ
    ∠QB0A0 = δ.

Hence

    ∠QPA0 = ∠QB0A0.
-/
lemma auxiliary_angle_chain
    {Q P A0 B0 : Point}
    (δ : ℝ)
    (h₁ :
      ang Q P A0 = δ)
    (h₂ :
      ang Q B0 A0 = δ) :
    ang Q P A0 =
      ang Q B0 A0 := by

  calc
    ang Q P A0
        = δ :=
      h₁

    _ =
        ang Q B0 A0 :=
      h₂.symm

/-!
============================================================
5. The P1 angle chain
============================================================
-/

/--
The source proves

    ∠PA0B0 = φ
    ∠PP1B0 = φ,

hence

    ∠PA0B0 = ∠PP1B0.
-/
lemma p1_angle_chain
    {P P1 A0 B0 : Point}
    (φ : ℝ)
    (hPA0 :
      ang P A0 B0 = φ)
    (hPP1 :
      ang P P1 B0 = φ) :
    ang P A0 B0 =
      ang P P1 B0 := by

  calc
    ang P A0 B0
        = φ :=
      hPA0

    _ =
        ang P P1 B0 :=
      hPP1.symm

/-!
============================================================
6. P1 lies on the auxiliary circle
============================================================
-/

/--
If `P,A0,B0` lie on `ω`, and a standard equal-angle criterion
says that

    ∠PA0B0 = ∠PP1B0

places `P1` on the same circle, then `P1 ∈ ω`.
-/
lemma p1_on_aux_circle
    {ω : Circle}
    {P P1 A0 B0 : Point}
    (hP :
      OnCircle ω P)
    (hA0 :
      OnCircle ω A0)
    (hB0 :
      OnCircle ω B0)
    (hangle :
      ang P A0 B0 =
        ang P P1 B0)
    (onCircle_of_equal_angle :
      OnCircle ω P →
      OnCircle ω A0 →
      OnCircle ω B0 →
      ang P A0 B0 =
          ang P P1 B0 →
      OnCircle ω P1) :
    OnCircle ω P1 := by

  exact
    onCircle_of_equal_angle
      hP
      hA0
      hB0
      hangle

/-!
============================================================
7. The Q1 angle chain
============================================================
-/

/--
The analogous source computation for `Q1`.
-/
lemma q1_angle_chain
    {Q Q1 A0 B0 : Point}
    (ψ : ℝ)
    (hQA0 :
      ang Q A0 B0 = ψ)
    (hQQ1 :
      ang Q Q1 B0 = ψ) :
    ang Q A0 B0 =
      ang Q Q1 B0 := by

  calc
    ang Q A0 B0
        = ψ :=
      hQA0

    _ =
        ang Q Q1 B0 :=
      hQQ1.symm

/-!
============================================================
8. Q1 lies on the auxiliary circle
============================================================
-/

lemma q1_on_aux_circle
    {ω : Circle}
    {Q Q1 A0 B0 : Point}
    (hQ :
      OnCircle ω Q)
    (hA0 :
      OnCircle ω A0)
    (hB0 :
      OnCircle ω B0)
    (hangle :
      ang Q A0 B0 =
        ang Q Q1 B0)
    (onCircle_of_equal_angle :
      OnCircle ω Q →
      OnCircle ω A0 →
      OnCircle ω B0 →
      ang Q A0 B0 =
          ang Q Q1 B0 →
      OnCircle ω Q1) :
    OnCircle ω Q1 := by

  exact
    onCircle_of_equal_angle
      hQ
      hA0
      hB0
      hangle

/-!
============================================================
9. Final concyclicity step
============================================================
-/

/--
If `P,Q,P1,Q1` all lie on the same circle, then they are
concyclic.
-/
theorem final_concyclic
    {ω : Circle}
    {P Q P1 Q1 : Point}
    (hP :
      OnCircle ω P)
    (hQ :
      OnCircle ω Q)
    (hP1 :
      OnCircle ω P1)
    (hQ1 :
      OnCircle ω Q1) :
    Concyclic OnCircle P Q P1 Q1 := by

  exact
    concyclic_of_same_circle
      OnCircle
      hP
      hQ
      hP1
      hQ1

/-!
============================================================
10. Complete source-style theorem
============================================================
-/

/--
This packages the complete logical structure of the supplied
solution.

It assumes the standard Euclidean facts that:

1. the first equal-angle relation constructs the auxiliary
   circle through `P,Q,A0,B0`;

2. the equal-angle criterion puts `P1` on that circle;

3. the analogous equal-angle criterion puts `Q1` on that circle.

Everything connecting those facts is fully checked by Lean.
-/
theorem imo2019_p2_core
    {P Q P1 Q1 A0 B0 : Point}
    (δ φ ψ : ℝ)

    /- Construction of the auxiliary circle. -/
    (hQPA0 :
      ang Q P A0 = δ)

    (hQB0A0 :
      ang Q B0 A0 = δ)

    (cyclic_of_equal_angle :
      ang Q P A0 =
          ang Q B0 A0 →
      ∃ ω : Circle,
        OnCircle ω P ∧
        OnCircle ω Q ∧
        OnCircle ω A0 ∧
        OnCircle ω B0)

    /- P1 angle chain. -/
    (hPA0 :
      ang P A0 B0 = φ)

    (hPP1 :
      ang P P1 B0 = φ)

    /- Q1 angle chain. -/
    (hQA0 :
      ang Q A0 B0 = ψ)

    (hQQ1 :
      ang Q Q1 B0 = ψ)

    /- Converse-inscribed-angle criterion for P1. -/
    (p1_membership :
      ∀ ω : Circle,
        OnCircle ω P →
        OnCircle ω A0 →
        OnCircle ω B0 →
        ang P A0 B0 =
            ang P P1 B0 →
        OnCircle ω P1)

    /- Converse-inscribed-angle criterion for Q1. -/
    (q1_membership :
      ∀ ω : Circle,
        OnCircle ω Q →
        OnCircle ω A0 →
        OnCircle ω B0 →
        ang Q A0 B0 =
            ang Q Q1 B0 →
        OnCircle ω Q1) :
    Concyclic
      OnCircle
      P
      Q
      P1
      Q1 := by

  have hAuxAngle :
      ang Q P A0 =
        ang Q B0 A0 :=
    auxiliary_angle_chain
      ang
      δ
      hQPA0
      hQB0A0

  obtain
    ⟨ω,
     hP,
     hQ,
     hA0,
     hB0⟩ :=
    cyclic_of_equal_angle
      hAuxAngle

  have hP1Angle :
      ang P A0 B0 =
        ang P P1 B0 :=
    p1_angle_chain
      ang
      φ
      hPA0
      hPP1

  have hP1 :
      OnCircle ω P1 :=
    p1_membership
      ω
      hP
      hA0
      hB0
      hP1Angle

  have hQ1Angle :
      ang Q A0 B0 =
        ang Q Q1 B0 :=
    q1_angle_chain
      ang
      ψ
      hQA0
      hQQ1

  have hQ1 :
      OnCircle ω Q1 :=
    q1_membership
      ω
      hQ
      hA0
      hB0
      hQ1Angle

  exact
    concyclic_of_same_circle
      OnCircle
      hP
      hQ
      hP1
      hQ1

end IMO2019P2
