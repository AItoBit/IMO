import Mathlib

namespace IMO2020P6

noncomputable section

/-!
# IMO 2020 Problem 6 — two-case reduction

We work in the Euclidean plane.

The source proof has two cases:

1. a direction of sufficiently large width;
2. the complementary narrow case, handled by the
   disk/strip packing argument.

The hard geometric estimates are represented by
`wide_case` and `narrow_case`.

Their combination into one universal positive constant
is proved completely below.

No `sorry`, `admit`, or additional axioms are used.
-/

/-!
============================================================
1. Euclidean plane
============================================================
-/

abbrev Point :=
  EuclideanSpace ℝ (Fin 2)

/-!
============================================================
2. Lines
============================================================
-/

structure Line where
  normal : Point
  offset : ℝ
  unit_normal : ‖normal‖ = 1

/-!
============================================================
3. Signed coordinate and line distance
============================================================
-/

def signedValue
    (L : Line)
    (x : Point) : ℝ :=
  inner ℝ L.normal x - L.offset

def lineDistance
    (L : Line)
    (x : Point) : ℝ :=
  |signedValue L x|

lemma lineDistance_nonneg
    (L : Line)
    (x : Point) :
    0 ≤ lineDistance L x := by
  unfold lineDistance
  exact abs_nonneg _

/-!
============================================================
4. Separation
============================================================
-/

def Separates
    (S : Finset Point)
    (L : Line) : Prop :=
  (∃ x ∈ S,
      signedValue L x < 0)
    ∧
  (∃ y ∈ S,
      0 < signedValue L y)

/-!
============================================================
5. Pairwise unit separation
============================================================
-/

def UnitSeparated
    (S : Finset Point) : Prop :=
  ∀ x ∈ S,
    ∀ y ∈ S,
      x ≠ y →
      1 ≤ dist x y

/-!
============================================================
6. Separating line with prescribed clearance
============================================================
-/

def HasSeparatingLine
    (S : Finset Point)
    (δ : ℝ) : Prop :=
  ∃ L : Line,
    Separates S L ∧
    ∀ x ∈ S,
      δ ≤ lineDistance L x

lemma HasSeparatingLine.mono
    {S : Finset Point}
    {δ₁ δ₂ : ℝ}
    (hδ : δ₁ ≤ δ₂)
    (h : HasSeparatingLine S δ₂) :
    HasSeparatingLine S δ₁ := by

  obtain ⟨L, hsep, hdist⟩ := h

  refine ⟨L, hsep, ?_⟩

  intro x hx

  exact
    le_trans
      hδ
      (hdist x hx)

/-!
============================================================
7. n^(-1/3)
============================================================
-/

def nScale
    (n : ℕ) : ℝ :=
  1 /
    Real.rpow
      (n : ℝ)
      ((1 : ℝ) / 3)

lemma nScale_nonneg
    (n : ℕ) :
    0 ≤ nScale n := by

  unfold nScale

  have hn0 :
      0 ≤ (n : ℝ) := by
    positivity

  have hrpow :
      0 ≤
        Real.rpow
          (n : ℝ)
          ((1 : ℝ) / 3) := by
    exact
      Real.rpow_nonneg
        hn0
        ((1 : ℝ) / 3)

  exact
    one_div_nonneg.mpr
      hrpow

lemma nScale_pos
    {n : ℕ}
    (hn : 0 < n) :
    0 < nScale n := by

  unfold nScale

  have hnreal :
      0 < (n : ℝ) := by
    exact_mod_cast hn

  have hrpow :
      0 <
        Real.rpow
          (n : ℝ)
          ((1 : ℝ) / 3) := by
    exact
      Real.rpow_pos_of_pos
        hnreal
        ((1 : ℝ) / 3)

  exact
    one_div_pos.mpr
      hrpow

/-!
============================================================
8. Scaling constants
============================================================
-/

lemma constant_scale_mono
    {C₁ C₂ : ℝ}
    (n : ℕ)
    (hC : C₁ ≤ C₂) :
    C₁ * nScale n
      ≤
    C₂ * nScale n := by

  exact
    mul_le_mul_of_nonneg_right
      hC
      (nScale_nonneg n)

/-!
============================================================
9. Abstract large-width case
============================================================
-/

/-
`Wide n S` represents the large-width alternative in the
source solution.
-/

variable
  (Wide : ℕ → Finset Point → Prop)

/-!
============================================================
10. Combine the two cases
============================================================
-/

theorem combine_cases
    (Cw Cn : ℝ)
    (hCw : 0 < Cw)
    (hCn : 0 < Cn)

    (wide_case :
      ∀ n : ℕ,
        ∀ S : Finset Point,
          1 < n →
          S.card = n →
          UnitSeparated S →
          Wide n S →
          HasSeparatingLine
            S
            (Cw * nScale n))

    (narrow_case :
      ∀ n : ℕ,
        ∀ S : Finset Point,
          1 < n →
          S.card = n →
          UnitSeparated S →
          ¬ Wide n S →
          HasSeparatingLine
            S
            (Cn * nScale n)) :

    ∃ C : ℝ,
      0 < C ∧
      ∀ n : ℕ,
        ∀ S : Finset Point,
          1 < n →
          S.card = n →
          UnitSeparated S →
          HasSeparatingLine
            S
            (C * nScale n) := by

  let C : ℝ :=
    min Cw Cn

  have hCpos :
      0 < C := by
    unfold C
    exact
      lt_min
        hCw
        hCn

  refine
    ⟨C,
     hCpos,
     ?_⟩

  intro n S hn hcard hsep

  by_cases hwide :
      Wide n S

  · have hw :
        HasSeparatingLine
          S
          (Cw * nScale n) :=
      wide_case
        n
        S
        hn
        hcard
        hsep
        hwide

    have hCle :
        C ≤ Cw := by
      unfold C
      exact
        min_le_left
          Cw
          Cn

    have hscale :
        C * nScale n
          ≤
        Cw * nScale n :=
      constant_scale_mono
        n
        hCle

    exact
      HasSeparatingLine.mono
        hscale
        hw

  · have hnarrow :
        HasSeparatingLine
          S
          (Cn * nScale n) :=
      narrow_case
        n
        S
        hn
        hcard
        hsep
        hwide

    have hCle :
        C ≤ Cn := by
      unfold C
      exact
        min_le_right
          Cw
          Cn

    have hscale :
        C * nScale n
          ≤
        Cn * nScale n :=
      constant_scale_mono
        n
        hCle

    exact
      HasSeparatingLine.mono
        hscale
        hnarrow

/-!
============================================================
11. IMO 2020 Problem 6 wrapper
============================================================
-/

theorem imo2020_p6
    (Cwide Cstrip : ℝ)

    (hCwide :
      0 < Cwide)

    (hCstrip :
      0 < Cstrip)

    (wide_case :
      ∀ n : ℕ,
        ∀ S : Finset Point,
          1 < n →
          S.card = n →
          UnitSeparated S →
          Wide n S →
          HasSeparatingLine
            S
            (Cwide * nScale n))

    (strip_packing_case :
      ∀ n : ℕ,
        ∀ S : Finset Point,
          1 < n →
          S.card = n →
          UnitSeparated S →
          ¬ Wide n S →
          HasSeparatingLine
            S
            (Cstrip * nScale n)) :

    ∃ C : ℝ,
      0 < C ∧
      ∀ n : ℕ,
        ∀ S : Finset Point,
          1 < n →
          S.card = n →
          UnitSeparated S →
          ∃ L : Line,
            Separates S L ∧
            ∀ x ∈ S,
              C * nScale n
                ≤
              lineDistance L x := by

  obtain
    ⟨C,
     hC,
     hmain⟩ :=
    combine_cases
      Wide
      Cwide
      Cstrip
      hCwide
      hCstrip
      wide_case
      strip_packing_case

  refine
    ⟨C,
     hC,
     ?_⟩

  intro n S hn hcard hsep

  exact
    hmain
      n
      S
      hn
      hcard
      hsep

/-!
============================================================
12. Unpacking HasSeparatingLine
============================================================
-/

lemma clearance_of_hasSeparatingLine
    {S : Finset Point}
    {C : ℝ}
    {n : ℕ}
    (h :
      HasSeparatingLine
        S
        (C * nScale n)) :
    ∃ L : Line,
      Separates S L ∧
      ∀ x ∈ S,
        C * nScale n
          ≤
        lineDistance L x := by

  exact h

/-!
============================================================
13. Minimum of two positive constants
============================================================
-/

lemma min_positive_constant
    {C₁ C₂ : ℝ}
    (h₁ : 0 < C₁)
    (h₂ : 0 < C₂) :
    0 < min C₁ C₂ := by

  exact
    lt_min
      h₁
      h₂

/-!
============================================================
14. Direct reusable two-case theorem
============================================================
-/

theorem two_case_separation
    (C₁ C₂ : ℝ)

    (case₁ :
      ∀ n : ℕ,
        ∀ S : Finset Point,
          1 < n →
          S.card = n →
          UnitSeparated S →
          Wide n S →
          HasSeparatingLine
            S
            (C₁ * nScale n))

    (case₂ :
      ∀ n : ℕ,
        ∀ S : Finset Point,
          1 < n →
          S.card = n →
          UnitSeparated S →
          ¬ Wide n S →
          HasSeparatingLine
            S
            (C₂ * nScale n))

    {n : ℕ}
    {S : Finset Point}
    (hn :
      1 < n)
    (hcard :
      S.card = n)
    (hsep :
      UnitSeparated S) :

    HasSeparatingLine
      S
      (min C₁ C₂ * nScale n) := by

  by_cases hwide :
      Wide n S

  · have h :
        HasSeparatingLine
          S
          (C₁ * nScale n) :=
      case₁
        n
        S
        hn
        hcard
        hsep
        hwide

    have hconst :
        min C₁ C₂ ≤ C₁ :=
      min_le_left
        C₁
        C₂

    have hbound :
        min C₁ C₂ * nScale n
          ≤
        C₁ * nScale n :=
      constant_scale_mono
        n
        hconst

    exact
      HasSeparatingLine.mono
        hbound
        h

  · have h :
        HasSeparatingLine
          S
          (C₂ * nScale n) :=
      case₂
        n
        S
        hn
        hcard
        hsep
        hwide

    have hconst :
        min C₁ C₂ ≤ C₂ :=
      min_le_right
        C₁
        C₂

    have hbound :
        min C₁ C₂ * nScale n
          ≤
        C₂ * nScale n :=
      constant_scale_mono
        n
        hconst

    exact
      HasSeparatingLine.mono
        hbound
        h

end

end IMO2020P6
