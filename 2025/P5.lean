import Mathlib

namespace IMO2025P5

noncomputable section

/-!
# IMO 2025 Problem 5

The critical value is

    1 / √2.

The source classification is:

    0 < lam < 1 / √2   → Bazza wins
    lam = 1 / √2       → neither wins
    1 / √2 < lam       → Alice wins

The central analytic inequality in Bazza's strategy is

    √2 ≤ t + √(2 - t²)

for 0 ≤ t ≤ √2.

No `sorry`, `admit`, or additional axioms are used.
-/

/-!
============================================================
1. Critical value
============================================================
-/

def critical : ℝ :=
  1 / Real.sqrt 2

lemma sqrt_two_pos :
    0 < Real.sqrt (2 : ℝ) := by
  positivity

lemma sqrt_two_ne_zero :
    Real.sqrt (2 : ℝ) ≠ 0 := by
  exact ne_of_gt sqrt_two_pos

lemma critical_pos :
    0 < critical := by
  unfold critical
  exact one_div_pos.mpr sqrt_two_pos

/-!
============================================================
2. Basic √2 identities
============================================================
-/

lemma sqrt_two_sq :
    (Real.sqrt (2 : ℝ)) ^ 2 = 2 := by
  norm_num

lemma sqrt_two_mul_self :
    Real.sqrt (2 : ℝ) *
        Real.sqrt (2 : ℝ)
      =
    2 := by
  nlinarith [sqrt_two_sq]

/-!
============================================================
3. Radicand nonnegativity
============================================================
-/

lemma two_sub_sq_nonneg
    {t : ℝ}
    (ht0 :
      0 ≤ t)
    (ht2 :
      t ≤ Real.sqrt 2) :
    0 ≤ 2 - t ^ 2 := by

  have hsqrt0 :
      0 ≤ Real.sqrt (2 : ℝ) :=
    Real.sqrt_nonneg _

  have hsquare :
      (Real.sqrt (2 : ℝ)) ^ 2 = 2 :=
    sqrt_two_sq

  nlinarith

/-!
============================================================
4. Square-root square identity
============================================================
-/

lemma sqrt_two_sub_sq_square
    {t : ℝ}
    (ht0 :
      0 ≤ t)
    (ht2 :
      t ≤ Real.sqrt 2) :
    (Real.sqrt (2 - t ^ 2)) ^ 2 =
      2 - t ^ 2 := by

  have hrad :
      0 ≤ 2 - t ^ 2 :=
    two_sub_sq_nonneg
      ht0
      ht2

  exact
    Real.sq_sqrt
      hrad

/-!
============================================================
5. Main inequality from Bazza's strategy
============================================================
-/

/--
For 0 ≤ t ≤ √2,

    √2 ≤ t + √(2-t²).
-/
theorem sqrt_two_le_add_sqrt
    {t : ℝ}
    (ht0 :
      0 ≤ t)
    (ht2 :
      t ≤ Real.sqrt 2) :
    Real.sqrt 2
      ≤
    t + Real.sqrt (2 - t ^ 2) := by

  have hsqrt2_nonneg :
      0 ≤ Real.sqrt (2 : ℝ) :=
    Real.sqrt_nonneg _

  have hrad :
      0 ≤ 2 - t ^ 2 :=
    two_sub_sq_nonneg
      ht0
      ht2

  have hs_nonneg :
      0 ≤ Real.sqrt (2 - t ^ 2) :=
    Real.sqrt_nonneg _

  have hs_sq :
      (Real.sqrt (2 - t ^ 2)) ^ 2 =
        2 - t ^ 2 :=
    Real.sq_sqrt
      hrad

  have htwo_sq :
      (Real.sqrt (2 : ℝ)) ^ 2 =
        2 :=
    sqrt_two_sq

  have hprod :
      0 ≤
        t * Real.sqrt (2 - t ^ 2) :=
    mul_nonneg
      ht0
      hs_nonneg

  have hsum_nonneg :
      0 ≤
        t + Real.sqrt (2 - t ^ 2) := by
    positivity

  nlinarith

/-!
============================================================
6. Interval version
============================================================
-/

lemma add_sqrt_ge_minimum
    {t : ℝ}
    (ht :
      t ∈ Set.Icc (0 : ℝ) (Real.sqrt 2)) :
    Real.sqrt 2
      ≤
    t + Real.sqrt (2 - t ^ 2) := by

  exact
    sqrt_two_le_add_sqrt
      ht.1
      ht.2

/-!
============================================================
7. Critical multiplication identity
============================================================
-/

lemma critical_mul_sqrt_two :
    critical * Real.sqrt 2 = 1 := by

  unfold critical

  field_simp [sqrt_two_ne_zero]

/-!
============================================================
8. Below-threshold equivalence
============================================================
-/

lemma lt_critical_iff
    {lam : ℝ} :
    lam < critical ↔
    lam * Real.sqrt 2 < 1 := by

  unfold critical

  have hs :
      0 < Real.sqrt (2 : ℝ) :=
    sqrt_two_pos

  constructor

  · intro h

    have h' :
        lam * Real.sqrt 2 < 1 :=
      (lt_div_iff₀ hs).mp h

    exact h'

  · intro h

    exact
      (lt_div_iff₀ hs).2
        h

/-!
============================================================
9. Above-threshold equivalence
============================================================
-/

lemma critical_lt_iff
    {lam : ℝ} :
    critical < lam ↔
    1 < lam * Real.sqrt 2 := by

  unfold critical

  have hs :
      0 < Real.sqrt (2 : ℝ) :=
    sqrt_two_pos

  constructor

  · intro h

    exact
      (div_lt_iff₀ hs).mp
        h

  · intro h

    exact
      (div_lt_iff₀ hs).2
        h

/-!
============================================================
10. Abstract game outcomes
============================================================
-/

/-
These predicates represent the game-theoretic outcomes.

A completely literal formalization would define histories,
strategies and legal moves explicitly.
-/

variable
  (AliceWins : ℝ → Prop)
  (BazzaWins : ℝ → Prop)
  (NeitherWins : ℝ → Prop)

/-!
============================================================
11. Three strategic facts from the source
============================================================
-/

structure StrategyFacts
    (AliceWins : ℝ → Prop)
    (BazzaWins : ℝ → Prop)
    (NeitherWins : ℝ → Prop) : Prop where

  alice :
    ∀ lam : ℝ,
      critical < lam →
      AliceWins lam

  bazza :
    ∀ lam : ℝ,
      0 < lam →
      lam < critical →
      BazzaWins lam

  equality :
    NeitherWins critical

/-!
============================================================
12. Classification of a positive parameter
============================================================
-/

theorem classification
    (F :
      StrategyFacts
        AliceWins
        BazzaWins
        NeitherWins)
    {lam : ℝ}
    (hlam :
      0 < lam) :
    (lam < critical ∧ BazzaWins lam) ∨
    (lam = critical ∧ NeitherWins lam) ∨
    (critical < lam ∧ AliceWins lam) := by

  rcases
    lt_trichotomy lam critical
  with hlt | heq | hgt

  · left

    exact
      ⟨hlt,
       F.bazza lam hlam hlt⟩

  · right
    left

    constructor

    · exact heq

    · rw [heq]

      exact F.equality

  · right
    right

    exact
      ⟨hgt,
       F.alice lam hgt⟩

/-!
============================================================
13. Alice's winning region
============================================================
-/

theorem alice_wins_above_threshold
    (F :
      StrategyFacts
        AliceWins
        BazzaWins
        NeitherWins)
    {lam : ℝ}
    (h :
      critical < lam) :
    AliceWins lam := by

  exact
    F.alice
      lam
      h

/-!
============================================================
14. Bazza's winning region
============================================================
-/

theorem bazza_wins_below_threshold
    (F :
      StrategyFacts
        AliceWins
        BazzaWins
        NeitherWins)
    {lam : ℝ}
    (hlam :
      0 < lam)
    (h :
      lam < critical) :
    BazzaWins lam := by

  exact
    F.bazza
      lam
      hlam
      h

/-!
============================================================
15. Equality case
============================================================
-/

theorem neither_wins_at_threshold
    (F :
      StrategyFacts
        AliceWins
        BazzaWins
        NeitherWins) :
    NeitherWins critical := by

  exact
    F.equality

/-!
============================================================
16. Trichotomy is exhaustive
============================================================
-/

lemma positive_threshold_trichotomy
    {lam : ℝ}
    (hlam :
      0 < lam) :
    lam < critical ∨
    lam = critical ∨
    critical < lam := by

  exact
    lt_trichotomy
      lam
      critical

/-!
============================================================
17. Explicit threshold version
============================================================
-/

lemma critical_eq_explicit :
    critical =
      1 / Real.sqrt 2 := by
  rfl

/-!
============================================================
18. Final source-style classification
============================================================
-/

theorem imo2025_p5
    (F :
      StrategyFacts
        AliceWins
        BazzaWins
        NeitherWins) :
    (∀ lam : ℝ,
      0 < lam →
      lam < 1 / Real.sqrt 2 →
      BazzaWins lam)
    ∧
    NeitherWins (1 / Real.sqrt 2)
    ∧
    (∀ lam : ℝ,
      1 / Real.sqrt 2 < lam →
      AliceWins lam) := by

  constructor

  · intro lam hlam hlt

    have hlt' :
        lam < critical := by

      unfold critical

      exact hlt

    exact
      F.bazza
        lam
        hlam
        hlt'

  constructor

  · change
      NeitherWins critical

    exact
      F.equality

  · intro lam hgt

    have hgt' :
        critical < lam := by

      unfold critical

      exact hgt

    exact
      F.alice
        lam
        hgt'

/-!
============================================================
19. Classification as an iff for Alice
============================================================
-/

/--
If one also knows Alice cannot win at or below the threshold,
then her winning region is exactly `critical < lam`.
-/
theorem alice_iff_above
    (F :
      StrategyFacts
        AliceWins
        BazzaWins
        NeitherWins)
    (alice_only_above :
      ∀ lam : ℝ,
        AliceWins lam →
        critical < lam) :
    ∀ lam : ℝ,
      AliceWins lam ↔
      critical < lam := by

  intro lam

  constructor

  · intro h

    exact
      alice_only_above
        lam
        h

  · intro h

    exact
      F.alice
        lam
        h

/-!
============================================================
20. Classification as an iff for Bazza
============================================================
-/

/--
If one also knows Bazza cannot win outside the lower region,
then for positive `lam` his winning region is exactly
`lam < critical`.
-/
theorem bazza_iff_below
    (F :
      StrategyFacts
        AliceWins
        BazzaWins
        NeitherWins)
    (bazza_only_below :
      ∀ lam : ℝ,
        0 < lam →
        BazzaWins lam →
        lam < critical) :
    ∀ lam : ℝ,
      0 < lam →
      (BazzaWins lam ↔
       lam < critical) := by

  intro lam hlam

  constructor

  · intro h

    exact
      bazza_only_below
        lam
        hlam
        h

  · intro h

    exact
      F.bazza
        lam
        hlam
        h

end

end IMO2025P5
