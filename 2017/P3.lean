import Mathlib

namespace IMO2017P3

noncomputable section

/-
IMO 2017 Problem 3 — quantitative core of the official solution.

The official construction considers

  ε = 200 - √(200² - 1)
    = 200 - √39999.

The key facts are

  ε² + 1 = 400 ε

and

  ε > 1/400.

These imply that, while the hunter-rabbit distance d is < 100,
the rabbit can choose one of the two 200-step directions so that

  new_distance² > d² + 1/2.
-/


/- ============================================================
   Definition of ε
   ============================================================ -/

def ε : ℝ :=
  200 - Real.sqrt 39999


/- ============================================================
   Facts about √39999
   ============================================================ -/

/--
  (√39999)² = 39999.
-/
lemma sqrt_39999_sq :
    (Real.sqrt (39999 : ℝ)) ^ 2 = 39999 := by
  exact Real.sq_sqrt (by norm_num)


/--
  √39999 ≥ 0.
-/
lemma sqrt_39999_nonneg :
    0 ≤ Real.sqrt (39999 : ℝ) := by
  exact Real.sqrt_nonneg _


/--
  √39999 < 200.

This follows because its square is 39999 < 40000.
-/
lemma sqrt_39999_lt_200 :
    Real.sqrt (39999 : ℝ) < 200 := by

  have hs0 :
      0 ≤ Real.sqrt (39999 : ℝ) :=
    sqrt_39999_nonneg

  have hs2 :
      (Real.sqrt (39999 : ℝ)) ^ 2 = 39999 :=
    sqrt_39999_sq

  by_contra h

  have hge :
      (200 : ℝ) ≤ Real.sqrt (39999 : ℝ) := by
    linarith

  have hsub :
      0 ≤ Real.sqrt (39999 : ℝ) - 200 := by
    linarith

  have hadd :
      0 ≤ Real.sqrt (39999 : ℝ) + 200 := by
    linarith

  have hprod :
      0 ≤
        (Real.sqrt (39999 : ℝ) - 200) *
        (Real.sqrt (39999 : ℝ) + 200) :=
    mul_nonneg hsub hadd

  nlinarith


/- ============================================================
   Facts about ε
   ============================================================ -/

/--
ε is positive.
-/
lemma epsilon_pos :
    0 < ε := by

  have hs :
      Real.sqrt (39999 : ℝ) < 200 :=
    sqrt_39999_lt_200

  unfold ε

  linarith


/--
Main algebraic identity:

  ε² + 1 = 400 ε.
-/
lemma epsilon_sq_add_one :
    ε ^ 2 + 1 = 400 * ε := by

  have hs2 :
      (Real.sqrt (39999 : ℝ)) ^ 2 = 39999 :=
    sqrt_39999_sq

  unfold ε

  nlinarith


/--
The numerical estimate used in the official solution:

  ε > 1/400.
-/
lemma epsilon_gt_one_div_400 :
    (1 : ℝ) / 400 < ε := by

  have he :
      ε ^ 2 + 1 = 400 * ε :=
    epsilon_sq_add_one

  have hepos :
      0 < ε :=
    epsilon_pos

  have hesqpos :
      0 < ε ^ 2 := by
    positivity

  nlinarith


/--
Consequently ε ≥ 0.
-/
lemma epsilon_nonneg :
    0 ≤ ε := by
  exact le_of_lt epsilon_pos


/- ============================================================
   Rewrite of the geometric distance formula
   ============================================================ -/

/--
In the official diagram, the squared new distance has the form

  y² = d² - 2 ε d + ε² + 1.

Using ε² + 1 = 400 ε, this becomes

  y² = d² + ε(400 - 2d).
-/
lemma distance_square_identity
    (d y : ℝ)
    (hy :
      y ^ 2 =
        d ^ 2
          - 2 * ε * d
          + ε ^ 2
          + 1) :
    y ^ 2 =
      d ^ 2 + ε * (400 - 2 * d) := by

  have he :
      ε ^ 2 + 1 = 400 * ε :=
    epsilon_sq_add_one

  rw [hy]

  nlinarith


/- ============================================================
   Main growth estimate
   ============================================================ -/

/--
If d < 100, then

  400 - 2d > 200.
-/
lemma factor_gt_200
    (d : ℝ)
    (hd100 : d < 100) :
    200 < 400 - 2 * d := by
  linarith


/--
If d < 100, then the extra squared-distance term

  ε(400 - 2d)

is strictly greater than 1/2.
-/
lemma epsilon_factor_gt_half
    (d : ℝ)
    (hd100 : d < 100) :
    (1 : ℝ) / 2 <
      ε * (400 - 2 * d) := by

  have heps :
      (1 : ℝ) / 400 < ε :=
    epsilon_gt_one_div_400

  have hfactor :
      200 < 400 - 2 * d :=
    factor_gt_200 d hd100

  have hfactor_pos :
      0 < 400 - 2 * d := by
    linarith

  have hmul :
      ((1 : ℝ) / 400) * (400 - 2 * d)
        <
      ε * (400 - 2 * d) :=
    mul_lt_mul_of_pos_right
      heps
      hfactor_pos

  have hhalf :
      (1 : ℝ) / 2
        <
      ((1 : ℝ) / 400) * (400 - 2 * d) := by
    nlinarith

  linarith


/--
Core 200-round inequality of the official solution.

If

  y² = d² - 2εd + ε² + 1

and d < 100, then

  y² > d² + 1/2.
-/
theorem block_growth
    (d y : ℝ)
    (hd100 : d < 100)
    (hy :
      y ^ 2 =
        d ^ 2
          - 2 * ε * d
          + ε ^ 2
          + 1) :
    d ^ 2 + (1 : ℝ) / 2 < y ^ 2 := by

  have hy' :
      y ^ 2 =
        d ^ 2 + ε * (400 - 2 * d) :=
    distance_square_identity d y hy

  have hgrowth :
      (1 : ℝ) / 2
        <
      ε * (400 - 2 * d) :=
    epsilon_factor_gt_half d hd100

  rw [hy']

  linarith


/--
Same theorem if the distance expression has already been
rewritten into its simplified form.
-/
theorem block_growth'
    (d y : ℝ)
    (hd100 : d < 100)
    (hy :
      y ^ 2 =
        d ^ 2
          + ε * (400 - 2 * d)) :
    d ^ 2 + (1 : ℝ) / 2 < y ^ 2 := by

  have hgrowth :
      (1 : ℝ) / 2
        <
      ε * (400 - 2 * d) :=
    epsilon_factor_gt_half d hd100

  rw [hy]

  linarith


/- ============================================================
   Iteration arithmetic
   ============================================================ -/

/--
After 20000 blocks, gaining 1/2 in squared distance
per block gives a total gain of 10000.
-/
lemma twenty_thousand_blocks :
    (20000 : ℝ) * ((1 : ℝ) / 2) = 10000 := by
  norm_num


/--
Each block uses 200 rounds.

20000 × 200 = 4,000,000.
-/
lemma rounds_for_twenty_thousand_blocks :
    (20000 : ℕ) * 200 = 4000000 := by
  norm_num


/--
Four million rounds is below 10^9.
-/
lemma four_million_lt_billion :
    (4000000 : ℕ) < 10 ^ 9 := by
  norm_num


/- ============================================================
   A general iteration lemma
   ============================================================ -/

/--
If a sequence of squared distances increases by more than 1/2
at every step, then after n steps its value exceeds the initial
value by n/2.
-/
lemma iterated_half_growth
    (D : ℕ → ℝ)
    (h :
      ∀ n : ℕ,
        D n + (1 : ℝ) / 2 < D (n + 1)) :
    ∀ n : ℕ,
      D 0 + (n : ℝ) / 2 < D n ∨ n = 0 := by

  intro n

  induction n with

  | zero =>
      right
      rfl

  | succ n ih =>

      left

      have hn :
          D n + (1 : ℝ) / 2 < D (n + 1) :=
        h n

      rcases ih with ih | hnzero

      · have hcast :
            ((n + 1 : ℕ) : ℝ) / 2 =
              (n : ℝ) / 2 + (1 : ℝ) / 2 := by
          push_cast
          ring

        rw [hcast]

        linarith

      · subst n

        norm_num at hn ⊢

        exact hn


/--
Specialization to 20000 successful 200-round blocks.
-/
lemma growth_after_20000_blocks
    (D : ℕ → ℝ)
    (h :
      ∀ n : ℕ,
        D n + (1 : ℝ) / 2 < D (n + 1)) :
    D 0 + 10000 < D 20000 := by

  have hgrowth :=
    iterated_half_growth D h 20000

  rcases hgrowth with hgrowth | hzero

  · norm_num at hgrowth ⊢
    exact hgrowth

  · norm_num at hzero


end

end IMO2017P3
