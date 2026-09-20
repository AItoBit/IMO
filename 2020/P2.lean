import Mathlib

namespace IMO2020P2

noncomputable section

/-!
# IMO 2020 Problem 2

Assume

    a ≥ b ≥ c ≥ d > 0
    a + b + c + d = 1.

We want to prove

    (a + 2b + 3c + 4d) a^a b^b c^c d^d < 1.

For real exponents we use `Real.rpow`.

The weighted AM-GM inequality

    a^a b^b c^c d^d ≤ a² + b² + c² + d²

is supplied explicitly as `hamgm`.

Everything after that step is proved in Lean without
`sorry`, `admit`, or extra axioms.
-/

/-!
============================================================
1. Definitions
============================================================
-/

def weightedProd
    (a b c d : ℝ) : ℝ :=
  Real.rpow a a *
    Real.rpow b b *
    Real.rpow c c *
    Real.rpow d d

def linearFactor
    (a b c d : ℝ) : ℝ :=
  a + 2 * b + 3 * c + 4 * d

def squareSum
    (a b c d : ℝ) : ℝ :=
  a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2

/-!
============================================================
2. Consequences of the ordering
============================================================
-/

lemma order_consequences
    {a b c d : ℝ}
    (hab : b ≤ a)
    (hbc : c ≤ b)
    (hcd : d ≤ c) :
    d ≤ b ∧
    c ≤ a ∧
    d ≤ a := by

  have hdb :
      d ≤ b :=
    le_trans hcd hbc

  have hca :
      c ≤ a :=
    le_trans hbc hab

  have hda :
      d ≤ a :=
    le_trans hdb hab

  exact
    ⟨hdb, hca, hda⟩

lemma positivity_consequences
    {a b c d : ℝ}
    (hab : b ≤ a)
    (hbc : c ≤ b)
    (hcd : d ≤ c)
    (hd : 0 < d) :
    0 < a ∧
    0 < b ∧
    0 < c ∧
    0 < d := by

  have hc :
      0 < c :=
    lt_of_lt_of_le
      hd
      hcd

  have hb :
      0 < b :=
    lt_of_lt_of_le
      hc
      hbc

  have ha :
      0 < a :=
    lt_of_lt_of_le
      hb
      hab

  exact
    ⟨ha, hb, hc, hd⟩

/-!
============================================================
3. Four linear estimates
============================================================
-/

/--
Using `d ≤ b`:

    a + 2b + 3c + 4d
      ≤
    a + 3b + 3c + 3d.
-/
lemma linear_bound_a
    {a b c d : ℝ}
    (hdb : d ≤ b) :
    a + 2 * b + 3 * c + 4 * d
      ≤
    a + 3 * b + 3 * c + 3 * d := by

  linarith

/--
Using `b ≤ a` and `d ≤ a`:

    a + 2b + 3c + 4d
      ≤
    3a + b + 3c + 3d.
-/
lemma linear_bound_b
    {a b c d : ℝ}
    (hab : b ≤ a)
    (hda : d ≤ a) :
    a + 2 * b + 3 * c + 4 * d
      ≤
    3 * a + b + 3 * c + 3 * d := by

  linarith

/--
Using `c ≤ a` and `d ≤ b`:

    a + 2b + 3c + 4d
      ≤
    3a + 3b + c + 3d.
-/
lemma linear_bound_c
    {a b c d : ℝ}
    (hca : c ≤ a)
    (hdb : d ≤ b) :
    a + 2 * b + 3 * c + 4 * d
      ≤
    3 * a + 3 * b + c + 3 * d := by

  linarith

/--
Using `d ≤ a` and `d ≤ b`:

    a + 2b + 3c + 4d
      ≤
    3a + 3b + 3c + d.
-/
lemma linear_bound_d
    {a b c d : ℝ}
    (hda : d ≤ a)
    (hdb : d ≤ b) :
    a + 2 * b + 3 * c + 4 * d
      ≤
    3 * a + 3 * b + 3 * c + d := by

  linarith

/-!
============================================================
4. Multiply the estimates by squares
============================================================
-/

lemma square_weighted_bound_a
    {a b c d : ℝ}
    (hdb : d ≤ b) :
    a ^ 2 *
        (a + 2 * b + 3 * c + 4 * d)
      ≤
    a ^ 2 *
        (a + 3 * b + 3 * c + 3 * d) := by

  exact
    mul_le_mul_of_nonneg_left
      (linear_bound_a hdb)
      (sq_nonneg a)

lemma square_weighted_bound_b
    {a b c d : ℝ}
    (hab : b ≤ a)
    (hda : d ≤ a) :
    b ^ 2 *
        (a + 2 * b + 3 * c + 4 * d)
      ≤
    b ^ 2 *
        (3 * a + b + 3 * c + 3 * d) := by

  exact
    mul_le_mul_of_nonneg_left
      (linear_bound_b hab hda)
      (sq_nonneg b)

lemma square_weighted_bound_c
    {a b c d : ℝ}
    (hca : c ≤ a)
    (hdb : d ≤ b) :
    c ^ 2 *
        (a + 2 * b + 3 * c + 4 * d)
      ≤
    c ^ 2 *
        (3 * a + 3 * b + c + 3 * d) := by

  exact
    mul_le_mul_of_nonneg_left
      (linear_bound_c hca hdb)
      (sq_nonneg c)

lemma square_weighted_bound_d
    {a b c d : ℝ}
    (hda : d ≤ a)
    (hdb : d ≤ b) :
    d ^ 2 *
        (a + 2 * b + 3 * c + 4 * d)
      ≤
    d ^ 2 *
        (3 * a + 3 * b + 3 * c + d) := by

  exact
    mul_le_mul_of_nonneg_left
      (linear_bound_d hda hdb)
      (sq_nonneg d)

/-!
============================================================
5. Correct cubic identity
============================================================
-/

/--
The sum produced by the four estimates equals

    (a+b+c+d)^3
      - 6(abc + abd + acd + bcd).

The four omitted triple products are positive.
-/
lemma cubic_identity
    (a b c d : ℝ) :
    a ^ 2 *
          (a + 3 * b + 3 * c + 3 * d)
      +
    b ^ 2 *
          (3 * a + b + 3 * c + 3 * d)
      +
    c ^ 2 *
          (3 * a + 3 * b + c + 3 * d)
      +
    d ^ 2 *
          (3 * a + 3 * b + 3 * c + d)
      =
    (a + b + c + d) ^ 3
      -
    6 *
      (a * b * c +
       a * b * d +
       a * c * d +
       b * c * d) := by

  ring

/-!
============================================================
6. Pure polynomial inequality
============================================================
-/

theorem polynomial_bound
    {a b c d : ℝ}
    (hab : b ≤ a)
    (hbc : c ≤ b)
    (hcd : d ≤ c)
    (hd : 0 < d)
    (hsum :
      a + b + c + d = 1) :
    (a + 2 * b + 3 * c + 4 * d) *
        (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2)
      <
    1 := by

  obtain
    ⟨hdb, hca, hda⟩ :=
    order_consequences
      hab
      hbc
      hcd

  obtain
    ⟨ha, hb, hc, hd'⟩ :=
    positivity_consequences
      hab
      hbc
      hcd
      hd

  have hA :
      a ^ 2 *
          (a + 2 * b + 3 * c + 4 * d)
        ≤
      a ^ 2 *
          (a + 3 * b + 3 * c + 3 * d) :=
    square_weighted_bound_a
      hdb

  have hB :
      b ^ 2 *
          (a + 2 * b + 3 * c + 4 * d)
        ≤
      b ^ 2 *
          (3 * a + b + 3 * c + 3 * d) :=
    square_weighted_bound_b
      hab
      hda

  have hC :
      c ^ 2 *
          (a + 2 * b + 3 * c + 4 * d)
        ≤
      c ^ 2 *
          (3 * a + 3 * b + c + 3 * d) :=
    square_weighted_bound_c
      hca
      hdb

  have hD :
      d ^ 2 *
          (a + 2 * b + 3 * c + 4 * d)
        ≤
      d ^ 2 *
          (3 * a + 3 * b + 3 * c + d) :=
    square_weighted_bound_d
      hda
      hdb

  have hExpand :
      (a + 2 * b + 3 * c + 4 * d) *
          (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2)
        =
      a ^ 2 *
          (a + 2 * b + 3 * c + 4 * d)
        +
      b ^ 2 *
          (a + 2 * b + 3 * c + 4 * d)
        +
      c ^ 2 *
          (a + 2 * b + 3 * c + 4 * d)
        +
      d ^ 2 *
          (a + 2 * b + 3 * c + 4 * d) := by

    ring

  have hsumBound :
      (a + 2 * b + 3 * c + 4 * d) *
          (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2)
        ≤
      a ^ 2 *
          (a + 3 * b + 3 * c + 3 * d)
        +
      b ^ 2 *
          (3 * a + b + 3 * c + 3 * d)
        +
      c ^ 2 *
          (3 * a + 3 * b + c + 3 * d)
        +
      d ^ 2 *
          (3 * a + 3 * b + 3 * c + d) := by

    rw [hExpand]

    exact
      add_le_add
        (add_le_add
          (add_le_add hA hB)
          hC)
        hD

  have htriple :
      0 <
        a * b * c +
        a * b * d +
        a * c * d +
        b * c * d := by

    positivity

  have hstrict :
      (a + b + c + d) ^ 3
          -
        6 *
          (a * b * c +
           a * b * d +
           a * c * d +
           b * c * d)
        <
      1 := by

    rw [hsum]

    norm_num only [one_pow]

    nlinarith [htriple]

  calc
    (a + 2 * b + 3 * c + 4 * d) *
          (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2)
        ≤
      a ^ 2 *
          (a + 3 * b + 3 * c + 3 * d)
        +
      b ^ 2 *
          (3 * a + b + 3 * c + 3 * d)
        +
      c ^ 2 *
          (3 * a + 3 * b + c + 3 * d)
        +
      d ^ 2 *
          (3 * a + 3 * b + 3 * c + d) :=
      hsumBound

    _ =
      (a + b + c + d) ^ 3
        -
      6 *
        (a * b * c +
         a * b * d +
         a * c * d +
         b * c * d) :=
      cubic_identity
        a b c d

    _ < 1 :=
      hstrict

/-!
============================================================
7. Positivity of the linear factor
============================================================
-/

lemma linearFactor_pos
    {a b c d : ℝ}
    (hab : b ≤ a)
    (hbc : c ≤ b)
    (hcd : d ≤ c)
    (hd : 0 < d) :
    0 <
      linearFactor a b c d := by

  obtain
    ⟨ha, hb, hc, hd'⟩ :=
    positivity_consequences
      hab
      hbc
      hcd
      hd

  unfold linearFactor

  positivity

lemma linearFactor_nonneg
    {a b c d : ℝ}
    (hab : b ≤ a)
    (hbc : c ≤ b)
    (hcd : d ≤ c)
    (hd : 0 < d) :
    0 ≤
      linearFactor a b c d := by

  exact
    le_of_lt
      (linearFactor_pos
        hab
        hbc
        hcd
        hd)

/-!
============================================================
8. Weighted AM-GM statement
============================================================
-/

/--
The weighted-AM-GM step used by the source:

    a^a b^b c^c d^d
      ≤
    a² + b² + c² + d².
-/
def WeightedAMGMStatement
    (a b c d : ℝ) : Prop :=
  weightedProd a b c d
    ≤
  squareSum a b c d

/-!
============================================================
9. Combine AM-GM and the polynomial estimate
============================================================
-/

theorem final_from_weighted_amgm
    {a b c d : ℝ}
    (hab : b ≤ a)
    (hbc : c ≤ b)
    (hcd : d ≤ c)
    (hd : 0 < d)
    (hsum :
      a + b + c + d = 1)
    (hamgm :
      WeightedAMGMStatement
        a b c d) :
    linearFactor a b c d *
        weightedProd a b c d
      <
    1 := by

  have hlin :
      0 ≤
        linearFactor a b c d :=
    linearFactor_nonneg
      hab
      hbc
      hcd
      hd

  have hamgm' :
      weightedProd a b c d
        ≤
      squareSum a b c d := by

    exact hamgm

  have hmul :
      linearFactor a b c d *
          weightedProd a b c d
        ≤
      linearFactor a b c d *
          squareSum a b c d := by

    exact
      mul_le_mul_of_nonneg_left
        hamgm'
        hlin

  have hpoly :
      linearFactor a b c d *
          squareSum a b c d
        <
      1 := by

    unfold linearFactor squareSum

    exact
      polynomial_bound
        hab
        hbc
        hcd
        hd
        hsum

  exact
    lt_of_le_of_lt
      hmul
      hpoly

/-!
============================================================
10. Expanded theorem
============================================================
-/

theorem imo2020_p2_core
    {a b c d : ℝ}
    (hab : b ≤ a)
    (hbc : c ≤ b)
    (hcd : d ≤ c)
    (hd : 0 < d)
    (hsum :
      a + b + c + d = 1)
    (hamgm :
      Real.rpow a a *
          Real.rpow b b *
          Real.rpow c c *
          Real.rpow d d
        ≤
      a ^ 2 +
        b ^ 2 +
        c ^ 2 +
        d ^ 2) :
    (a + 2 * b + 3 * c + 4 * d) *
        (Real.rpow a a *
          Real.rpow b b *
          Real.rpow c c *
          Real.rpow d d)
      <
    1 := by

  have hAMGM :
      WeightedAMGMStatement
        a b c d := by

    unfold WeightedAMGMStatement
    unfold weightedProd squareSum

    exact hamgm

  have hfinal :=
    final_from_weighted_amgm
      hab
      hbc
      hcd
      hd
      hsum
      hAMGM

  unfold linearFactor weightedProd at hfinal

  exact hfinal

/-!
============================================================
11. Standalone polynomial theorem
============================================================
-/

theorem imo2020_p2_polynomial
    {a b c d : ℝ}
    (hab : b ≤ a)
    (hbc : c ≤ b)
    (hcd : d ≤ c)
    (hd : 0 < d)
    (hsum :
      a + b + c + d = 1) :
    (a + 2 * b + 3 * c + 4 * d) *
        (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2)
      <
    1 := by

  exact
    polynomial_bound
      hab
      hbc
      hcd
      hd
      hsum

end

end IMO2020P2
