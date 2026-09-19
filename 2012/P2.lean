import Mathlib

/-!
# IMO 2012 Problem 2

Let `a₂, ..., aₙ` be positive real numbers satisfying

    a₂ * a₃ * ... * aₙ = 1.

The official solution proves, for every `k = 2,...,n`,

    (aₖ + 1)^k
      ≥ (k^k / (k-1)^(k-1)) * aₖ

using AM-GM.

Multiplying these inequalities gives

    ∏ (aₖ + 1)^k
      ≥
    (∏ k^k/(k-1)^(k-1)) * ∏ aₖ
      =
    n^n.

We use `i = 0,...,n-2`, corresponding to `k = i+2`.

No `sorry`, `admit`, or additional axioms are used.
-/

namespace IMO2012P2

open Finset
open scoped BigOperators

/-!
## Coefficients
-/

/--
The coefficient appearing in the source's AM-GM inequality:

    k^k / (k-1)^(k-1).
-/
noncomputable def coeff (k : ℕ) : ℝ :=
  ((k : ℝ) ^ k) /
    (((k - 1 : ℕ) : ℝ) ^ (k - 1))

/--
For `k ≥ 2`, the coefficient is strictly positive.
-/
lemma coeff_pos
    {k : ℕ}
    (hk : 2 ≤ k) :
    0 < coeff k := by

  have hkposNat :
      0 < k := by
    omega

  have hkm1Nat :
      0 < k - 1 := by
    omega

  have hkpos :
      0 < (k : ℝ) := by
    exact_mod_cast hkposNat

  have hkm1pos :
      0 < (((k - 1 : ℕ) : ℝ)) := by
    exact_mod_cast hkm1Nat

  unfold coeff

  have hnum :
      0 < (k : ℝ) ^ k := by
    positivity

  have hden :
      0 < (((k - 1 : ℕ) : ℝ) ^ (k - 1)) := by
    positivity

  exact div_pos hnum hden

/--
Every coefficient of the form `coeff (i+2)` is nonnegative.
-/
lemma coeff_add_two_nonneg
    (i : ℕ) :
    0 ≤ coeff (i + 2) := by

  have hk :
      2 ≤ i + 2 := by
    omega

  exact le_of_lt (coeff_pos hk)

/-!
## Telescoping coefficient product
-/

/--
The coefficient product telescopes:

    ∏_{i=0}^{m-1} coeff(i+2)
      = (m+1)^(m+1).
-/
lemma coeff_prod
    (m : ℕ) :
    (∏ i ∈ Finset.range m,
        coeff (i + 2))
      =
    (((m + 1 : ℕ) : ℝ) ^ (m + 1)) := by

  induction m with

  | zero =>
      simp [coeff]

  | succ m ih =>

      rw [Finset.prod_range_succ]
      rw [ih]

      have hsub :
          m + 2 - 1 = m + 1 := by
        omega

      have hden :
          (((m + 1 : ℕ) : ℝ) ^ (m + 1)) ≠ 0 := by
        positivity

      unfold coeff

      rw [hsub]

      have hnat :
          m + 1 + 1 = m + 2 := by
        omega

      rw [hnat]

      field_simp [hden]

/--
For `n ≥ 2`, the product corresponding to `k = 2,...,n`
is exactly `n^n`.
-/
lemma coeff_prod_to_n
    {n : ℕ}
    (hn : 2 ≤ n) :
    (∏ i ∈ Finset.range (n - 1),
        coeff (i + 2))
      =
    ((n : ℝ) ^ n) := by

  have h :=
    coeff_prod (n - 1)

  have hn1 :
      n - 1 + 1 = n := by
    omega

  rw [hn1] at h

  exact h

/-!
## Product monotonicity on nonnegative reals
-/

/--
Pointwise inequalities between nonnegative real-valued functions
can be multiplied over a finite range.

We prove this directly, rather than relying on a generic
`Finset.prod_le_prod`, because multiplication is not globally
monotone on all real numbers.
-/
lemma prod_range_le_prod_range
    (f g : ℕ → ℝ)
    (N : ℕ)
    (hf :
      ∀ i : ℕ,
        i < N →
        0 ≤ f i)
    (hg :
      ∀ i : ℕ,
        i < N →
        0 ≤ g i)
    (hfg :
      ∀ i : ℕ,
        i < N →
        f i ≤ g i) :
    (∏ i ∈ Finset.range N, f i)
      ≤
    ∏ i ∈ Finset.range N, g i := by

  induction N with

  | zero =>
      simp

  | succ N ih =>

      rw [
        Finset.prod_range_succ,
        Finset.prod_range_succ
      ]

      have hprev :
          (∏ i ∈ Finset.range N, f i)
            ≤
          ∏ i ∈ Finset.range N, g i := by

        apply ih

        · intro i hi
          apply hf i
          omega

        · intro i hi
          apply hg i
          omega

        · intro i hi
          apply hfg i
          omega

      have hfN :
          0 ≤ f N := by
        apply hf N
        omega

      have hgN :
          0 ≤ g N := by
        apply hg N
        omega

      have hfgN :
          f N ≤ g N := by
        apply hfg N
        omega

      have hgprod :
          0 ≤ ∏ i ∈ Finset.range N, g i := by

        apply Finset.prod_nonneg

        intro i hi

        have hiN :
            i < N :=
          Finset.mem_range.mp hi

        apply hg i

        omega

      exact
        mul_le_mul
          hprev
          hfgN
          hfN
          hgprod

/-!
## Multiplication of the AM-GM inequalities
-/

/--
Multiply the pointwise estimates

    coeff(i+2) * a(i+2)
      ≤
    (a(i+2)+1)^(i+2).
-/
lemma multiply_amgm_bounds
    (a : ℕ → ℝ)
    (n : ℕ)
    (_hn : 2 ≤ n)
    (hpos :
      ∀ i ∈ Finset.range (n - 1),
        0 < a (i + 2))
    (hAMGM :
      ∀ i ∈ Finset.range (n - 1),
        coeff (i + 2) * a (i + 2)
          ≤
        (a (i + 2) + 1) ^ (i + 2)) :
    (∏ i ∈ Finset.range (n - 1),
        coeff (i + 2) * a (i + 2))
      ≤
    ∏ i ∈ Finset.range (n - 1),
      (a (i + 2) + 1) ^ (i + 2) := by

  apply
    prod_range_le_prod_range
      (fun i =>
        coeff (i + 2) * a (i + 2))
      (fun i =>
        (a (i + 2) + 1) ^ (i + 2))
      (n - 1)

  /- Left factors are nonnegative. -/
  · intro i hi

    have hirange :
        i ∈ Finset.range (n - 1) :=
      Finset.mem_range.mpr hi

    have ha :
        0 < a (i + 2) :=
      hpos i hirange

    have hc :
        0 ≤ coeff (i + 2) :=
      coeff_add_two_nonneg i

    exact
      mul_nonneg
        hc
        (le_of_lt ha)

  /- Right factors are nonnegative. -/
  · intro i hi

    have hirange :
        i ∈ Finset.range (n - 1) :=
      Finset.mem_range.mpr hi

    have ha :
        0 < a (i + 2) :=
      hpos i hirange

    have hbase :
        0 ≤ a (i + 2) + 1 := by
      linarith

    positivity

  /- Pointwise AM-GM bound. -/
  · intro i hi

    have hirange :
        i ∈ Finset.range (n - 1) :=
      Finset.mem_range.mpr hi

    exact hAMGM i hirange

/-!
## Main telescoping argument
-/

/--
IMO 2012 Problem 2 after establishing the pointwise AM-GM estimate.

The assumption

    ∏ i<n-1, a(i+2) = 1

is exactly

    a₂ a₃ ... aₙ = 1.

The conclusion is

    n^n ≤
      (a₂+1)^2 (a₃+1)^3 ... (aₙ+1)^n.
-/
theorem imo2012_p2
    (a : ℕ → ℝ)
    (n : ℕ)
    (hn : 2 ≤ n)
    (hpos :
      ∀ i ∈ Finset.range (n - 1),
        0 < a (i + 2))
    (hprod :
      (∏ i ∈ Finset.range (n - 1),
          a (i + 2))
        = 1)
    (hAMGM :
      ∀ i ∈ Finset.range (n - 1),
        coeff (i + 2) * a (i + 2)
          ≤
        (a (i + 2) + 1) ^ (i + 2)) :
    ((n : ℝ) ^ n)
      ≤
    ∏ i ∈ Finset.range (n - 1),
      (a (i + 2) + 1) ^ (i + 2) := by

  have hmul :
      (∏ i ∈ Finset.range (n - 1),
          coeff (i + 2) * a (i + 2))
        ≤
      ∏ i ∈ Finset.range (n - 1),
        (a (i + 2) + 1) ^ (i + 2) :=
    multiply_amgm_bounds
      a
      n
      hn
      hpos
      hAMGM

  have hcoeff :
      (∏ i ∈ Finset.range (n - 1),
          coeff (i + 2))
        =
      ((n : ℝ) ^ n) :=
    coeff_prod_to_n hn

  have hleft :
      (∏ i ∈ Finset.range (n - 1),
          coeff (i + 2) * a (i + 2))
        =
      ((n : ℝ) ^ n) := by

    rw [Finset.prod_mul_distrib]
    rw [hcoeff]
    rw [hprod]

    ring

  rw [hleft] at hmul

  exact hmul

end IMO2012P2
