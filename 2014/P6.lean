import Mathlib

namespace IMO2014P6

/-!
# IMO 2014 Problem 6 — counting core

The source's coloring algorithm eventually produces `k` blue lines.

There are `n - k` remaining lines.

Every blue-blue intersection introduces at most two red points.
Since there are C(k,2) blue-blue intersections, the number of
available red points is at most

    2 * C(k,2) = k * (k - 1).

When no more lines can be colored blue, every remaining line
must be blocked by one of these red points. Hence

    n - k ≤ k * (k - 1).

Therefore

    n ≤ k²,

and consequently

    √n ≤ k.

This file formalizes that numerical conclusion.
No `sorry`, `admit`, or additional axioms are used.
-/

/-!
## Basic identity
-/

/--
For every natural number `k`,

    k + k(k-1) = k².
-/
lemma add_mul_pred_eq_square
    (k : ℕ) :
    k + k * (k - 1) = k * k := by

  cases k with

  | zero =>
      simp

  | succ m =>
      simp
      ring

/-!
## From remaining-line coverage to the total bound
-/

/--
If `k ≤ n` and the remaining `n-k` lines can all be
accounted for by at most `k(k-1)` blockers, then

    n ≤ k + k(k-1).
-/
lemma total_le_blue_plus_blockers
    {n k : ℕ}
    (hkn :
      k ≤ n)
    (hcover :
      n - k ≤ k * (k - 1)) :
    n ≤ k + k * (k - 1) := by

  have hdecomp :
      n - k + k = n :=
    Nat.sub_add_cancel hkn

  calc
    n =
        (n - k) + k := by
          exact hdecomp.symm

    _ ≤
        k * (k - 1) + k := by
          exact
            Nat.add_le_add_right
              hcover
              k

    _ =
        k + k * (k - 1) := by
          ac_rfl

/-!
## The key square inequality
-/

/--
The source's inequality

    n-k ≤ k(k-1)

implies

    n ≤ k².
-/
lemma square_bound
    {n k : ℕ}
    (hkn :
      k ≤ n)
    (hcover :
      n - k ≤ k * (k - 1)) :
    n ≤ k * k := by

  have htotal :
      n ≤ k + k * (k - 1) :=
    total_le_blue_plus_blockers
      hkn
      hcover

  rw [add_mul_pred_eq_square k] at htotal

  exact htotal

/-!
## Real square-root conclusion
-/

/--
If `n ≤ k²`, then

    √n ≤ k

as an inequality in the real numbers.
-/
lemma sqrt_le_of_square_bound
    {n k : ℕ}
    (h :
      n ≤ k * k) :
    Real.sqrt (n : ℝ) ≤ (k : ℝ) := by

  have hn0 :
      (0 : ℝ) ≤ (n : ℝ) := by
    positivity

  have hk0 :
      (0 : ℝ) ≤ (k : ℝ) := by
    positivity

  have hsqrt0 :
      (0 : ℝ) ≤ Real.sqrt (n : ℝ) :=
    Real.sqrt_nonneg (n : ℝ)

  have hsqrt_sq :
      (Real.sqrt (n : ℝ)) ^ 2 =
        (n : ℝ) :=
    Real.sq_sqrt hn0

  have hR :
      (n : ℝ) ≤ (k : ℝ) ^ 2 := by

    have hcast :
        (n : ℝ) ≤
          ((k * k : ℕ) : ℝ) := by
      exact_mod_cast h

    simpa [pow_two] using hcast

  nlinarith

/-!
## Main numerical theorem
-/

/--
The final counting step of IMO 2014 Problem 6.

Suppose:

* there are `n` lines in total;
* `k` of them have been colored blue;
* therefore `k ≤ n`;
* every remaining line must be covered by the red points
  produced by blue-blue intersections;
* there are at most `k(k-1)` such blockers.

Then at least `√n` lines are blue.
-/
theorem imo2014_p6_counting_core
    {n k : ℕ}
    (hkn :
      k ≤ n)
    (hcover :
      n - k ≤ k * (k - 1)) :
    Real.sqrt (n : ℝ) ≤ (k : ℝ) := by

  have hsq :
      n ≤ k * k :=
    square_bound
      hkn
      hcover

  exact
    sqrt_le_of_square_bound
      hsq

/-!
## Equivalent formulation using an explicit red-point count
-/

/--
Suppose `r` is the number of red blocking points.

If

    n-k ≤ r

and

    r ≤ k(k-1),

then again `√n ≤ k`.
-/
theorem imo2014_p6_from_red_count
    {n k r : ℕ}
    (hkn :
      k ≤ n)
    (hremaining :
      n - k ≤ r)
    (hred :
      r ≤ k * (k - 1)) :
    Real.sqrt (n : ℝ) ≤ (k : ℝ) := by

  have hcover :
      n - k ≤ k * (k - 1) :=
    le_trans
      hremaining
      hred

  exact
    imo2014_p6_counting_core
      hkn
      hcover

/-!
## Source's "two red points per blue intersection"
-/

/--
Abstract version of the source's estimate.

If there are `p` blue-blue intersections and every such
intersection introduces at most two red points, then

    r ≤ 2p.
-/
lemma red_points_bound
    {p r : ℕ}
    (h :
      r ≤ 2 * p) :
    r ≤ 2 * p := by
  exact h

/--
For `k` blue lines, twice the number of unordered pairs is
algebraically represented by

    k(k-1).

We use this form instead of division by two.
-/
def twicePairCount
    (k : ℕ) : ℕ :=
  k * (k - 1)

/--
The definition of the twice-pair count.
-/
lemma twicePairCount_eq
    (k : ℕ) :
    twicePairCount k =
      k * (k - 1) := by
  rfl

/-!
## Full abstract counting package
-/

/--
This packages precisely the final combinatorial counting
argument from the source.

`r` is the number of red blocking points.

1. Every remaining line is blocked:
       n-k ≤ r

2. The coloring algorithm creates at most two red points
   for each blue-blue pair:
       r ≤ k(k-1)

Therefore `√n ≤ k`.
-/
theorem imo2014_p6_final_count
    {n k r : ℕ}
    (hkn :
      k ≤ n)
    (hblocked :
      n - k ≤ r)
    (hred :
      r ≤ twicePairCount k) :
    Real.sqrt (n : ℝ) ≤ (k : ℝ) := by

  have hred' :
      r ≤ k * (k - 1) := by
    simpa [twicePairCount] using hred

  exact
    imo2014_p6_from_red_count
      hkn
      hblocked
      hred'

/-!
## A purely natural-number conclusion
-/

/--
The same argument without mentioning real square roots:

    n ≤ k².

This is exactly equivalent to the numerical conclusion
needed by the olympiad problem.
-/
theorem imo2014_p6_square_form
    {n k r : ℕ}
    (hkn :
      k ≤ n)
    (hblocked :
      n - k ≤ r)
    (hred :
      r ≤ k * (k - 1)) :
    n ≤ k * k := by

  have hcover :
      n - k ≤ k * (k - 1) :=
    le_trans
      hblocked
      hred

  exact
    square_bound
      hkn
      hcover

end IMO2014P6
