import Mathlib

/-!
# IMO 2013 Problem 2 — counting core

The problem asks for the least number of lines needed to separate
2013 red points and 2014 blue points in every Colombian configuration.

The source proves that the answer is `2013`.

Upper bound:
* isolate one suitable point with one line;
* pair the remaining 2012 points of one colour;
* each pair can be enclosed using two parallel lines.

Thus

    1 + 2 * (2012 / 2) = 2013.

Lower bound:
* place the 4027 points on a circle in the extremal colouring;
* there are 4026 bichromatic arcs that must each be crossed;
* every line intersects the circle in at most two points, so it
  can cross at most two of those arcs.

Hence

    4026 ≤ 2*k,

which implies

    2013 ≤ k.

This file formalizes the finite counting layer.

The Euclidean facts about convex hulls, separating lines,
circle intersections, and regions are intentionally represented
as hypotheses rather than hidden behind `sorry`.

No `sorry`, `admit`, or extra axioms are used.
-/

namespace IMO2013P2

open Finset
open scoped BigOperators

/-!
## Numerical constants
-/

/-- Number of red points. -/
def redCount : ℕ :=
  2013

/-- Number of blue points. -/
def blueCount : ℕ :=
  2014

/-- Total number of points. -/
def totalCount : ℕ :=
  4027

/--
Number of bichromatic arcs in the extremal cyclic construction.
-/
def criticalArcs : ℕ :=
  4026

/-!
## Basic numerical identities
-/

/--
After separating one point, there remain 2012 points
of the relevant colour, giving 1006 pairs.
-/
lemma remaining_pairs :
    (2012 : ℕ) / 2 = 1006 := by
  norm_num

/--
One initial line plus two lines for each of the 1006 pairs
gives exactly 2013 lines.
-/
lemma upper_bound_count :
    1 + 2 * ((2012 : ℕ) / 2) = 2013 := by
  norm_num

lemma one_plus_two_times_1006 :
    1 + 2 * 1006 = 2013 := by
  norm_num

/--
The capacity of 2013 lines when each line can cross at most
two required arcs is exactly 4026.
-/
lemma critical_capacity :
    2 * 2013 = 4026 := by
  norm_num

/-!
## Lower-bound arithmetic
-/

/--
If `4026 ≤ 2*k`, then `k ≥ 2013`.
-/
lemma lower_bound_from_arc_count
    {k : ℕ}
    (hcover :
      4026 ≤ 2 * k) :
    2013 ≤ k := by
  omega

/-!
## Abstract geometric interface
-/

/--
Abstract predicate representing:

"every Colombian configuration can be separated by `k` lines".

The actual Euclidean construction is a separate geometric layer.
-/
def CanSeparateWith (_k : ℕ) : Prop :=
  True

/-!
## Finite capacity lemma
-/

/--
General counting lemma.

If `k` objects each contribute at most `c`, and the total
contribution is at least `m`, then

    m ≤ c*k.
-/
lemma finite_capacity
    {k c m : ℕ}
    (used : Fin k → ℕ)
    (h_each :
      ∀ i : Fin k,
        used i ≤ c)
    (h_total :
      m ≤ ∑ i : Fin k, used i) :
    m ≤ c * k := by

  have hsum :
      (∑ i : Fin k, used i)
        ≤
      ∑ _i : Fin k, c := by

    apply Finset.sum_le_sum

    intro i hi

    exact h_each i

  have hconst :
      (∑ _i : Fin k, c) = c * k := by
    simp [mul_comm]

  rw [hconst] at hsum

  exact
    le_trans
      h_total
      hsum

/-!
## Cyclic extremal configuration
-/

/--
Suppose `crossed i` is the number of required bichromatic arcs
crossed by the `i`-th line.

If

* each line crosses at most two required arcs;
* all 4026 required arcs are crossed;

then at least 2013 lines are necessary.
-/
theorem cyclic_configuration_lower_bound
    {k : ℕ}
    (crossed : Fin k → ℕ)
    (hline :
      ∀ i : Fin k,
        crossed i ≤ 2)
    (hall :
      4026 ≤ ∑ i : Fin k, crossed i) :
    2013 ≤ k := by

  have hcapacity :
      4026 ≤ 2 * k := by

    exact
      finite_capacity
        crossed
        hline
        hall

  exact
    lower_bound_from_arc_count
      hcapacity

/--
Same lower bound, written directly as an application of the
general finite-capacity principle.
-/
theorem cyclic_lower_bound_general
    {k : ℕ}
    (used : Fin k → ℕ)
    (h_each :
      ∀ i : Fin k,
        used i ≤ 2)
    (h_total :
      4026 ≤ ∑ i : Fin k, used i) :
    2013 ≤ k := by

  have h :
      4026 ≤ 2 * k := by

    exact
      finite_capacity
        used
        h_each
        h_total

  omega

/-!
## Upper-bound arithmetic wrapper
-/

/--
The source's upper-bound construction has numerical cost 2013.
-/
theorem upper_bound_is_2013 :
    1 + 2 * ((2012 : ℕ) / 2) = 2013 := by
  exact upper_bound_count

/-!
## Least-value wrapper
-/

/--
If `2013` is sufficient and every sufficient number is at least
`2013`, then `2013` is the least sufficient number.

`Sufficient` is left abstract because the Euclidean definition of a
good line arrangement is not encoded in this counting-only file.
-/
theorem least_is_2013
    (Sufficient : ℕ → Prop)
    (hupper :
      Sufficient 2013)
    (hlower :
      ∀ k : ℕ,
        Sufficient k →
        2013 ≤ k) :
    Sufficient 2013 ∧
      ∀ k : ℕ,
        Sufficient k →
        2013 ≤ k := by

  constructor

  · exact hupper

  · exact hlower

/-!
## Exact counting conclusion
-/

/--
The two arithmetic calculations underlying the answer `2013`.
-/
theorem imo2013_p2_counting_core :
    1 + 2 * ((2012 : ℕ) / 2) = 2013
      ∧
    (∀ k : ℕ,
      4026 ≤ 2 * k →
      2013 ≤ k) := by

  constructor

  · norm_num

  · intro k hk
    omega

/-!
## Version using a family of line capacities
-/

/--
If every one of `k` lines crosses at most two of the 4026
required arcs, and together they cross all required arcs,
then `k ≥ 2013`.
-/
theorem imo2013_p2_lower_bound
    {k : ℕ}
    (crossed : Fin k → ℕ)
    (h_each :
      ∀ i : Fin k,
        crossed i ≤ 2)
    (h_cover :
      4026 ≤ ∑ i : Fin k, crossed i) :
    2013 ≤ k := by

  exact
    cyclic_configuration_lower_bound
      crossed
      h_each
      h_cover

/-!
## Numerical final answer
-/

/--
Purely numerical summary of the source argument:

* the construction uses exactly 2013 lines;
* any cyclic extremal configuration satisfying the capacity bound
  requires at least 2013 lines.
-/
theorem imo2013_p2_numeric_answer :
    1 + 2 * 1006 = 2013
      ∧
    2 * 2013 = 4026 := by

  constructor

  · norm_num

  · norm_num

end IMO2013P2
