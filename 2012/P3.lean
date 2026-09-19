import Mathlib

/-!
# IMO 2012 Problem 3 — potential-function core of part (b)

The source uses

    rho = 1.999 = 1999 / 1000

and the potential

    g(m) = Σ rho^(f(i,m)).

After a question, the two possible next potentials satisfy

    g_in + g_out = N + rho * g_prev.

Player A chooses the smaller one, so

    g_next ≤ (N + rho * g_prev) / 2.

If

    N + rho * B < 2 * B,

then the invariant `g < B` is preserved.

In the problem we take

    B = rho^(k+1).

No `sorry`, `admit`, or extra axioms are used.
-/

namespace IMO2012P3

open Finset
open scoped BigOperators

/-- The constant `1.999`. -/
noncomputable def rho : ℝ :=
  1999 / 1000

lemma rho_eq :
    rho = (1999 : ℝ) / 1000 := by
  rfl

lemma rho_pos :
    0 < rho := by
  unfold rho
  norm_num

lemma rho_lt_two :
    rho < 2 := by
  unfold rho
  norm_num

lemma one_lt_rho :
    1 < rho := by
  unfold rho
  norm_num

/-!
## Elementary averaging
-/

/--
For any two real numbers, their minimum is at most their average.
-/
lemma min_le_average
    (x y : ℝ) :
    min x y ≤ (x + y) / 2 := by

  by_cases h : x ≤ y

  · rw [min_eq_left h]
    linarith

  · have hyx :
        y ≤ x :=
      le_of_not_ge h

    rw [min_eq_right hyx]
    linarith

/--
If `x + y < 2B`, then one of `x,y` is strictly less than `B`.
-/
lemma min_lt_of_sum_lt_two_mul
    {x y B : ℝ}
    (h : x + y < 2 * B) :
    min x y < B := by

  have hav :
      min x y ≤ (x + y) / 2 :=
    min_le_average x y

  linarith

/-!
## One transition
-/

/--
If the two possible next potentials sum to

    N + rho*g

and this quantity is below `2B`, then the smaller branch is below `B`.
-/
lemma choose_branch_below
    {N g gin gout B : ℝ}
    (hsum :
      gin + gout = N + rho * g)
    (hbound :
      N + rho * g < 2 * B) :
    min gin gout < B := by

  apply min_lt_of_sum_lt_two_mul

  rw [hsum]

  exact hbound

/--
If

    g < B

and

    N + rho*B < 2B,

then

    N + rho*g < 2B.
-/
lemma transition_bound
    {N g B : ℝ}
    (hg : g < B)
    (hB :
      N + rho * B < 2 * B) :
    N + rho * g < 2 * B := by

  have hrho :
      0 ≤ rho :=
    le_of_lt rho_pos

  have hmul :
      rho * g ≤ rho * B := by
    exact
      mul_le_mul_of_nonneg_left
        (le_of_lt hg)
        hrho

  linarith

/--
One invariant-preserving step.
-/
lemma preserve_potential
    {N g gin gout B : ℝ}
    (hg : g < B)
    (hsum :
      gin + gout = N + rho * g)
    (hB :
      N + rho * B < 2 * B) :
    min gin gout < B := by

  have hnext :
      N + rho * g < 2 * B :=
    transition_bound hg hB

  exact
    choose_branch_below
      hsum
      hnext

/-!
## Iterating the invariant
-/

/--
If

    g 0 < B

and every step satisfies

    g(m+1) ≤ (N + rho*g(m))/2,

then the condition

    N + rho*B < 2B

implies `g(m) < B` for every `m`.
-/
theorem invariant_by_induction
    (N B : ℝ)
    (g : ℕ → ℝ)
    (hg0 :
      g 0 < B)
    (hstep :
      ∀ m : ℕ,
        g (m + 1) ≤
          (N + rho * g m) / 2)
    (hB :
      N + rho * B < 2 * B) :
    ∀ m : ℕ,
      g m < B := by

  intro m

  induction m with

  | zero =>
      exact hg0

  | succ m ih =>

      have htransition :
          N + rho * g m < 2 * B :=
        transition_bound ih hB

      have hav :
          (N + rho * g m) / 2 < B := by
        linarith

      exact
        lt_of_le_of_lt
          (hstep m)
          hav

/-!
## Concrete invariant condition
-/

/--
If

    N < (2-rho)B,

then

    N + rho*B < 2B.
-/
lemma invariant_condition
    {N B : ℝ}
    (hN :
      N < (2 - rho) * B) :
    N + rho * B < 2 * B := by

  nlinarith

/--
Since

    2 - 1.999 = 0.001.
-/
lemma two_sub_rho :
    2 - rho = (1 : ℝ) / 1000 := by

  unfold rho
  norm_num

/--
Therefore the sufficient condition can be written as

    N < B / 1000.
-/
lemma invariant_condition_1000
    {N B : ℝ}
    (hN :
      N < B / 1000) :
    N + rho * B < 2 * B := by

  apply invariant_condition

  rw [two_sub_rho]

  calc
    N < B / 1000 := hN
    _ = (1 / 1000 : ℝ) * B := by
      ring

/--
With

    B = rho^(k+1),

the sufficient condition becomes

    N < rho^(k+1)/1000.
-/
lemma concrete_invariant_condition
    {N : ℝ}
    {k : ℕ}
    (hN :
      N < rho ^ (k + 1) / 1000) :
    N + rho * rho ^ (k + 1)
      <
    2 * rho ^ (k + 1) := by

  exact
    invariant_condition_1000
      hN

/-!
## The potential invariant
-/

/--
If initially the potential is below `rho^(k+1)` and each step
chooses a branch no larger than the average, then the potential
remains below `rho^(k+1)`.
-/
theorem potential_stays_below
    (N : ℝ)
    (k : ℕ)
    (g : ℕ → ℝ)
    (hg0 :
      g 0 < rho ^ (k + 1))
    (hstep :
      ∀ m : ℕ,
        g (m + 1)
          ≤
        (N + rho * g m) / 2)
    (hN :
      N < rho ^ (k + 1) / 1000) :
    ∀ m : ℕ,
      g m < rho ^ (k + 1) := by

  apply
    invariant_by_induction
      N
      (rho ^ (k + 1))
      g
      hg0
      hstep

  exact
    concrete_invariant_condition
      hN

/-!
## Powers of rho
-/

/--
Every natural power of `rho` is positive.
-/
lemma rho_pow_pos
    (m : ℕ) :
    0 < rho ^ m := by

  exact
    pow_pos
      rho_pos
      m

/--
Every natural power of `rho` is nonnegative.
-/
lemma rho_pow_nonneg
    (m : ℕ) :
    0 ≤ rho ^ m := by

  exact
    le_of_lt
      (rho_pow_pos m)

/-!
## One term is bounded by the total potential
-/

/--
For a finite family of nonnegative reals, any individual term
is at most the total sum.
-/
lemma term_le_univ_sum
    {N : ℕ}
    (w : Fin N → ℝ)
    (i : Fin N)
    (hw :
      ∀ j : Fin N,
        0 ≤ w j) :
    w i ≤ ∑ j : Fin N, w j := by

  have h :
      w i
        ≤
      ∑ j ∈ (Finset.univ : Finset (Fin N)),
        w j := by

    exact
      Finset.single_le_sum
        (fun j _ => hw j)
        (Finset.mem_univ i)

  simpa using h

/-!
## Potential bound forbids exponent k+1
-/

/--
If

    Σ rho^(f i) < rho^(k+1),

then no individual exponent can reach `k+1`.
-/
lemma exponent_lt_of_potential_lt
    {N k : ℕ}
    (f : Fin N → ℕ)
    (hpot :
      (∑ i : Fin N, rho ^ f i)
        < rho ^ (k + 1)) :
    ∀ i : Fin N,
      f i < k + 1 := by

  intro i

  by_contra hnot

  have hki :
      k + 1 ≤ f i := by
    omega

  have hmono :
      rho ^ (k + 1)
        ≤
      rho ^ f i := by

    exact
      pow_le_pow_right₀
        (le_of_lt one_lt_rho)
        hki

  have hterm :
      rho ^ f i
        ≤
      ∑ j : Fin N,
        rho ^ f j := by

    apply
      term_le_univ_sum
        (fun j : Fin N =>
          rho ^ f j)
        i

    intro j

    exact
      rho_pow_nonneg
        (f j)

  linarith

/-!
## Final abstract form of part (b)
-/

/--
Abstract form of the potential strategy in IMO 2012 Problem 3(b).

If

* `g 0 < rho^(k+1)`,
* every next potential is at most `(N + rho*g m)/2`,
* `N < rho^(k+1)/1000`,

then

    g m < rho^(k+1)

for every step `m`.
-/
theorem imo2012_p3_part_b_core
    (N : ℝ)
    (k : ℕ)
    (g : ℕ → ℝ)
    (hg0 :
      g 0 < rho ^ (k + 1))
    (hstep :
      ∀ m : ℕ,
        g (m + 1)
          ≤
        (N + rho * g m) / 2)
    (hN :
      N < rho ^ (k + 1) / 1000) :
    ∀ m : ℕ,
      g m < rho ^ (k + 1) := by

  exact
    potential_stays_below
      N
      k
      g
      hg0
      hstep
      hN

end IMO2012P3
