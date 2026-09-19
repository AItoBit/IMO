import Mathlib

namespace IMO2014P5

open Finset
open scoped BigOperators

/-!
# IMO 2014 Problem 5 — final packing core

The official proof eventually reduces to the following argument.

There are `k` boxes, each of capacity `1`.
Every remaining light coin has value at most

    1 / (2k + 1).

If a light coin remains and cannot be placed in any box,
then every box has weight greater than

    1 - 1 / (2k + 1).

For `k = 100`, this forces the total weight to be greater than

    100 * (1 - 1 / 201)

which is greater than

    99 + 1/2.

This contradicts the total-value bound.

No `sorry`, `admit`, or extra axioms are used.
-/

/-!
## Summing strict lower bounds
-/

lemma sum_gt_const
    {n : ℕ}
    (hn : 0 < n)
    (w : Fin n → ℝ)
    (a : ℝ)
    (h : ∀ i : Fin n, a < w i) :
    (n : ℝ) * a <
      ∑ i : Fin n, w i := by

  have hle :
      ∀ i ∈ (Finset.univ : Finset (Fin n)),
        a ≤ w i := by
    intro i _
    exact le_of_lt (h i)

  have hex :
      ∃ i ∈ (Finset.univ : Finset (Fin n)),
        a < w i := by

    let i : Fin n :=
      ⟨0, hn⟩

    exact
      ⟨i,
       Finset.mem_univ i,
       h i⟩

  have hs :
      (∑ _i : Fin n, a) <
        ∑ i : Fin n, w i := by

    exact
      Finset.sum_lt_sum
        hle
        hex

  simpa using hs

/-!
## If a coin cannot fit, the box is almost full
-/

lemma heavy_of_cannot_fit
    {w c δ : ℝ}
    (hc :
      c ≤ δ)
    (hblocked :
      1 < w + c) :
    1 - δ < w := by
  linarith

/-!
## General packing obstruction
-/

lemma total_gt_of_leftover
    {k : ℕ}
    (hk :
      0 < k)
    (w : Fin k → ℝ)
    (c δ : ℝ)
    (hc :
      c ≤ δ)
    (hblocked :
      ∀ i : Fin k,
        1 < w i + c) :
    (k : ℝ) * (1 - δ) <
      ∑ i : Fin k, w i := by

  have hheavy :
      ∀ i : Fin k,
        1 - δ < w i := by

    intro i

    exact
      heavy_of_cannot_fit
        hc
        (hblocked i)

  exact
    sum_gt_const
      hk
      w
      (1 - δ)
      hheavy

/-!
## Threshold used in the official proof
-/

noncomputable def lightThreshold
    (k : ℕ) : ℝ :=
  1 / ((2 * k + 1 : ℕ) : ℝ)

lemma source_packing_bound
    {k : ℕ}
    (hk :
      0 < k)
    (w : Fin k → ℝ)
    (c : ℝ)
    (hc :
      c ≤ lightThreshold k)
    (hblocked :
      ∀ i : Fin k,
        1 < w i + c) :
    (k : ℝ) *
        (1 - lightThreshold k)
      <
    ∑ i : Fin k, w i := by

  exact
    total_gt_of_leftover
      hk
      w
      c
      (lightThreshold k)
      hc
      hblocked

/-!
## Algebraic identity
-/

lemma source_bound_identity
    (k : ℕ) :
    (k : ℝ) *
        (1 -
          1 / ((2 * k + 1 : ℕ) : ℝ))
      =
    (k : ℝ) -
      (k : ℝ) /
        ((2 * k + 1 : ℕ) : ℝ) := by
  ring

/-!
## Specialization to 100 boxes
-/

lemma threshold_100 :
    lightThreshold 100 =
      (1 : ℝ) / 201 := by
  norm_num [lightThreshold]

lemma numerical_bound_100 :
    (99 : ℝ) + 1 / 2
      <
    100 * (1 - 1 / 201) := by
  norm_num

lemma numerical_bound_100' :
    (199 : ℝ) / 2
      <
    100 * (1 - 1 / 201) := by
  norm_num

/-!
## Main contradiction with 100 boxes
-/

theorem no_leftover_after_100_boxes
    (w : Fin 100 → ℝ)
    (c : ℝ)
    (htotal :
      (∑ i : Fin 100, w i)
        ≤ (99 : ℝ) + 1 / 2)
    (hc :
      c ≤ 1 / 201)
    (hblocked :
      ∀ i : Fin 100,
        1 < w i + c) :
    False := by

  have hsum :
      (100 : ℝ) *
          (1 - 1 / 201)
        <
      ∑ i : Fin 100, w i := by

    exact
      total_gt_of_leftover
        (by norm_num)
        w
        c
        (1 / 201)
        hc
        hblocked

  have hnum :
      (99 : ℝ) + 1 / 2
        <
      100 * (1 - 1 / 201) :=
    numerical_bound_100

  linarith

/-!
## Each box is > 200/201
-/

lemma every_box_gt_200_div_201
    (w : Fin 100 → ℝ)
    (c : ℝ)
    (hc :
      c ≤ 1 / 201)
    (hblocked :
      ∀ i : Fin 100,
        1 < w i + c) :
    ∀ i : Fin 100,
      (200 : ℝ) / 201 < w i := by

  intro i

  have h :
      1 - (1 : ℝ) / 201 < w i :=
    heavy_of_cannot_fit
      hc
      (hblocked i)

  have heq :
      1 - (1 : ℝ) / 201 =
        (200 : ℝ) / 201 := by
    norm_num

  rw [← heq]

  exact h

/-!
## Total weight > 20000/201
-/

lemma total_gt_20000_div_201
    (w : Fin 100 → ℝ)
    (c : ℝ)
    (hc :
      c ≤ 1 / 201)
    (hblocked :
      ∀ i : Fin 100,
        1 < w i + c) :
    (20000 : ℝ) / 201 <
      ∑ i : Fin 100, w i := by

  have hbox :
      ∀ i : Fin 100,
        (200 : ℝ) / 201 < w i :=
    every_box_gt_200_div_201
      w
      c
      hc
      hblocked

  have hsum :
      (100 : ℝ) *
          ((200 : ℝ) / 201)
        <
      ∑ i : Fin 100, w i :=
    sum_gt_const
      (by norm_num)
      w
      ((200 : ℝ) / 201)
      hbox

  have heq :
      (100 : ℝ) *
          ((200 : ℝ) / 201)
        =
      (20000 : ℝ) / 201 := by
    norm_num

  rw [← heq]

  exact hsum

/-!
## Numerical comparison
-/

lemma critical_bound :
    (199 : ℝ) / 2 <
      (20000 : ℝ) / 201 := by
  norm_num

/-!
## Compact final contradiction
-/

theorem imo2014_p5_final_core
    (w : Fin 100 → ℝ)
    (c : ℝ)
    (htotal :
      (∑ i : Fin 100, w i)
        ≤ (199 : ℝ) / 2)
    (hc :
      c ≤ 1 / 201)
    (hblocked :
      ∀ i : Fin 100,
        1 < w i + c) :
    False := by

  have hlarge :
      (20000 : ℝ) / 201 <
        ∑ i : Fin 100, w i :=
    total_gt_20000_div_201
      w
      c
      hc
      hblocked

  have hcritical :
      (199 : ℝ) / 2 <
        (20000 : ℝ) / 201 :=
    critical_bound

  linarith

/-!
## Contrapositive: a light coin must fit somewhere
-/

theorem light_coin_fits_some_box
    (w : Fin 100 → ℝ)
    (c : ℝ)
    (htotal :
      (∑ i : Fin 100, w i)
        ≤ (199 : ℝ) / 2)
    (hc :
      c ≤ 1 / 201) :
    ∃ i : Fin 100,
      w i + c ≤ 1 := by

  by_contra hnone

  push Not at hnone

  have hblocked :
      ∀ i : Fin 100,
        1 < w i + c := by

    intro i

    exact hnone i

  exact
    imo2014_p5_final_core
      w
      c
      htotal
      hc
      hblocked

end IMO2014P5
