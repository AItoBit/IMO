import Mathlib

namespace IMO2018P3

open Finset
open scoped BigOperators

/-!
# IMO 2018 Problem 3 — arithmetic/counting core

The source introduces

    M n = maximum element in row n
    m n = minimum element in row n.

If the two numbers directly below `M n` are `a > b`,
then

    M n = a - b.

Since

    a ≤ M (n+1)
    m (n+1) ≤ b,

we get

    M n + m (n+1) ≤ M (n+1).

The final part of the source divides the integers into
"small" and "large" values and derives a counting
contradiction in the bottom row.

No `sorry`, `admit`, or extra axioms.
-/

/-!
## Triangular numbers
-/

def tri (n : ℕ) : ℕ :=
  n * (n + 1) / 2

lemma tri_2018 :
    tri 2018 = 2037171 := by
  norm_num [tri]

lemma tri_2017 :
    tri 2017 = 2035153 := by
  norm_num [tri]

lemma tri_64 :
    tri 64 = 2080 := by
  norm_num [tri]

lemma tri_difference :
    tri 2018 - tri 2017 = 2018 := by
  norm_num [tri]

lemma row_1954_numerical_bound :
    tri 2018 - tri 64 < tri 2017 := by
  norm_num [tri]

/-!
## One max/min step
-/

lemma max_min_step
    {M Mnext mnext a b : ℤ}
    (hM :
      M = a - b)
    (ha :
      a ≤ Mnext)
    (hb :
      mnext ≤ b) :
    M + mnext ≤ Mnext := by
  linarith

lemma max_next_ge
    {M Mnext mnext a b : ℤ}
    (hM :
      a - b = M)
    (ha :
      a ≤ Mnext)
    (hb :
      mnext ≤ b) :
    Mnext ≥ M + mnext := by
  linarith

/-!
## Iterating the max/min inequality
-/

/--
Abstract finite form of

    M_j ≥ M_i + Σ m_k.

List accesses carry explicit bound proofs.
-/
lemma iterate_max_bound
    (M0 : ℤ)
    (xs : List ℤ)
    (M : ℕ → ℤ)
    (h0 :
      M 0 = M0)
    (hstep :
      ∀ i : ℕ,
        ∀ hi : i < xs.length,
          M (i + 1) ≥
            M i + xs[i]'hi) :
    M xs.length ≥
      M0 + xs.sum := by

  induction xs generalizing M M0 with

  | nil =>
      simpa using h0.ge

  | cons x xs ih =>

      have hfirst :
          M 1 ≥ M 0 + x := by
        have hs :=
          hstep 0 (by simp)
        simpa using hs

      let M' : ℕ → ℤ :=
        fun i => M (i + 1)

      have hstep' :
          ∀ i : ℕ,
            ∀ hi : i < xs.length,
              M' (i + 1) ≥
                M' i + xs[i]'hi := by

        intro i hi

        have hi' :
            i + 1 < (x :: xs).length := by
          simp
          omega

        have hs :=
          hstep (i + 1) hi'

        dsimp [M']

        simpa using hs

      have htail :
          M' xs.length ≥
            M' 0 + xs.sum :=
        ih
          (M := M')
          (M0 := M' 0)
          rfl
          hstep'

      dsimp [M'] at htail

      simp only [
        List.length_cons,
        List.sum_cons
      ]

      linarith

/-!
## Small and large values
-/

def smallThreshold : ℕ :=
  tri 2017

def IsSmall (x : ℕ) : Prop :=
  x ≤ smallThreshold

def IsLarge (x : ℕ) : Prop :=
  smallThreshold < x

lemma smallThreshold_value :
    smallThreshold = 2035153 := by
  norm_num [smallThreshold, tri]

lemma number_of_large_values :
    tri 2018 - tri 2017 = 2018 := by
  exact tri_difference

lemma early_row_upper_bound :
    tri 2018 - tri 64 <
      smallThreshold := by
  exact row_1954_numerical_bound

/-!
## Final numerical counts
-/

lemma number_of_rows_1955_to_2017 :
    2017 - 1955 + 1 = 63 := by
  norm_num

lemma outside_large_bound :
    2 * (2017 - 1955 + 1) = 126 := by
  norm_num

lemma bottom_large_lower_bound :
    2018 - 126 = 1892 := by
  norm_num

lemma bottom_nonlarge_upper_bound
    {large nonlarge : ℕ}
    (htotal :
      large + nonlarge = 2018)
    (hlarge :
      1892 ≤ large) :
    nonlarge ≤ 126 := by
  omega

/-!
## Adjacent pairs
-/

lemma adjacent_pair_count :
    2018 - 1 = 2017 := by
  norm_num

lemma spoiled_pair_bound :
    2 * 126 = 252 := by
  norm_num

lemma many_large_adjacent_pairs
    {bad good : ℕ}
    (htotal :
      bad + good = 2017)
    (hbad :
      bad ≤ 252) :
    1765 ≤ good := by
  omega

/-!
## Finite-set lemma
-/

/--
If a finite set contains at least two elements, then for
any prescribed element `e` there is an element in the set
different from `e`.
-/
lemma exists_ne_of_card_ge_two
    {α : Type*}
    [DecidableEq α]
    (s : Finset α)
    (hcard :
      2 ≤ s.card)
    (e : α) :
    ∃ x ∈ s, x ≠ e := by

  by_cases he :
      e ∈ s

  · have hcardErase :
        1 ≤ (s.erase e).card := by

      rw [Finset.card_erase_of_mem he]

      omega

    have hnonempty :
        (s.erase e).Nonempty := by

      exact
        Finset.card_pos.mp
          (by omega)

    rcases hnonempty with
      ⟨x, hx⟩

    have hxData :
        x ≠ e ∧ x ∈ s := by

      exact
        Finset.mem_erase.mp hx

    exact
      ⟨x,
       hxData.2,
       hxData.1⟩

  · have hnonempty :
        s.Nonempty := by

      exact
        Finset.card_pos.mp
          (by omega)

    rcases hnonempty with
      ⟨x, hx⟩

    have hxe :
        x ≠ e := by

      intro hxe

      subst x

      exact he hx

    exact
      ⟨x, hx, hxe⟩

lemma enough_good_pairs :
    2 ≤ 1765 := by
  norm_num

/-!
## Good pair away from the exceptional pair
-/

theorem good_pair_away_from_exception
    (goodPairs : Finset (Fin 2017))
    (hgood :
      1765 ≤ goodPairs.card)
    (exception : Fin 2017) :
    ∃ i ∈ goodPairs,
      i ≠ exception := by

  have htwo :
      2 ≤ goodPairs.card := by
    omega

  exact
    exists_ne_of_card_ge_two
      goodPairs
      htwo
      exception

/-!
## Final contradiction package
-/

theorem final_counting_contradiction
    (goodPairs : Finset (Fin 2017))
    (exception : Fin 2017)
    (hgood :
      1765 ≤ goodPairs.card)
    (hforbidden :
      ∀ i ∈ goodPairs,
        i ≠ exception →
        False) :
    False := by

  obtain ⟨i, hi, hine⟩ :=
    good_pair_away_from_exception
      goodPairs
      hgood
      exception

  exact
    hforbidden
      i
      hi
      hine

/-!
## Useful abstract form of the bottom-row count
-/

/--
If there are at least 1892 large entries in a row of
2018 entries, there are at most 126 non-large entries.
-/
theorem bottom_row_counting_core
    {large nonlarge : ℕ}
    (htotal :
      large + nonlarge = 2018)
    (hlarge :
      1892 ≤ large) :
    nonlarge ≤ 126 := by

  exact
    bottom_nonlarge_upper_bound
      htotal
      hlarge

/--
If at most 252 adjacent pairs are spoiled, among the
2017 adjacent pairs there are at least 1765 good ones.
-/
theorem adjacent_pair_counting_core
    {bad good : ℕ}
    (htotal :
      bad + good = 2017)
    (hbad :
      bad ≤ 252) :
    1765 ≤ good := by

  exact
    many_large_adjacent_pairs
      htotal
      hbad

/-!
## Combined final counting argument
-/

/--
A compact abstraction of the final paragraph of the source.

If:

* the bottom row has `large + nonlarge = 2018`;
* at least 1892 entries are large;
* `bad + good = 2017` for the adjacent pairs;
* each non-large entry can spoil at most two pairs;
* all good pairs except possibly one are impossible,

then contradiction.
-/
theorem imo2018_p3_counting_core
    (goodPairs : Finset (Fin 2017))
    (exception : Fin 2017)
    {large nonlarge bad : ℕ}
    (hentries :
      large + nonlarge = 2018)
    (hlarge :
      1892 ≤ large)
    (hbad :
      bad ≤ 2 * nonlarge)
    (hpairs :
      bad + goodPairs.card = 2017)
    (hforbidden :
      ∀ i ∈ goodPairs,
        i ≠ exception →
        False) :
    False := by

  have hnonlarge :
      nonlarge ≤ 126 :=
    bottom_nonlarge_upper_bound
      hentries
      hlarge

  have hbad252 :
      bad ≤ 252 := by

    calc
      bad
          ≤ 2 * nonlarge :=
        hbad

      _ ≤ 2 * 126 := by
        omega

      _ = 252 := by
        norm_num

  have hgood :
      1765 ≤ goodPairs.card := by

    exact
      many_large_adjacent_pairs
        hpairs
        hbad252

  exact
    final_counting_contradiction
      goodPairs
      exception
      hgood
      hforbidden

/-!
## Combined numerical summary
-/

theorem numerical_core :
    tri 2018 = 2037171 ∧
    tri 2017 = 2035153 ∧
    tri 64 = 2080 ∧
    tri 2018 - tri 64 < tri 2017 ∧
    tri 2018 - tri 2017 = 2018 ∧
    2 * 63 = 126 ∧
    2018 - 126 = 1892 ∧
    2017 - 252 = 1765 := by

  norm_num [tri]

end IMO2018P3
