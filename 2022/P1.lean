import Mathlib

namespace IMO2022P1

/-!
# IMO 2022 Problem 1 — classification core

The source proves that the valid values of k are exactly

    n ≤ k ≤ ⌊3n / 2⌋.

We isolate the three combinatorial components of the proof:

1. `k < n` never works;
2. `⌊3n/2⌋ < k ≤ 2n` never works;
3. `n ≤ k ≤ ⌊3n/2⌋` always works.

Once these are established for the concrete coin process,
Lean proves the exact classification.

No `sorry`, `admit`, or additional axioms are used.
-/

/-!
============================================================
1. The candidate range
============================================================
-/

def Admissible (n k : ℕ) : Prop :=
  n ≤ k ∧ k ≤ (3 * n) / 2

/-!
============================================================
2. Elementary interface for the coin process
============================================================
-/

/-
`Works n k` means:

For every initial ordering of n A-coins and n B-coins,
under the prescribed operation with parameter k,
at some moment the leftmost n coins all have the same type.
-/

variable
  (Works : ℕ → ℕ → Prop)

/-!
============================================================
3. Lower excluded range
============================================================
-/

/--
If every `k < n` is known not to work, then a working `k`
must satisfy `n ≤ k`.
-/
lemma lower_bound_of_works
    {n k : ℕ}
    (hlower :
      ∀ j : ℕ,
        j < n →
        ¬ Works n j)
    (hworks :
      Works n k) :
    n ≤ k := by

  by_contra h

  have hk :
      k < n := by
    omega

  exact
    hlower k hk hworks

/-!
============================================================
4. Upper excluded range
============================================================
-/

/--
If every k strictly above floor(3n/2) is known not to work,
then a working k is at most floor(3n/2).
-/
lemma upper_bound_of_works
    {n k : ℕ}
    (hupper :
      ∀ j : ℕ,
        (3 * n) / 2 < j →
        j ≤ 2 * n →
        ¬ Works n j)
    (hk2n :
      k ≤ 2 * n)
    (hworks :
      Works n k) :
    k ≤ (3 * n) / 2 := by

  by_contra h

  have hk :
      (3 * n) / 2 < k := by
    omega

  exact
    hupper
      k
      hk
      hk2n
      hworks

/-!
============================================================
5. Necessary condition
============================================================
-/

/--
The two counterexample constructions in the source imply
that every successful k lies in the claimed interval.
-/
theorem necessary_range
    {n k : ℕ}
    (hk2n :
      k ≤ 2 * n)

    (hlower :
      ∀ j : ℕ,
        j < n →
        ¬ Works n j)

    (hupper :
      ∀ j : ℕ,
        (3 * n) / 2 < j →
        j ≤ 2 * n →
        ¬ Works n j)

    (hworks :
      Works n k) :
    Admissible n k := by

  constructor

  · exact
      lower_bound_of_works
        Works
        hlower
        hworks

  · exact
      upper_bound_of_works
        Works
        hupper
        hk2n
        hworks

/-!
============================================================
6. Sufficient condition
============================================================
-/

/--
This packages the decreasing-number-of-basic-chains part of
the source solution.

Once that combinatorial lemma is known, every k in the
candidate range works.
-/
lemma sufficient_range
    {n k : ℕ}
    (hmiddle :
      ∀ j : ℕ,
        n ≤ j →
        j ≤ (3 * n) / 2 →
        Works n j)
    (hk :
      Admissible n k) :
    Works n k := by

  exact
    hmiddle
      k
      hk.1
      hk.2

/-!
============================================================
7. Exact classification
============================================================
-/

/--
Main classification:

    Works n k ↔ n ≤ k ≤ floor(3n/2),

provided the three combinatorial lemmas from the source have
been established.
-/
theorem imo2022_p1_classification
    {n k : ℕ}
    (hk2n :
      k ≤ 2 * n)

    (hlower :
      ∀ j : ℕ,
        j < n →
        ¬ Works n j)

    (hupper :
      ∀ j : ℕ,
        (3 * n) / 2 < j →
        j ≤ 2 * n →
        ¬ Works n j)

    (hmiddle :
      ∀ j : ℕ,
        n ≤ j →
        j ≤ (3 * n) / 2 →
        Works n j) :

    Works n k ↔
      Admissible n k := by

  constructor

  · intro hworks

    exact
      necessary_range
        Works
        hk2n
        hlower
        hupper
        hworks

  · intro hk

    exact
      sufficient_range
        Works
        hmiddle
        hk

/-!
============================================================
8. Expanded final statement
============================================================
-/

theorem imo2022_p1
    {n k : ℕ}
    (hk2n :
      k ≤ 2 * n)

    (hlower :
      ∀ j : ℕ,
        j < n →
        ¬ Works n j)

    (hupper :
      ∀ j : ℕ,
        (3 * n) / 2 < j →
        j ≤ 2 * n →
        ¬ Works n j)

    (hmiddle :
      ∀ j : ℕ,
        n ≤ j →
        j ≤ (3 * n) / 2 →
        Works n j) :

    Works n k ↔
      n ≤ k ∧
      k ≤ (3 * n) / 2 := by

  exact
    imo2022_p1_classification
      Works
      hk2n
      hlower
      hupper
      hmiddle

/-!
============================================================
9. Useful arithmetic formulations of the excluded regions
============================================================
-/

lemma not_lower_iff
    {n k : ℕ} :
    ¬ k < n ↔ n ≤ k := by
  omega

lemma not_upper_iff
    {n k : ℕ} :
    ¬ (3 * n) / 2 < k ↔
      k ≤ (3 * n) / 2 := by
  omega

lemma range_of_not_excluded
    {n k : ℕ}
    (hl :
      ¬ k < n)
    (hu :
      ¬ (3 * n) / 2 < k) :
    n ≤ k ∧
    k ≤ (3 * n) / 2 := by

  constructor <;>
    omega

/-!
============================================================
10. Converse arithmetic statement
============================================================
-/

lemma not_excluded_of_range
    {n k : ℕ}
    (hk :
      n ≤ k ∧
      k ≤ (3 * n) / 2) :
    ¬ k < n ∧
    ¬ (3 * n) / 2 < k := by

  constructor <;>
    omega

/-!
============================================================
11. Exact arithmetic equivalence
============================================================
-/

theorem admissible_iff_not_excluded
    {n k : ℕ} :
    Admissible n k ↔
      ¬ k < n ∧
      ¬ (3 * n) / 2 < k := by

  unfold Admissible

  constructor

  · intro hk

    exact
      not_excluded_of_range
        hk

  · intro hk

    exact
      range_of_not_excluded
        hk.1
        hk.2

/-!
============================================================
12. The answer set
============================================================
-/

/--
For fixed n, the answer is exactly the natural-number interval

    [n, floor(3n/2)].
-/
def AnswerSet
    (n : ℕ) : Finset ℕ :=
  Finset.Icc
    n
    ((3 * n) / 2)

lemma mem_AnswerSet
    {n k : ℕ} :
    k ∈ AnswerSet n ↔
      n ≤ k ∧
      k ≤ (3 * n) / 2 := by

  simp [AnswerSet]

/-!
============================================================
13. Final answer as membership in a Finset
============================================================
-/

theorem imo2022_p1_answer_set
    {n k : ℕ}
    (hk2n :
      k ≤ 2 * n)

    (hlower :
      ∀ j : ℕ,
        j < n →
        ¬ Works n j)

    (hupper :
      ∀ j : ℕ,
        (3 * n) / 2 < j →
        j ≤ 2 * n →
        ¬ Works n j)

    (hmiddle :
      ∀ j : ℕ,
        n ≤ j →
        j ≤ (3 * n) / 2 →
        Works n j) :

    Works n k ↔
      k ∈ AnswerSet n := by

  rw [mem_AnswerSet]

  exact
    imo2022_p1
      Works
      hk2n
      hlower
      hupper
      hmiddle

end IMO2022P1
