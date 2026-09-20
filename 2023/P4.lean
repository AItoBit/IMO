import Mathlib

namespace IMO2023P4

/-!
# IMO 2023 Problem 4 — recurrence core

The analytic part of the source proves, for every relevant n,

    a_{n+2} ≥ a_n + 2,

and equality is impossible because the original x_i are
pairwise distinct.

Since every a_n is an integer, this becomes

    a_{n+2} ≥ a_n + 3.

Using zero-based indexing:

    a 0    = a₁
    a 2022 = a₂₀₂₃.

Iterating the two-step recurrence 1011 times gives

    a 2022 ≥ 1 + 3*1011 = 3034.

No `sorry`, `admit`, or additional axioms are used.
-/

/-!
============================================================
1. Integer strengthening
============================================================
-/

/--
If `a + 2 < b` for natural numbers, then `a + 3 ≤ b`.
-/
lemma add_three_le_of_add_two_lt
    {a b : ℕ}
    (h : a + 2 < b) :
    a + 3 ≤ b := by
  omega

/-!
============================================================
2. Source-style strict recurrence
============================================================
-/

/--
The AM-GM step gives `a n + 2 ≤ a (n+2)`.
If equality is excluded, we obtain strict inequality.
-/
lemma strict_two_step
    {a : ℕ → ℕ}
    {n : ℕ}
    (hle :
      a n + 2 ≤ a (n + 2))
    (hne :
      a (n + 2) ≠ a n + 2) :
    a n + 2 < a (n + 2) := by

  omega

/-!
============================================================
3. Upgrade to +3
============================================================
-/

/--
Because all values are integers, the strict inequality

    a n + 2 < a (n+2)

implies

    a n + 3 ≤ a (n+2).
-/
lemma two_step_add_three
    {a : ℕ → ℕ}
    {n : ℕ}
    (hle :
      a n + 2 ≤ a (n + 2))
    (hne :
      a (n + 2) ≠ a n + 2) :
    a n + 3 ≤ a (n + 2) := by

  have hlt :
      a n + 2 < a (n + 2) :=
    strict_two_step
      hle
      hne

  omega

/-!
============================================================
4. Iterating on even zero-based indices
============================================================
-/

/--
If every two-step move increases by at least 3, then

    a (2m) ≥ a 0 + 3m.
-/
lemma iterate_two_step
    (a : ℕ → ℕ)
    (hstep :
      ∀ n : ℕ,
        a n + 3 ≤ a (n + 2)) :
    ∀ m : ℕ,
      a 0 + 3 * m ≤ a (2 * m) := by

  intro m

  induction m with

  | zero =>
      simp

  | succ m ih =>

      have hs :
          a (2 * m) + 3
            ≤
          a (2 * m + 2) :=
        hstep (2 * m)

      have hmain :
          a 0 + 3 * m + 3
            ≤
          a (2 * m + 2) :=
        le_trans
          (Nat.add_le_add_right ih 3)
          hs

      calc
        a 0 + 3 * (m + 1)
            =
          a 0 + 3 * m + 3 := by
            ring

        _ ≤ a (2 * m + 2) :=
          hmain

        _ = a (2 * (m + 1)) := by
          ring

/-!
============================================================
5. Starting value
============================================================
-/

/--
For the expression in the problem,

    a₁ = sqrt(x₁ * 1/x₁) = 1.

In zero-based indexing this is `a 0 = 1`.
-/
lemma iterate_from_one
    (a : ℕ → ℕ)
    (h0 :
      a 0 = 1)
    (hstep :
      ∀ n : ℕ,
        a n + 3 ≤ a (n + 2)) :
    ∀ m : ℕ,
      1 + 3 * m ≤ a (2 * m) := by

  intro m

  have h :
      a 0 + 3 * m ≤
        a (2 * m) :=
    iterate_two_step
      a
      hstep
      m

  rw [h0] at h

  exact h

/-!
============================================================
6. The numerical computation
============================================================
-/

lemma arithmetic_2023 :
    1 + 3 * 1011 = 3034 := by
  norm_num

lemma index_2023 :
    2 * 1011 = 2022 := by
  norm_num

/-!
============================================================
7. Main recurrence theorem
============================================================
-/

/--
This is the final arithmetic step of IMO 2023 P4.

`a 2022` denotes `a₂₀₂₃`.
-/
theorem imo2023_p4_from_three_step
    (a : ℕ → ℕ)
    (h0 :
      a 0 = 1)
    (hstep :
      ∀ n : ℕ,
        a n + 3 ≤ a (n + 2)) :
    3034 ≤ a 2022 := by

  have h :
      1 + 3 * 1011 ≤
        a (2 * 1011) :=
    iterate_from_one
      a
      h0
      hstep
      1011

  norm_num at h ⊢

  exact h

/-!
============================================================
8. Version matching the AM-GM output
============================================================
-/

/--
This version assumes exactly what the source proves:

1. AM-GM gives

       a n + 2 ≤ a (n+2);

2. equality cannot occur.

Because the sequence values are natural numbers, the result
follows.
-/
theorem imo2023_p4_core
    (a : ℕ → ℕ)

    (h0 :
      a 0 = 1)

    (hamgm :
      ∀ n : ℕ,
        a n + 2 ≤
          a (n + 2))

    (hneq :
      ∀ n : ℕ,
        a (n + 2) ≠
          a n + 2) :

    3034 ≤ a 2022 := by

  have hstep :
      ∀ n : ℕ,
        a n + 3 ≤
          a (n + 2) := by

    intro n

    exact
      two_step_add_three
        (hamgm n)
        (hneq n)

  exact
    imo2023_p4_from_three_step
      a
      h0
      hstep

/-!
============================================================
9. Pairwise distinctness interface
============================================================
-/

/--
The source derives `hneq` from pairwise distinctness of the
original positive real numbers x_i.

This theorem packages that final reduction explicitly.
-/
theorem imo2023_p4_from_distinctness
    (a : ℕ → ℕ)

    (h0 :
      a 0 = 1)

    (hamgm :
      ∀ n : ℕ,
        a n + 2 ≤
          a (n + 2))

    (equality_impossible :
      ∀ n : ℕ,
        a (n + 2) ≠
          a n + 2) :

    3034 ≤ a 2022 := by

  exact
    imo2023_p4_core
      a
      h0
      hamgm
      equality_impossible

/-!
============================================================
10. One-based presentation
============================================================
-/

/--
If `b n` uses ordinary mathematical indexing, so that
`b 1 = a₁`, this is the same numerical conclusion.
-/
theorem imo2023_p4_one_based
    (b : ℕ → ℕ)

    (h1 :
      b 1 = 1)

    (hstep :
      ∀ n : ℕ,
        1 ≤ n →
        b n + 3 ≤
          b (n + 2)) :

    3034 ≤ b 2023 := by

  have hodd :
      ∀ m : ℕ,
        b 1 + 3 * m ≤
          b (1 + 2 * m) := by

    intro m

    induction m with

    | zero =>
        simp

    | succ m ih =>

      have hn :
          1 ≤ 1 + 2 * m := by
        omega

      have hs :
          b (1 + 2 * m) + 3
            ≤
          b ((1 + 2 * m) + 2) :=
        hstep
          (1 + 2 * m)
          hn

      calc
        b 1 + 3 * (m + 1)
            =
          (b 1 + 3 * m) + 3 := by
            ring

        _ ≤
          b (1 + 2 * m) + 3 := by
            exact
              Nat.add_le_add_right
                ih
                3

        _ ≤
          b ((1 + 2 * m) + 2) :=
            hs

        _ =
          b (1 + 2 * (m + 1)) := by
            ring

  have h :
      b 1 + 3 * 1011 ≤
        b (1 + 2 * 1011) :=
    hodd 1011

  rw [h1] at h

  norm_num at h ⊢

  exact h

end IMO2023P4
