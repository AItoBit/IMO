import Mathlib

namespace IMO2019P5

/-!
# IMO 2019 Problem 5 — expectation core

For a configuration `C`, let `L(C)` be the number of
operations until the process terminates.

Let

    F(n) = ∑ L(C)

where the sum ranges over all `2^n` configurations of length `n`.

The source's case division gives

    F(1) = 1

and for every `n ≥ 1`

    F(n+1) = 2 F(n) + (n+1) 2^n.

From this we prove

    F(n) / 2^n = n(n+1)/4.

No `sorry`, `admit`, or additional axioms are used.
-/

/-!
============================================================
1. The recurrence
============================================================
-/

def TotalRecurrence
    (F : ℕ → ℕ) : Prop :=
  F 1 = 1 ∧
  ∀ n : ℕ,
    1 ≤ n →
    F (n + 1) =
      2 * F n +
      (n + 1) * 2 ^ n

lemma total_one
    {F : ℕ → ℕ}
    (h : TotalRecurrence F) :
    F 1 = 1 := by
  exact h.1

lemma total_step
    {F : ℕ → ℕ}
    (h : TotalRecurrence F)
    (n : ℕ)
    (hn : 1 ≤ n) :
    F (n + 1) =
      2 * F n +
      (n + 1) * 2 ^ n := by
  exact h.2 n hn

/-!
============================================================
2. Closed form
============================================================
-/

/--
Equivalent closed form:

    2 * F(n+1) = (n+1)(n+2)2^n.
-/
theorem total_closed
    (F : ℕ → ℕ)
    (h : TotalRecurrence F) :
    ∀ n : ℕ,
      2 * F (n + 1) =
        (n + 1) * (n + 2) * 2 ^ n := by

  intro n

  induction n with

  | zero =>
      have h1 :
          F 1 = 1 :=
        h.1

      norm_num [h1]

  | succ n ih =>

      have hrec :
          F (n + 2) =
            2 * F (n + 1) +
            (n + 2) * 2 ^ (n + 1) := by

        have hs :=
          h.2 (n + 1) (by omega)

        simpa [Nat.add_assoc] using hs

      change
        2 * F (n + 2) =
          (n + 2) * (n + 3) *
            2 ^ (n + 1)

      rw [hrec]

      calc
        2 *
            (2 * F (n + 1) +
              (n + 2) * 2 ^ (n + 1))
            =
          2 * (2 * F (n + 1)) +
            2 * (n + 2) * 2 ^ (n + 1) := by
              ring

        _ =
          2 *
              ((n + 1) * (n + 2) * 2 ^ n) +
            2 * (n + 2) * 2 ^ (n + 1) := by
              rw [ih]

        _ =
          (n + 2) * (n + 3) *
            2 ^ (n + 1) := by
              rw [pow_succ]
              ring

/-!
============================================================
3. Cross-multiplied form
============================================================
-/

/--
Multiplying by two:

    4 * F(n+1)
      =
    (n+1)(n+2)2^(n+1).
-/
lemma total_cross_identity
    (F : ℕ → ℕ)
    (h : TotalRecurrence F)
    (n : ℕ) :
    4 * F (n + 1) =
      (n + 1) * (n + 2) *
        2 ^ (n + 1) := by

  have hc :=
    total_closed
      F
      h
      n

  calc
    4 * F (n + 1)
        =
      2 * (2 * F (n + 1)) := by
        ring

    _ =
      2 *
        ((n + 1) * (n + 2) *
          2 ^ n) := by
        rw [hc]

    _ =
      (n + 1) * (n + 2) *
        2 ^ (n + 1) := by
        rw [pow_succ]
        ring

/-!
============================================================
4. Fraction lemma
============================================================
-/

/--
If

    4A = BC

and `C ≠ 0`, then

    A/C = B/4.
-/
lemma div_eq_quarter_of_cross
    (A B C : ℚ)
    (hC : C ≠ 0)
    (h :
      4 * A = B * C) :
    A / C = B / 4 := by

  field_simp [hC]

  nlinarith [h]

/-!
============================================================
5. Expected value for n+1 coins
============================================================
-/

theorem expected_value_succ
    (F : ℕ → ℕ)
    (h : TotalRecurrence F)
    (n : ℕ) :
    (F (n + 1) : ℚ) /
        ((2 ^ (n + 1) : ℕ) : ℚ)
      =
    (((n + 1) * (n + 2) : ℕ) : ℚ) /
        4 := by

  have hnat :
      4 * F (n + 1) =
        (n + 1) * (n + 2) *
          2 ^ (n + 1) :=
    total_cross_identity
      F
      h
      n

  have hrat :
      (4 : ℚ) *
          (F (n + 1) : ℚ)
        =
      (((n + 1) * (n + 2) : ℕ) : ℚ) *
        ((2 ^ (n + 1) : ℕ) : ℚ) := by

    exact_mod_cast hnat

  have hden :
      ((2 ^ (n + 1) : ℕ) : ℚ) ≠ 0 := by
    positivity

  exact
    div_eq_quarter_of_cross
      (F (n + 1) : ℚ)
      (((n + 1) * (n + 2) : ℕ) : ℚ)
      ((2 ^ (n + 1) : ℕ) : ℚ)
      hden
      hrat

/-!
============================================================
6. Expected value for every positive n
============================================================
-/

theorem expected_value
    (F : ℕ → ℕ)
    (h : TotalRecurrence F)
    (n : ℕ)
    (hn : 0 < n) :
    (F n : ℚ) /
        ((2 ^ n : ℕ) : ℚ)
      =
    ((n * (n + 1) : ℕ) : ℚ) /
        4 := by

  cases n with

  | zero =>
      omega

  | succ m =>
      simpa [
        Nat.succ_eq_add_one,
        Nat.add_assoc
      ] using
        expected_value_succ
          F
          h
          m

/-!
============================================================
7. Pretty rational form
============================================================
-/

theorem expected_value_pretty
    (F : ℕ → ℕ)
    (h : TotalRecurrence F)
    (n : ℕ)
    (hn : 0 < n) :
    (F n : ℚ) /
        ((2 ^ n : ℕ) : ℚ)
      =
    (n : ℚ) * (n + 1 : ℚ) / 4 := by

  have hE :=
    expected_value
      F
      h
      n
      hn

  calc
    (F n : ℚ) /
        ((2 ^ n : ℕ) : ℚ)
        =
      ((n * (n + 1) : ℕ) : ℚ) /
        4 :=
      hE

    _ =
      (n : ℚ) * (n + 1 : ℚ) / 4 := by
        norm_num

/-!
============================================================
8. First cases
============================================================
-/

/--
For one coin:

    L(T) + L(H) = 0 + 1 = 1,

so the expectation is `1/2`.
-/
lemma expected_one_coin
    (F : ℕ → ℕ)
    (h : TotalRecurrence F) :
    (F 1 : ℚ) / 2 =
      1 / 2 := by

  have h1 :
      F 1 = 1 :=
    h.1

  rw [h1]

  norm_num

/--
For two coins the expectation is `3/2`.
-/
lemma expected_two_coins
    (F : ℕ → ℕ)
    (h : TotalRecurrence F) :
    (F 2 : ℚ) / 4 =
      3 / 2 := by

  have hE :=
    expected_value_pretty
      F
      h
      2
      (by norm_num)

  norm_num at hE

  norm_num

  exact hE

/--
For three coins the expectation is `3`.
-/
lemma expected_three_coins
    (F : ℕ → ℕ)
    (h : TotalRecurrence F) :
    (F 3 : ℚ) / 8 = 3 := by

  have hE :=
    expected_value_pretty
      F
      h
      3
      (by norm_num)

  norm_num at hE

  norm_num

  exact hE

/-!
============================================================
9. Alternative small-case proofs
============================================================
-/

/--
Directly derive the total for two coins from the recurrence.
-/
lemma total_two
    (F : ℕ → ℕ)
    (h : TotalRecurrence F) :
    F 2 = 6 := by

  have hs :=
    h.2 1 (by norm_num)

  norm_num [h.1] at hs ⊢

  exact hs

/--
Directly derive the total for three coins.
-/
lemma total_three
    (F : ℕ → ℕ)
    (h : TotalRecurrence F) :
    F 3 = 24 := by

  have h2 :
      F 2 = 6 :=
    total_two
      F
      h

  have hs :=
    h.2 2 (by norm_num)

  norm_num [h2] at hs ⊢

  exact hs

/-!
============================================================
10. Source-style final theorem
============================================================
-/

/--
Once the case analysis on configurations has established

    F 1 = 1

and

    F(n+1) = 2F(n) + (n+1)2^n,

the expected number of operations is

    n(n+1)/4.
-/
theorem imo2019_p5_expectation
    (F : ℕ → ℕ)
    (hbase :
      F 1 = 1)
    (hrec :
      ∀ n : ℕ,
        1 ≤ n →
        F (n + 1) =
          2 * F n +
          (n + 1) * 2 ^ n)
    (n : ℕ)
    (hn : 0 < n) :
    (F n : ℚ) /
        ((2 ^ n : ℕ) : ℚ)
      =
    (n : ℚ) * (n + 1 : ℚ) / 4 := by

  have hTotal :
      TotalRecurrence F :=
    ⟨hbase, hrec⟩

  exact
    expected_value_pretty
      F
      hTotal
      n
      hn

end IMO2019P5
