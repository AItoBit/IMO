import Mathlib

namespace IMO2019P4

open Finset
open scoped BigOperators

/-!
# IMO 2019 Problem 4 — bounded classification

We define

    rhs n = ∏ i ∈ range n, (2^n - 2^i).

The original equation is

    k! = rhs n.

The official argument first proves that every solution has
`n ≤ 5`, using 2-adic valuation and growth estimates.

This file formalizes the classification once that bound is known.

No `sorry`, `admit`, or additional axioms.
-/

/-!
============================================================
1. Right-hand side
============================================================
-/

def rhs (n : ℕ) : ℕ :=
  ∏ i ∈ Finset.range n,
    (2 ^ n - 2 ^ i)

def IsSolution (k n : ℕ) : Prop :=
  0 < k ∧
  0 < n ∧
  k.factorial = rhs n

/-!
============================================================
2. Small RHS values
============================================================
-/

lemma rhs_one :
    rhs 1 = 1 := by
  norm_num [rhs]

lemma rhs_two :
    rhs 2 = 6 := by
  norm_num [rhs]

lemma rhs_three :
    rhs 3 = 168 := by
  norm_num [rhs]

lemma rhs_four :
    rhs 4 = 20160 := by
  norm_num [rhs]

lemma rhs_five :
    rhs 5 = 9999360 := by
  norm_num [rhs]

/-!
============================================================
3. The two genuine solutions
============================================================
-/

lemma solution_one_one :
    IsSolution 1 1 := by
  constructor
  · norm_num
  constructor
  · norm_num
  · norm_num [rhs]

lemma solution_three_two :
    IsSolution 3 2 := by
  constructor
  · norm_num
  constructor
  · norm_num
  · norm_num [rhs]

/-!
============================================================
4. Factorial values
============================================================
-/

lemma factorial_one :
    (1 : ℕ).factorial = 1 := by
  norm_num

lemma factorial_two :
    (2 : ℕ).factorial = 2 := by
  norm_num

lemma factorial_three :
    (3 : ℕ).factorial = 6 := by
  norm_num

lemma factorial_four :
    (4 : ℕ).factorial = 24 := by
  norm_num

lemma factorial_five :
    (5 : ℕ).factorial = 120 := by
  norm_num

lemma factorial_six :
    (6 : ℕ).factorial = 720 := by
  norm_num

lemma factorial_seven :
    (7 : ℕ).factorial = 5040 := by
  norm_num

lemma factorial_eight :
    (8 : ℕ).factorial = 40320 := by
  norm_num

lemma factorial_nine :
    (9 : ℕ).factorial = 362880 := by
  norm_num

lemma factorial_ten :
    (10 : ℕ).factorial = 3628800 := by
  norm_num

lemma factorial_eleven :
    (11 : ℕ).factorial = 39916800 := by
  norm_num

/-!
============================================================
5. Monotonicity of factorial
============================================================
-/

/--
Factorial is monotone on naturals.

We prove this directly to avoid depending on a theorem name
that differs between Mathlib versions.
-/
lemma factorial_mono
    {a b : ℕ}
    (hab : a ≤ b) :
    a.factorial ≤ b.factorial := by

  induction b with

  | zero =>
      have ha :
          a = 0 := by
        omega

      subst a

      exact le_rfl

  | succ b ih =>

      by_cases hEq :
          a = b + 1

      · subst a
        exact le_rfl

      · have hab' :
            a ≤ b := by
          omega

        have hle :
            a.factorial ≤ b.factorial :=
          ih hab'

        have hstep :
            b.factorial ≤
              (b + 1).factorial := by

          rw [Nat.factorial_succ]

          calc
            b.factorial
                =
              1 * b.factorial := by
                simp

            _ ≤
              (b + 1) * b.factorial := by
                exact
                  Nat.mul_le_mul_right
                    b.factorial
                    (by omega)

        exact
          le_trans
            hle
            hstep

/-!
============================================================
6. Case n = 1
============================================================
-/

lemma solution_n_one
    {k : ℕ}
    (hk : 0 < k)
    (h :
      k.factorial = rhs 1) :
    k = 1 := by

  rw [rhs_one] at h

  by_contra hk1

  have hk2 :
      2 ≤ k := by
    omega

  have hfac :
      (2 : ℕ).factorial ≤
        k.factorial :=
    factorial_mono hk2

  norm_num at hfac

  omega

/-!
============================================================
7. Case n = 2
============================================================
-/

lemma solution_n_two
    {k : ℕ}
    (hk : 0 < k)
    (h :
      k.factorial = rhs 2) :
    k = 3 := by

  rw [rhs_two] at h

  by_cases hk3 :
      k = 3

  · exact hk3

  by_cases hklt :
      k < 3

  · have hkcases :
        k = 1 ∨ k = 2 := by
      omega

    rcases hkcases with hk1 | hk2

    · subst k
      norm_num at h

    · subst k
      norm_num at h

  · have hk4 :
        4 ≤ k := by
      omega

    have hfac :
        (4 : ℕ).factorial ≤
          k.factorial :=
      factorial_mono hk4

    norm_num at hfac

    omega

/-!
============================================================
8. Case n = 3
============================================================
-/

lemma no_solution_n_three
    {k : ℕ}
    (hk : 0 < k)
    (h :
      k.factorial = rhs 3) :
    False := by

  rw [rhs_three] at h

  by_cases hk5 :
      k ≤ 5

  · have hkcases :
        k = 1 ∨
        k = 2 ∨
        k = 3 ∨
        k = 4 ∨
        k = 5 := by
      omega

    rcases hkcases with
      hk1 | hk2 | hk3 | hk4 | hk5'

    · subst k
      norm_num at h

    · subst k
      norm_num at h

    · subst k
      norm_num at h

    · subst k
      norm_num at h

    · subst k
      norm_num at h

  · have hk6 :
        6 ≤ k := by
      omega

    have hfac :
        (6 : ℕ).factorial ≤
          k.factorial :=
      factorial_mono hk6

    norm_num at hfac

    omega

/-!
============================================================
9. Case n = 4
============================================================
-/

lemma no_solution_n_four
    {k : ℕ}
    (hk : 0 < k)
    (h :
      k.factorial = rhs 4) :
    False := by

  rw [rhs_four] at h

  by_cases hk7 :
      k ≤ 7

  · have hkcases :
        k = 1 ∨
        k = 2 ∨
        k = 3 ∨
        k = 4 ∨
        k = 5 ∨
        k = 6 ∨
        k = 7 := by
      omega

    rcases hkcases with
      hk1 | hk2 | hk3 | hk4 | hk5 | hk6 | hk7'

    · subst k
      norm_num at h

    · subst k
      norm_num at h

    · subst k
      norm_num at h

    · subst k
      norm_num at h

    · subst k
      norm_num at h

    · subst k
      norm_num at h

    · subst k
      norm_num at h

  · have hk8 :
        8 ≤ k := by
      omega

    have hfac :
        (8 : ℕ).factorial ≤
          k.factorial :=
      factorial_mono hk8

    norm_num at hfac

    omega

/-!
============================================================
10. Case n = 5
============================================================
-/

lemma no_solution_n_five
    {k : ℕ}
    (hk : 0 < k)
    (h :
      k.factorial = rhs 5) :
    False := by

  rw [rhs_five] at h

  by_cases hk10 :
      k ≤ 10

  · have hkcases :
        k = 1 ∨
        k = 2 ∨
        k = 3 ∨
        k = 4 ∨
        k = 5 ∨
        k = 6 ∨
        k = 7 ∨
        k = 8 ∨
        k = 9 ∨
        k = 10 := by
      omega

    rcases hkcases with
      hk1 | hk2 | hk3 | hk4 | hk5 |
      hk6 | hk7 | hk8 | hk9 | hk10'

    · subst k
      norm_num at h

    · subst k
      norm_num at h

    · subst k
      norm_num at h

    · subst k
      norm_num at h

    · subst k
      norm_num at h

    · subst k
      norm_num at h

    · subst k
      norm_num at h

    · subst k
      norm_num at h

    · subst k
      norm_num at h

    · subst k
      norm_num at h

  · have hk11 :
        11 ≤ k := by
      omega

    have hfac :
        (11 : ℕ).factorial ≤
          k.factorial :=
      factorial_mono hk11

    norm_num at hfac

    omega

/-!
============================================================
11. Classification for n ≤ 5
============================================================
-/

theorem classify_bounded
    {k n : ℕ}
    (hk : 0 < k)
    (hn : 0 < n)
    (hn5 : n ≤ 5)
    (h :
      k.factorial = rhs n) :
    (k = 1 ∧ n = 1)
      ∨
    (k = 3 ∧ n = 2) := by

  have hcases :
      n = 1 ∨
      n = 2 ∨
      n = 3 ∨
      n = 4 ∨
      n = 5 := by
    omega

  rcases hcases with
    hn1 | hn2 | hn3 | hn4 | hn5'

  · subst n

    left

    constructor

    · exact
        solution_n_one
          hk
          h

    · rfl

  · subst n

    right

    constructor

    · exact
        solution_n_two
          hk
          h

    · rfl

  · subst n

    exact
      False.elim
        (no_solution_n_three
          hk
          h)

  · subst n

    exact
      False.elim
        (no_solution_n_four
          hk
          h)

  · subst n

    exact
      False.elim
        (no_solution_n_five
          hk
          h)

/-!
============================================================
12. IsSolution version
============================================================
-/

theorem classify_bounded_solution
    {k n : ℕ}
    (hn5 : n ≤ 5)
    (h : IsSolution k n) :
    (k = 1 ∧ n = 1)
      ∨
    (k = 3 ∧ n = 2) := by

  rcases h with
    ⟨hk, hn, heq⟩

  exact
    classify_bounded
      hk
      hn
      hn5
      heq

/-!
============================================================
13. Converse
============================================================
-/

lemma solution_of_classified
    {k n : ℕ}
    (h :
      (k = 1 ∧ n = 1)
        ∨
      (k = 3 ∧ n = 2)) :
    IsSolution k n := by

  rcases h with h | h

  · rcases h with
      ⟨rfl, rfl⟩

    exact
      solution_one_one

  · rcases h with
      ⟨rfl, rfl⟩

    exact
      solution_three_two

/-!
============================================================
14. Complete classification from n ≤ 5
============================================================
-/

/--
Once the official valuation/growth argument proves that any
solution has `n ≤ 5`, the complete classification follows.
-/
theorem imo2019_p4_of_bound
    (hbound :
      ∀ k n : ℕ,
        IsSolution k n →
        n ≤ 5) :
    ∀ k n : ℕ,
      IsSolution k n
        ↔
      ((k = 1 ∧ n = 1)
        ∨
       (k = 3 ∧ n = 2)) := by

  intro k n

  constructor

  · intro h

    exact
      classify_bounded_solution
        (hbound k n h)
        h

  · intro h

    exact
      solution_of_classified
        h

/-!
============================================================
15. Equation form
============================================================
-/

theorem imo2019_p4_equation_of_bound
    (hbound :
      ∀ k n : ℕ,
        0 < k →
        0 < n →
        k.factorial = rhs n →
        n ≤ 5)
    (k n : ℕ)
    (hk : 0 < k)
    (hn : 0 < n) :
    k.factorial = rhs n
      ↔
    ((k = 1 ∧ n = 1)
      ∨
     (k = 3 ∧ n = 2)) := by

  constructor

  · intro h

    exact
      classify_bounded
        hk
        hn
        (hbound
          k
          n
          hk
          hn
          h)
        h

  · intro h

    rcases h with h | h

    · rcases h with
        ⟨rfl, rfl⟩

      norm_num [rhs]

    · rcases h with
        ⟨rfl, rfl⟩

      norm_num [rhs]

end IMO2019P4
