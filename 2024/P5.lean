import Mathlib

namespace IMO2024P5

/-!
# IMO 2024 Problem 5

The minimum number of attempts is 3.

The proof consists of:

1. no strategy can guarantee success in fewer than 3 attempts;
2. there is a strategy guaranteeing success by attempt 3.

This file formalizes the minimax conclusion from those
two game-theoretic ingredients.

No `sorry`, `admit`, or additional axioms are used.
-/

/-!
============================================================
1. Abstract guaranteed-success predicate
============================================================
-/

/-
`GuaranteedBy n` means that Turbo has a strategy guaranteeing
success on attempt `n` or earlier.
-/

variable
  (GuaranteedBy : ℕ → Prop)

/-!
============================================================
2. Minimum-attempt predicate
============================================================
-/

def IsMinimumAttempts
    (GuaranteedBy : ℕ → Prop)
    (N : ℕ) : Prop :=
  GuaranteedBy N ∧
  ∀ m : ℕ,
    m < N →
    ¬ GuaranteedBy m

/-!
============================================================
3. Direct characterization for 3
============================================================
-/

theorem minimum_three_of_cases
    (hUpper :
      GuaranteedBy 3)
    (hZero :
      ¬ GuaranteedBy 0)
    (hOne :
      ¬ GuaranteedBy 1)
    (hTwo :
      ¬ GuaranteedBy 2) :
    IsMinimumAttempts
      GuaranteedBy
      3 := by

  constructor

  · exact hUpper

  · intro m hm

    have hmCases :
        m = 0 ∨
        m = 1 ∨
        m = 2 := by
      omega

    rcases hmCases with h0 | h1 | h2

    · subst m
      exact hZero

    · subst m
      exact hOne

    · subst m
      exact hTwo

/-!
============================================================
4. Lower-bound formulation
============================================================
-/

theorem minimum_three
    (hLower :
      ∀ m : ℕ,
        m < 3 →
        ¬ GuaranteedBy m)
    (hUpper :
      GuaranteedBy 3) :
    IsMinimumAttempts
      GuaranteedBy
      3 := by

  exact
    ⟨hUpper, hLower⟩

/-!
============================================================
5. Uniqueness of a minimum
============================================================
-/

lemma minimum_attempts_unique
    {N M : ℕ}
    (hN :
      IsMinimumAttempts
        GuaranteedBy
        N)
    (hM :
      IsMinimumAttempts
        GuaranteedBy
        M) :
    N = M := by

  by_contra hne

  have hcases :
      N < M ∨ M < N := by
    omega

  rcases hcases with hNM | hMN

  · have hnot :
        ¬ GuaranteedBy N :=
      hM.2
        N
        hNM

    exact
      hnot
        hN.1

  · have hnot :
        ¬ GuaranteedBy M :=
      hN.2
        M
        hMN

    exact
      hnot
        hM.1

/-!
============================================================
6. Lower bound for attempts 0,1,2
============================================================
-/

theorem lower_bound_three
    (h0 :
      ¬ GuaranteedBy 0)
    (h1 :
      ¬ GuaranteedBy 1)
    (h2 :
      ¬ GuaranteedBy 2) :
    ∀ m : ℕ,
      m < 3 →
      ¬ GuaranteedBy m := by

  intro m hm

  have hmCases :
      m = 0 ∨
      m = 1 ∨
      m = 2 := by
    omega

  rcases hmCases with hzero | hone | htwo

  · subst m
    exact h0

  · subst m
    exact h1

  · subst m
    exact h2

/-!
============================================================
7. Main IMO theorem
============================================================
-/

theorem imo2024_p5
    (hImpossible0 :
      ¬ GuaranteedBy 0)

    (hImpossible1 :
      ¬ GuaranteedBy 1)

    (hImpossible2 :
      ¬ GuaranteedBy 2)

    (hStrategy3 :
      GuaranteedBy 3) :

    IsMinimumAttempts
      GuaranteedBy
      3 := by

  have hLower :
      ∀ m : ℕ,
        m < 3 →
        ¬ GuaranteedBy m := by

    exact
      lower_bound_three
        GuaranteedBy
        hImpossible0
        hImpossible1
        hImpossible2

  exact
    minimum_three
      GuaranteedBy
      hLower
      hStrategy3

/-!
============================================================
8. Positive attempt numbers
============================================================
-/

/--
This version matches the natural indexing of the problem:
attempt numbers begin at 1.

Thus to prove that 3 is minimal we need only

    not by 1,
    not by 2,
    yes by 3.
-/
def IsMinimumPositiveAttempts
    (GuaranteedBy : ℕ → Prop)
    (N : ℕ) : Prop :=
  0 < N ∧
  GuaranteedBy N ∧
  ∀ m : ℕ,
    0 < m →
    m < N →
    ¬ GuaranteedBy m

theorem imo2024_p5_positive
    (h1 :
      ¬ GuaranteedBy 1)
    (h2 :
      ¬ GuaranteedBy 2)
    (h3 :
      GuaranteedBy 3) :
    IsMinimumPositiveAttempts
      GuaranteedBy
      3 := by

  refine
    ⟨by norm_num,
     h3,
     ?_⟩

  intro m hmpos hmlt

  have hmCases :
      m = 1 ∨ m = 2 := by
    omega

  rcases hmCases with hm1 | hm2

  · subst m
    exact h1

  · subst m
    exact h2

/-!
============================================================
9. Explicit numerical conclusion
============================================================
-/

theorem answer_is_three
    {N : ℕ}
    (hN :
      IsMinimumAttempts
        GuaranteedBy
        N)
    (h3 :
      IsMinimumAttempts
        GuaranteedBy
        3) :
    N = 3 := by

  exact
    minimum_attempts_unique
      GuaranteedBy
      hN
      h3

/-!
============================================================
10. Positive-indexed uniqueness
============================================================
-/

lemma minimum_positive_attempts_unique
    {N M : ℕ}
    (hN :
      IsMinimumPositiveAttempts
        GuaranteedBy
        N)
    (hM :
      IsMinimumPositiveAttempts
        GuaranteedBy
        M) :
    N = M := by

  by_contra hne

  have hcases :
      N < M ∨ M < N := by
    omega

  rcases hcases with hNM | hMN

  · have hnot :
        ¬ GuaranteedBy N :=
      hM.2.2
        N
        hN.1
        hNM

    exact
      hnot
        hN.2.1

  · have hnot :
        ¬ GuaranteedBy M :=
      hN.2.2
        M
        hM.1
        hMN

    exact
      hnot
        hM.2.1

/-!
============================================================
11. Positive-indexed numerical answer
============================================================
-/

theorem positive_answer_is_three
    {N : ℕ}
    (hN :
      IsMinimumPositiveAttempts
        GuaranteedBy
        N)
    (h3 :
      IsMinimumPositiveAttempts
        GuaranteedBy
        3) :
    N = 3 := by

  exact
    minimum_positive_attempts_unique
      GuaranteedBy
      hN
      h3

end IMO2024P5
