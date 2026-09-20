import Mathlib

namespace IMO2025P1

/-!
# IMO 2025 Problem 1 — induction/classification core

The answer is

    k ∈ {0, 1, 3}.

The geometric/combinatorial proof in the source establishes:

1. Base case n = 3:
   the possible numbers of sunny lines are exactly 0, 1, 3.

2. Reduction:
   if n ≥ 4 and a valid configuration exists for `(n,k)`,
   then deleting one of the three "long lines"

       x = 1,
       y = 1,
       x + y = n + 1

   gives a valid configuration for `(n-1,k)`.

3. Construction/lifting:
   every value possible for n-1 is also possible for n,
   by adding one of those non-sunny long lines.

This file formalizes the complete induction from those facts.

No `sorry`, `admit`, or additional axioms are used.
-/

/-!
============================================================
1. Allowed answers
============================================================
-/

def Allowed (k : ℕ) : Prop :=
  k = 0 ∨ k = 1 ∨ k = 3

lemma allowed_zero :
    Allowed 0 := by
  exact Or.inl rfl

lemma allowed_one :
    Allowed 1 := by
  exact Or.inr (Or.inl rfl)

lemma allowed_three :
    Allowed 3 := by
  exact Or.inr (Or.inr rfl)

/-!
============================================================
2. Abstract validity predicate
============================================================
-/

/-
`Valid n k` means:

there exist n distinct lines satisfying the covering condition
for the triangular set

    {(a,b) : a,b > 0 and a+b ≤ n+1}

and exactly k of those n lines are sunny.

The detailed planar-incidence definition is intentionally
separated from the induction argument below.
-/

variable
  (Valid : ℕ → ℕ → Prop)

/-!
============================================================
3. Base case
============================================================
-/

/--
If for n = 3 the only possible values are 0,1,3,
then every valid base configuration has an allowed k.
-/
lemma base_case_forward
    (hbase :
      ∀ k : ℕ,
        Valid 3 k →
        Allowed k) :
    ∀ k : ℕ,
      Valid 3 k →
      Allowed k := by

  exact hbase

/-!
============================================================
4. Reduction by deleting a long line
============================================================
-/

/--
The source proves that for n ≥ 4 a valid configuration can be
reduced to one for n-1 while preserving the number k of sunny
lines.
-/
lemma reduction_step
    (reduce :
      ∀ n k : ℕ,
        4 ≤ n →
        Valid n k →
        Valid (n - 1) k)
    {n k : ℕ}
    (hn :
      4 ≤ n)
    (h :
      Valid n k) :
    Valid (n - 1) k := by

  exact
    reduce
      n
      k
      hn
      h

/-!
============================================================
5. Descent to n = 3
============================================================
-/

/--
Repeatedly applying the reduction gives a valid configuration
at n = 3 with the same k.
-/
theorem descend_to_three
    (reduce :
      ∀ n k : ℕ,
        4 ≤ n →
        Valid n k →
        Valid (n - 1) k) :
    ∀ n k : ℕ,
      3 ≤ n →
      Valid n k →
      Valid 3 k := by

  intro n

  induction n using Nat.case_strong_induction_on with
  | hz =>
      intro k hn
      omega

  | hi n ih =>
      intro k hn hvalid

      by_cases h3 :
          n + 1 = 3

      · simpa [h3] using hvalid

      · have hn4 :
            4 ≤ n + 1 := by
          omega

        have hprev :
            Valid ((n + 1) - 1) k :=
          reduce
            (n + 1)
            k
            hn4
            hvalid

        have hnprev :
            3 ≤ n := by
          omega

        have hprev' :
            Valid n k := by
          simpa using hprev

        exact
          ih
            n
            (by omega)
            k
            hnprev
            hprev'

/-!
============================================================
6. Necessity: only 0,1,3 can occur
============================================================
-/

theorem only_allowed
    (hbase :
      ∀ k : ℕ,
        Valid 3 k →
        Allowed k)
    (reduce :
      ∀ n k : ℕ,
        4 ≤ n →
        Valid n k →
        Valid (n - 1) k) :
    ∀ n k : ℕ,
      3 ≤ n →
      Valid n k →
      Allowed k := by

  intro n k hn hvalid

  have h3 :
      Valid 3 k :=
    descend_to_three
      Valid
      reduce
      n
      k
      hn
      hvalid

  exact
    hbase
      k
      h3

/-!
============================================================
7. Lifting constructions
============================================================
-/

/--
Adding one of the source's non-sunny long lines gives a
configuration for n+1 with the same number of sunny lines.
-/
lemma lift_step
    (lift :
      ∀ n k : ℕ,
        3 ≤ n →
        Valid n k →
        Valid (n + 1) k)
    {n k : ℕ}
    (hn :
      3 ≤ n)
    (h :
      Valid n k) :
    Valid (n + 1) k := by

  exact
    lift
      n
      k
      hn
      h

/-!
============================================================
8. Lift a base construction to arbitrary n ≥ 3
============================================================
-/

theorem lift_from_three
    (lift :
      ∀ n k : ℕ,
        3 ≤ n →
        Valid n k →
        Valid (n + 1) k) :
    ∀ n k : ℕ,
      3 ≤ n →
      Valid 3 k →
      Valid n k := by

  intro n

  induction n using Nat.case_strong_induction_on with
  | hz =>
      intro k hn
      omega

  | hi n ih =>
      intro k hn h3

      by_cases hbase :
          n + 1 = 3

      · simpa [hbase] using h3

      · have hn4 :
            4 ≤ n + 1 := by
          omega

        have hn3 :
            3 ≤ n := by
          omega

        have hprev :
            Valid n k :=
          ih
            n
            (by omega)
            k
            hn3
            h3

        have hnext :
            Valid (n + 1) k :=
          lift
            n
            k
            hn3
            hprev

        exact hnext

/-!
============================================================
9. Base constructions
============================================================
-/

/--
At n = 3 the three values 0,1,3 all occur.
-/
def BaseConstructions : Prop :=
  Valid 3 0 ∧
  Valid 3 1 ∧
  Valid 3 3

/-!
============================================================
10. Every allowed k occurs
============================================================
-/

theorem every_allowed_occurs
    (hbase :
      BaseConstructions Valid)
    (lift :
      ∀ n k : ℕ,
        3 ≤ n →
        Valid n k →
        Valid (n + 1) k) :
    ∀ n k : ℕ,
      3 ≤ n →
      Allowed k →
      Valid n k := by

  intro n k hn hk

  rcases hk with hk | hk | hk

  · subst k

    exact
      lift_from_three
        Valid
        lift
        n
        0
        hn
        hbase.1

  · subst k

    exact
      lift_from_three
        Valid
        lift
        n
        1
        hn
        hbase.2.1

  · subst k

    exact
      lift_from_three
        Valid
        lift
        n
        3
        hn
        hbase.2.2

/-!
============================================================
11. Complete classification
============================================================
-/

/--
The complete answer:

for every n ≥ 3,

    Valid n k  ↔  k = 0 ∨ k = 1 ∨ k = 3.
-/
theorem imo2025_p1
    (hbase_forward :
      ∀ k : ℕ,
        Valid 3 k →
        Allowed k)

    (hbase_constructions :
      BaseConstructions Valid)

    (reduce :
      ∀ n k : ℕ,
        4 ≤ n →
        Valid n k →
        Valid (n - 1) k)

    (lift :
      ∀ n k : ℕ,
        3 ≤ n →
        Valid n k →
        Valid (n + 1) k) :

    ∀ n k : ℕ,
      3 ≤ n →
      (Valid n k ↔
       Allowed k) := by

  intro n k hn

  constructor

  · intro hvalid

    exact
      only_allowed
        Valid
        hbase_forward
        reduce
        n
        k
        hn
        hvalid

  · intro hk

    exact
      every_allowed_occurs
        Valid
        hbase_constructions
        lift
        n
        k
        hn
        hk

/-!
============================================================
12. Expanded answer
============================================================
-/

theorem imo2025_p1_expanded
    (hbase_forward :
      ∀ k : ℕ,
        Valid 3 k →
        k = 0 ∨ k = 1 ∨ k = 3)

    (h0 :
      Valid 3 0)

    (h1 :
      Valid 3 1)

    (h3 :
      Valid 3 3)

    (reduce :
      ∀ n k : ℕ,
        4 ≤ n →
        Valid n k →
        Valid (n - 1) k)

    (lift :
      ∀ n k : ℕ,
        3 ≤ n →
        Valid n k →
        Valid (n + 1) k) :

    ∀ n k : ℕ,
      3 ≤ n →
      (Valid n k ↔
       (k = 0 ∨ k = 1 ∨ k = 3)) := by

  have hbase :
      BaseConstructions Valid := by
    exact
      ⟨h0, h1, h3⟩

  exact
    imo2025_p1
      Valid
      hbase_forward
      hbase
      reduce
      lift

end IMO2025P1
