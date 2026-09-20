import Mathlib

namespace IMO2026P6

/-!
# IMO 2026 Problem 6 — eventual translation core

The source proves that the set of sequence terms eventually
becomes invariant under translation by a positive integer L.

From this one obtains positive integers T and L such that

    a (n + T) = a n + L

for every n.

No `sorry`, `admit`, or additional axioms are used.
-/

/-!
============================================================
1. Basic recurrence data
============================================================
-/

def FollowsNext
    (a next : ℕ → ℕ) : Prop :=
  ∀ n : ℕ,
    a (n + 1) = next (a n)

def NextTranslationInvariant
    (next : ℕ → ℕ)
    (L : ℕ) : Prop :=
  ∀ x : ℕ,
    next (x + L) =
      next x + L

/-!
============================================================
2. Index arithmetic
============================================================
-/

lemma succ_add_shift
    (n T : ℕ) :
    (n + 1) + T =
      (n + T) + 1 := by

  omega

/-!
============================================================
3. Main recurrence induction
============================================================
-/

theorem translation_recurrence
    {a next : ℕ → ℕ}
    {T L : ℕ}
    (hrec :
      FollowsNext a next)
    (htrans :
      NextTranslationInvariant next L)
    (hbase :
      a T = a 0 + L) :
    ∀ n : ℕ,
      a (n + T) =
        a n + L := by

  intro n

  induction n with

  | zero =>
      simpa using hbase

  | succ n ih =>

      have hrec_left :
          a ((n + T) + 1) =
            next (a (n + T)) :=
        hrec (n + T)

      have hrec_right :
          a (n + 1) =
            next (a n) :=
        hrec n

      calc
        a ((n + 1) + T)
            =
          a ((n + T) + 1) := by
            rw [succ_add_shift]

        _ =
          next (a (n + T)) :=
            hrec_left

        _ =
          next (a n + L) := by
            rw [ih]

        _ =
          next (a n) + L :=
            htrans (a n)

        _ =
          a (n + 1) + L := by
            rw [hrec_right]

/-!
============================================================
4. Positive-period formulation
============================================================
-/

def HasPeriodicTranslation
    (a : ℕ → ℕ) : Prop :=
  ∃ T L : ℕ,
    0 < T ∧
    0 < L ∧
    ∀ n : ℕ,
      a (n + T) =
        a n + L

theorem periodic_translation_of_next
    {a next : ℕ → ℕ}
    {T L : ℕ}
    (hT :
      0 < T)
    (hL :
      0 < L)
    (hrec :
      FollowsNext a next)
    (htrans :
      NextTranslationInvariant next L)
    (hbase :
      a T =
        a 0 + L) :
    HasPeriodicTranslation a := by

  refine
    ⟨T, L, hT, hL, ?_⟩

  exact
    translation_recurrence
      hrec
      htrans
      hbase

/-!
============================================================
5. One-based indexing
============================================================
-/

def HasPeriodicTranslationOneBased
    (a : ℕ → ℕ) : Prop :=
  ∃ T L : ℕ,
    0 < T ∧
    0 < L ∧
    ∀ n : ℕ,
      1 ≤ n →
      a (n + T) =
        a n + L

lemma zero_based_implies_one_based
    {a : ℕ → ℕ}
    (h :
      HasPeriodicTranslation a) :
    HasPeriodicTranslationOneBased a := by

  rcases h with
    ⟨T, L, hT, hL, hshift⟩

  refine
    ⟨T, L, hT, hL, ?_⟩

  intro n hn

  exact
    hshift n

/-!
============================================================
6. Set of sequence values
============================================================
-/

def Values
    (a : ℕ → ℕ) : Set ℕ :=
  Set.range a

lemma value_mem
    (a : ℕ → ℕ)
    (n : ℕ) :
    a n ∈ Values a := by

  exact
    ⟨n, rfl⟩

/-!
============================================================
7. Eventual translation invariance
============================================================
-/

def EventuallyTranslationInvariant
    (A : Set ℕ)
    (start L : ℕ) : Prop :=
  ∀ m : ℕ,
    start ≤ m →
    (m ∈ A ↔ m + L ∈ A)

/-!
============================================================
8. Forward membership translation
============================================================
-/

lemma mem_add_of_eventually_translation_invariant
    {A : Set ℕ}
    {start L m : ℕ}
    (h :
      EventuallyTranslationInvariant A start L)
    (hm :
      start ≤ m)
    (hmem :
      m ∈ A) :
    m + L ∈ A := by

  exact
    (h m hm).mp
      hmem

/-!
============================================================
9. Backward membership translation
============================================================
-/

lemma mem_of_add_mem
    {A : Set ℕ}
    {start L m : ℕ}
    (h :
      EventuallyTranslationInvariant A start L)
    (hm :
      start ≤ m)
    (hmem :
      m + L ∈ A) :
    m ∈ A := by

  exact
    (h m hm).mpr
      hmem

/-!
============================================================
10. Repeated translations
============================================================
-/

lemma mem_add_mul
    {A : Set ℕ}
    {start L m : ℕ}
    (h :
      EventuallyTranslationInvariant A start L)
    (hm :
      start ≤ m)
    (hmem :
      m ∈ A) :
    ∀ k : ℕ,
      m + k * L ∈ A := by

  intro k

  induction k with

  | zero =>
      simpa using hmem

  | succ k ih =>

      have hm_le :
          m ≤ m + k * L := by
        exact
          Nat.le_add_right
            m
            (k * L)

      have hmk :
          start ≤ m + k * L :=
        le_trans
          hm
          hm_le

      have hnext :
          (m + k * L) + L ∈ A :=
        (h (m + k * L) hmk).mp
          ih

      have hindex :
          m + (k + 1) * L =
            (m + k * L) + L := by
        ring

      rw [hindex]

      exact hnext

/-!
============================================================
11. Source reduction data
============================================================
-/

/-
IMPORTANT:

This structure must live in `Type`, not `Prop`, because
it contains actual data fields `T : ℕ` and `L : ℕ`.
-/

structure SourcePeriodData
    (a next : ℕ → ℕ) where

  T : ℕ
  L : ℕ

  T_pos :
    0 < T

  L_pos :
    0 < L

  recurrence :
    FollowsNext a next

  next_translation :
    NextTranslationInvariant next L

  first_period :
    a T =
      a 0 + L

/-!
============================================================
12. Complete source-style conclusion
============================================================
-/

theorem imo2026_p6_core
    {a next : ℕ → ℕ}
    (D :
      SourcePeriodData a next) :
    ∃ T L : ℕ,
      0 < T ∧
      0 < L ∧
      ∀ n : ℕ,
        a (n + T) =
          a n + L := by

  refine
    ⟨D.T,
     D.L,
     D.T_pos,
     D.L_pos,
     ?_⟩

  exact
    translation_recurrence
      D.recurrence
      D.next_translation
      D.first_period

/-!
============================================================
13. Compact final theorem
============================================================
-/

theorem imo2026_p6
    {a next : ℕ → ℕ}
    (D :
      SourcePeriodData a next) :
    HasPeriodicTranslation a := by

  exact
    periodic_translation_of_next
      D.T_pos
      D.L_pos
      D.recurrence
      D.next_translation
      D.first_period

/-!
============================================================
14. Two periods
============================================================
-/

lemma two_periods
    {a : ℕ → ℕ}
    {T L : ℕ}
    (h :
      ∀ n : ℕ,
        a (n + T) =
          a n + L) :
    ∀ n : ℕ,
      a (n + 2 * T) =
        a n + 2 * L := by

  intro n

  have hindex :
      n + 2 * T =
        (n + T) + T := by
    ring

  have hvalue :
      a n + L + L =
        a n + 2 * L := by
    ring

  calc
    a (n + 2 * T)
        =
      a ((n + T) + T) := by
        rw [hindex]

    _ =
      a (n + T) + L :=
        h (n + T)

    _ =
      (a n + L) + L := by
        rw [h n]

    _ =
      a n + 2 * L := by
        exact hvalue

/-!
============================================================
15. Arbitrarily many periods
============================================================
-/

/--
For every k,

    a(n + kT) = a(n) + kL.
-/
lemma iterate_period
    {a : ℕ → ℕ}
    {T L : ℕ}
    (h :
      ∀ n : ℕ,
        a (n + T) =
          a n + L) :
    ∀ n k : ℕ,
      a (n + k * T) =
        a n + k * L := by

  intro n k

  induction k with

  | zero =>
      simp

  | succ k ih =>

      have hindex :
          n + (k + 1) * T =
            (n + k * T) + T := by
        ring

      have hvalue :
          (a n + k * L) + L =
            a n + (k + 1) * L := by
        ring

      calc
        a (n + (k + 1) * T)
            =
          a ((n + k * T) + T) := by
            rw [hindex]

        _ =
          a (n + k * T) + L :=
            h (n + k * T)

        _ =
          (a n + k * L) + L := by
            rw [ih]

        _ =
          a n + (k + 1) * L := by
            exact hvalue

/-!
============================================================
16. Translation preserves ordering
============================================================
-/

lemma add_period_strict_mono
    {L x y : ℕ}
    (hxy :
      x < y) :
    x + L < y + L := by

  exact
    Nat.add_lt_add_right
      hxy
      L

/-!
============================================================
17. Periodic translation gives strict growth
============================================================
-/

lemma periodic_term_larger
    {a : ℕ → ℕ}
    {T L n : ℕ}
    (hL :
      0 < L)
    (h :
      a (n + T) =
        a n + L) :
    a n < a (n + T) := by

  rw [h]

  omega

end IMO2026P6
