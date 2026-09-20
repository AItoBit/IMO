import Mathlib

namespace IMO2021P1

/-!
# IMO 2021 Problem 1 — combinatorial core

The source constructs three distinct card values `a b c`
between `n` and `2n` such that every pair has square sum.

Then, because there are only two piles, two of the three
cards lie in the same pile.

No `sorry`, `admit`, or additional axioms are used.
-/

/-!
============================================================
1. Perfect squares
============================================================
-/

def IsSquare (m : ℕ) : Prop :=
  ∃ r : ℕ, m = r ^ 2

/-!
============================================================
2. Three objects in two piles
============================================================
-/

lemma three_bool_pigeonhole
    (x y z : Bool) :
    x = y ∨ x = z ∨ y = z := by
  cases x <;>
    cases y <;>
      cases z <;>
        simp

/-!
============================================================
3. Abstract three-card configuration
============================================================
-/

structure GoodTriple (n : ℕ) where
  a : ℕ
  b : ℕ
  c : ℕ

  ha_lower : n ≤ a
  ha_upper : a ≤ 2 * n

  hb_lower : n ≤ b
  hb_upper : b ≤ 2 * n

  hc_lower : n ≤ c
  hc_upper : c ≤ 2 * n

  hab_ne : a ≠ b
  hac_ne : a ≠ c
  hbc_ne : b ≠ c

  hab_square : IsSquare (a + b)
  hac_square : IsSquare (a + c)
  hbc_square : IsSquare (b + c)

/-!
============================================================
4. Pigeonhole step
============================================================
-/

/--
If three card values form a `GoodTriple`, then in any
assignment to two piles, two distinct card values in the
same pile have square sum.
-/
theorem pair_in_same_pile
    {n : ℕ}
    (T : GoodTriple n)
    (pile : ℕ → Bool) :
    ∃ x y : ℕ,
      x ≠ y ∧
      n ≤ x ∧
      x ≤ 2 * n ∧
      n ≤ y ∧
      y ≤ 2 * n ∧
      pile x = pile y ∧
      IsSquare (x + y) := by

  have hpigeon :
      pile T.a = pile T.b ∨
      pile T.a = pile T.c ∨
      pile T.b = pile T.c :=
    three_bool_pigeonhole
      (pile T.a)
      (pile T.b)
      (pile T.c)

  rcases hpigeon with hab | hac | hbc

  · refine
      ⟨T.a,
       T.b,
       T.hab_ne,
       T.ha_lower,
       T.ha_upper,
       T.hb_lower,
       T.hb_upper,
       hab,
       T.hab_square⟩

  · refine
      ⟨T.a,
       T.c,
       T.hac_ne,
       T.ha_lower,
       T.ha_upper,
       T.hc_lower,
       T.hc_upper,
       hac,
       T.hac_square⟩

  · refine
      ⟨T.b,
       T.c,
       T.hbc_ne,
       T.hb_lower,
       T.hb_upper,
       T.hc_lower,
       T.hc_upper,
       hbc,
       T.hbc_square⟩

/-!
============================================================
5. Final IMO wrapper
============================================================
-/

/--
If for every `n ≥ 100` there exists a `GoodTriple n`,
then every partition of the cards `n, n+1, ..., 2n`
into two piles contains two cards in one pile whose sum
is a perfect square.
-/
theorem imo2021_p1
    (exists_good_triple :
      ∀ n : ℕ,
        100 ≤ n →
        ∃ T : GoodTriple n,
          True) :
    ∀ n : ℕ,
      100 ≤ n →
      ∀ pile : ℕ → Bool,
        ∃ x y : ℕ,
          x ≠ y ∧
          n ≤ x ∧
          x ≤ 2 * n ∧
          n ≤ y ∧
          y ≤ 2 * n ∧
          pile x = pile y ∧
          IsSquare (x + y) := by

  intro n hn pile

  obtain ⟨T, _⟩ :=
    exists_good_triple
      n
      hn

  exact
    pair_in_same_pile
      T
      pile

/-!
============================================================
6. Explicit square identities from the source
============================================================
-/

/--
The three algebraic identities from Solution 3:

    (2k² - 4k) + (2k² + 1) = (2k - 1)²
    (2k² - 4k) + (2k² + 4k) = (2k)²
    (2k² + 1) + (2k² + 4k) = (2k + 1)²

Over the integers these are direct ring identities.
-/

lemma source_square_identity_ab
    (k : ℤ) :
    (2 * k ^ 2 - 4 * k) +
        (2 * k ^ 2 + 1)
      =
    (2 * k - 1) ^ 2 := by
  ring

lemma source_square_identity_ac
    (k : ℤ) :
    (2 * k ^ 2 - 4 * k) +
        (2 * k ^ 2 + 4 * k)
      =
    (2 * k) ^ 2 := by
  ring

lemma source_square_identity_bc
    (k : ℤ) :
    (2 * k ^ 2 + 1) +
        (2 * k ^ 2 + 4 * k)
      =
    (2 * k + 1) ^ 2 := by
  ring

/-!
============================================================
7. Source construction over integers
============================================================
-/

def sourceA (k : ℤ) : ℤ :=
  2 * k ^ 2 - 4 * k

def sourceB (k : ℤ) : ℤ :=
  2 * k ^ 2 + 1

def sourceC (k : ℤ) : ℤ :=
  2 * k ^ 2 + 4 * k

lemma sourceA_add_sourceB
    (k : ℤ) :
    sourceA k + sourceB k =
      (2 * k - 1) ^ 2 := by
  unfold sourceA sourceB
  ring

lemma sourceA_add_sourceC
    (k : ℤ) :
    sourceA k + sourceC k =
      (2 * k) ^ 2 := by
  unfold sourceA sourceC
  ring

lemma sourceB_add_sourceC
    (k : ℤ) :
    sourceB k + sourceC k =
      (2 * k + 1) ^ 2 := by
  unfold sourceB sourceC
  ring

/-!
============================================================
8. Distinctness of the three constructed values
============================================================
-/

lemma sourceA_lt_sourceB
    {k : ℤ}
    (hk : 1 ≤ k) :
    sourceA k < sourceB k := by
  unfold sourceA sourceB
  nlinarith

lemma sourceB_lt_sourceC
    {k : ℤ}
    (hk : 1 ≤ k) :
    sourceB k < sourceC k := by
  unfold sourceB sourceC
  nlinarith

lemma sourceA_lt_sourceC
    {k : ℤ}
    (hk : 1 ≤ k) :
    sourceA k < sourceC k := by
  have h₁ :
      sourceA k < sourceB k :=
    sourceA_lt_sourceB hk

  have h₂ :
      sourceB k < sourceC k :=
    sourceB_lt_sourceC hk

  exact lt_trans h₁ h₂

/-!
============================================================
9. Interval consequence from the square bounds
============================================================
-/

/--
This is the arithmetic conversion used on page 4 of the source.

If

    n/2 + 1 ≤ (k-1)²
    (k+1)² ≤ n+1

then

    n ≤ 2k² - 4k
    2k² + 4k ≤ 2n.

We state it over ℤ to avoid natural-number subtraction.
-/
lemma source_interval_bounds
    {n k : ℤ}
    (hlower :
      n + 2 ≤
        2 * (k - 1) ^ 2)
    (hupper :
      (k + 1) ^ 2 ≤
        n + 1) :
    n ≤ sourceA k ∧
    sourceC k ≤ 2 * n := by

  unfold sourceA sourceC

  constructor <;>
    nlinarith

/-!
============================================================
10. Middle value also lies in the interval
============================================================
-/

lemma source_middle_bounds
    {n k : ℤ}
    (hn : 0 ≤ n)
    (hk : 1 ≤ k)
    (ha :
      n ≤ sourceA k)
    (hc :
      sourceC k ≤ 2 * n) :
    n ≤ sourceB k ∧
    sourceB k ≤ 2 * n := by

  have hab :
      sourceA k < sourceB k :=
    sourceA_lt_sourceB hk

  have hbc :
      sourceB k < sourceC k :=
    sourceB_lt_sourceC hk

  constructor

  · exact
      le_trans
        ha
        (le_of_lt hab)

  · exact
      le_trans
        (le_of_lt hbc)
        hc

end IMO2021P1
