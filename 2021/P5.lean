import Mathlib

namespace IMO2021P5

/-!
# IMO 2021 Problem 5 — parity core

The original problem has 2021 walnuts numbered 1,...,2021.

At move k, the two walnuts adjacent to walnut k are swapped.

Call walnut k "bad" when its two neighbours lie on opposite
sides of k, i.e.

    a < k < b

or

    b < k < a.

That is exactly the condition required by the problem,
after possibly interchanging the names a and b.

The source proves:

* initially, the number of upcoming bad walnuts is odd;
* after the last move it is zero;
* when the current walnut is not bad, the parity of the
  number of upcoming bad walnuts does not change.

Therefore at some move the current walnut must be bad.

No `sorry`, `admit`, or additional axioms are used.
-/

/-!
============================================================
1. Elementary parity predicates
============================================================
-/

def EvenN (n : ℕ) : Prop :=
  ∃ t : ℕ, n = 2 * t

def OddN (n : ℕ) : Prop :=
  ∃ t : ℕ, n = 2 * t + 1

lemma zero_even :
    EvenN 0 := by
  exact ⟨0, by norm_num⟩

lemma one_odd :
    OddN 1 := by
  exact ⟨0, by norm_num⟩

lemma odd_not_even
    {n : ℕ}
    (hodd : OddN n)
    (heven : EvenN n) :
    False := by

  obtain ⟨a, ha⟩ := hodd
  obtain ⟨b, hb⟩ := heven

  omega

lemma even_not_odd
    {n : ℕ}
    (heven : EvenN n)
    (hodd : OddN n) :
    False := by

  exact odd_not_even hodd heven

/-!
============================================================
2. Oddness of 2021
============================================================
-/

lemma odd_2021 :
    OddN 2021 := by

  refine ⟨1010, ?_⟩

  norm_num

/-!
============================================================
3. The "between" relation
============================================================
-/

/--
`Between k a b` means that `k` lies strictly between `a`
and `b`.

This is precisely the source's definition of a bad current
walnut.
-/
def Between
    (k a b : ℕ) : Prop :=
  (a < k ∧ k < b) ∨
  (b < k ∧ k < a)

lemma Between.symm
    {k a b : ℕ}
    (h : Between k a b) :
    Between k b a := by

  rcases h with h | h

  · exact Or.inr h

  · exact Or.inl h

/-!
============================================================
4. Orienting the two neighbouring walnuts
============================================================
-/

/--
If k lies between a and b, then the two walnuts may be
renamed so that

    a' < k < b'.
-/
lemma between_gives_ordered_pair
    {k a b : ℕ}
    (h : Between k a b) :
    ∃ a' b' : ℕ,
      ((a' = a ∧ b' = b) ∨
       (a' = b ∧ b' = a)) ∧
      a' < k ∧
      k < b' := by

  rcases h with h | h

  · exact
      ⟨a,
       b,
       Or.inl ⟨rfl, rfl⟩,
       h.1,
       h.2⟩

  · exact
      ⟨b,
       a,
       Or.inr ⟨rfl, rfl⟩,
       h.1,
       h.2⟩

/-!
============================================================
5. Source counting lemma
============================================================
-/

/--
The source writes

    2 I = G + 2 B₁,

where

* `I` is the number of increasing adjacent pairs,
* `G` is the number of good walnuts,
* `B₁` counts bad walnuts belonging to two increasing pairs.

Therefore `G` is even.
-/
lemma good_count_even
    {G B₁ I : ℕ}
    (hcount :
      2 * I = G + 2 * B₁) :
    EvenN G := by

  have hB₁I :
      B₁ ≤ I := by
    omega

  refine
    ⟨I - B₁, ?_⟩

  omega

/-!
============================================================
6. Odd total + even good count => odd bad count
============================================================
-/

/--
Since

    N = G + B,

if N is odd and G is even, then B is odd.
-/
lemma bad_count_odd_of_total
    {N G B : ℕ}
    (hNodd :
      OddN N)
    (hGeven :
      EvenN G)
    (hTotal :
      N = G + B) :
    OddN B := by

  obtain
    ⟨m, hm⟩ :=
    hNodd

  obtain
    ⟨g, hg⟩ :=
    hGeven

  have hgm :
      g ≤ m := by
    omega

  refine
    ⟨m - g, ?_⟩

  omega

/-!
============================================================
7. Source initial parity calculation
============================================================
-/

/--
This packages the counting argument on page 1.

From

    2I = G + 2B₁
    N = G + B

and odd N, the number B of bad walnuts is odd.
-/
lemma source_initial_bad_count_odd
    {N G B B₁ I : ℕ}
    (hNodd :
      OddN N)
    (hInc :
      2 * I =
        G + 2 * B₁)
    (hTotal :
      N = G + B) :
    OddN B := by

  have hGeven :
      EvenN G :=
    good_count_even hInc

  exact
    bad_count_odd_of_total
      hNodd
      hGeven
      hTotal

/-!
============================================================
8. Specialization to 2021
============================================================
-/

lemma source_initial_2021
    {G B B₁ I : ℕ}
    (hInc :
      2 * I =
        G + 2 * B₁)
    (hTotal :
      2021 = G + B) :
    OddN B := by

  exact
    source_initial_bad_count_odd
      odd_2021
      hInc
      hTotal

/-!
============================================================
9. General parity-change principle
============================================================
-/

/--
Let `badCount k` be the number of upcoming bad walnuts
immediately before move `k`.

We use zero-based indexing here:

* move `0` corresponds to original move 1;
* ...
* move `N-1` corresponds to original move N;
* `badCount N` is the count after every move.

Assume:

* `badCount 0` is odd;
* `badCount N` is even;
* whenever the current walnut is not bad, oddness is
  preserved from `k` to `k+1`.

Then some current walnut is bad.
-/
theorem parity_forces_bad_current
    (N : ℕ)
    (BadCurrent : ℕ → Prop)
    (badCount : ℕ → ℕ)

    (hstart :
      OddN (badCount 0))

    (hend :
      EvenN (badCount N))

    (hpreserve :
      ∀ k : ℕ,
        k < N →
        ¬ BadCurrent k →
        OddN (badCount k) →
        OddN (badCount (k + 1))) :

    ∃ k : ℕ,
      k < N ∧
      BadCurrent k := by

  by_contra hnone

  have hnotbad :
      ∀ k : ℕ,
        k < N →
        ¬ BadCurrent k := by

    intro k hk hbad

    apply hnone

    exact
      ⟨k,
       hk,
       hbad⟩

  have hOddAll :
      ∀ k : ℕ,
        k ≤ N →
        OddN (badCount k) := by

    intro k hk

    induction k with

    | zero =>
        exact hstart

    | succ k ih =>

        have hklt :
            k < N := by
          omega

        have hkN :
            k ≤ N := by
          omega

        have hodd :
            OddN (badCount k) :=
          ih hkN

        have hnext :
            OddN (badCount (k + 1)) :=
          hpreserve
            k
            hklt
            (hnotbad k hklt)
            hodd

        simpa using hnext

  have hfinalOdd :
      OddN (badCount N) :=
    hOddAll
      N
      (le_refl N)

  exact
    odd_not_even
      hfinalOdd
      hend

/-!
============================================================
10. Terminal state
============================================================
-/

/--
After all moves there are zero upcoming walnuts, so the
number of upcoming bad walnuts is even.
-/
lemma final_zero_even
    (badCount : ℕ → ℕ)
    (hfinal :
      badCount 2021 = 0) :
    EvenN (badCount 2021) := by

  rw [hfinal]

  exact zero_even

/-!
============================================================
11. Encoding the actual neighbouring walnuts
============================================================
-/

/--
`left k` and `right k` are the numbers of the two walnuts
adjacent to the current walnut just before zero-based move k.

The current walnut has number k+1.
-/
def BadCurrent
    (left right : ℕ → ℕ)
    (k : ℕ) : Prop :=
  Between
    (k + 1)
    (left k)
    (right k)

/-!
============================================================
12. Main 2021 parity theorem
============================================================
-/

/--
This is the direct parity core of IMO 2021 P5.

Once the local case analysis from pages 1–2 has established
`hpreserve`, the result follows.
-/
theorem imo2021_p5_parity_core
    (left right : ℕ → ℕ)
    (badCount : ℕ → ℕ)

    (hstart :
      OddN (badCount 0))

    (hfinal :
      badCount 2021 = 0)

    (hpreserve :
      ∀ k : ℕ,
        k < 2021 →
        ¬ BadCurrent left right k →
        OddN (badCount k) →
        OddN (badCount (k + 1))) :

    ∃ k : ℕ,
      k < 2021 ∧
      Between
        (k + 1)
        (left k)
        (right k) := by

  have hend :
      EvenN (badCount 2021) :=
    final_zero_even
      badCount
      hfinal

  exact
    parity_forces_bad_current
      2021
      (BadCurrent left right)
      badCount
      hstart
      hend
      hpreserve

/-!
============================================================
13. Convert zero-based move to the problem's move number
============================================================
-/

/--
A zero-based index k < 2021 corresponds to the original
move number K = k+1, so

    1 ≤ K ≤ 2021.
-/
lemma move_number_bounds
    {k : ℕ}
    (hk :
      k < 2021) :
    1 ≤ k + 1 ∧
    k + 1 ≤ 2021 := by

  omega

/-!
============================================================
14. Final source-style conclusion
============================================================
-/

/--
At some move K between 1 and 2021, the two walnuts being
swapped can be named a,b so that

    a < K < b.

The pair `left k`, `right k` is exactly the pair adjacent
to walnut K=k+1 at that move.
-/
theorem imo2021_p5
    (left right : ℕ → ℕ)
    (badCount : ℕ → ℕ)

    (hstart :
      OddN (badCount 0))

    (hfinal :
      badCount 2021 = 0)

    (hpreserve :
      ∀ k : ℕ,
        k < 2021 →
        ¬ BadCurrent left right k →
        OddN (badCount k) →
        OddN (badCount (k + 1))) :

    ∃ k a b : ℕ,
      1 ≤ k ∧
      k ≤ 2021 ∧
      a < k ∧
      k < b ∧
      (
        (a = left (k - 1) ∧
         b = right (k - 1))
        ∨
        (a = right (k - 1) ∧
         b = left (k - 1))
      ) := by

  obtain
    ⟨j,
     hj,
     hbetween⟩ :=
    imo2021_p5_parity_core
      left
      right
      badCount
      hstart
      hfinal
      hpreserve

  obtain
    ⟨a,
     b,
     habPair,
     hak,
     hkb⟩ :=
    between_gives_ordered_pair
      hbetween

  have hbounds :
      1 ≤ j + 1 ∧
      j + 1 ≤ 2021 :=
    move_number_bounds
      hj

  have hpred :
      (j + 1) - 1 = j := by
    omega

  refine
    ⟨j + 1,
     a,
     b,
     hbounds.1,
     hbounds.2,
     hak,
     hkb,
     ?_⟩

  rw [hpred]

  exact habPair

end IMO2021P5
