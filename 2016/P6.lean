import Mathlib

namespace IMO2016P6

/-!
# IMO 2016 Problem 6 — parity core

The geometric proof eventually reduces both parts to parity.

Part (b), n even:
-----------------
Starting from a circled endpoint B, the source alternates

    circle, cross, circle, cross, ...

around one side of the arc BB'.

There are exactly `n - 1` other blue endpoints on that side.
For the alternation to finish consistently, `n - 1` must be even.
But if `n` is even, `n - 1` is odd. Contradiction.

Part (a), n odd:
----------------
Assume two frogs collide. The source considers an arc AB and
lets `k` be the number of intermediate blue points.

Because both endpoints A and B are circled, alternation implies
that `k` is odd.

The pairing argument involving red intersection points shows
that the intermediate blue points occur in pairs, so `k` is even.

Contradiction.

No `sorry`, `admit`, or additional axioms are used.
-/

/-!
## Elementary parity incompatibility
-/

/--
A natural number cannot be both even and odd.
-/
lemma not_even_and_odd
    {k : ℕ}
    (he : Even k)
    (ho : Odd k) :
    False := by

  rcases he with ⟨a, ha⟩
  rcases ho with ⟨b, hb⟩

  omega

/--
Same result with the hypotheses reversed.
-/
lemma not_odd_and_even
    {k : ℕ}
    (ho : Odd k)
    (he : Even k) :
    False := by

  exact
    not_even_and_odd
      he
      ho

/-!
## Parity of a predecessor
-/

/--
If `n` is positive and even, then `n - 1` is odd.
-/
lemma odd_pred_of_even
    {n : ℕ}
    (hn : 0 < n)
    (heven : Even n) :
    Odd (n - 1) := by

  rcases heven with ⟨t, ht⟩

  have htpos :
      0 < t := by
    omega

  refine ⟨t - 1, ?_⟩

  omega

/--
Consequently, for positive even `n`, `n-1` cannot be even.
-/
lemma pred_not_even_of_even
    {n : ℕ}
    (hn : 0 < n)
    (heven : Even n) :
    ¬ Even (n - 1) := by

  intro hpred

  have hodd :
      Odd (n - 1) :=
    odd_pred_of_even
      hn
      heven

  exact
    not_even_and_odd
      hpred
      hodd

/-!
## Part (b): even n is impossible
-/

/--
Abstract form of the final contradiction in part (b).

The geometric alternation argument would force

    Even (n - 1).

For even positive `n`, this is impossible.
-/
theorem even_case_contradiction
    {n : ℕ}
    (hn : 2 ≤ n)
    (heven : Even n)
    (halternation :
      Even (n - 1)) :
    False := by

  exact
    pred_not_even_of_even
      (by omega)
      heven
      halternation

/--
If a successful placement would force `Even (n-1)`,
then no successful placement exists for even `n`.
-/
theorem no_success_when_even
    {n : ℕ}
    (hn : 2 ≤ n)
    (heven : Even n)
    (Successful : Prop)
    (hnecessary :
      Successful →
      Even (n - 1)) :
    ¬ Successful := by

  intro hs

  exact
    even_case_contradiction
      hn
      heven
      (hnecessary hs)

/-!
## Alternating endpoints
-/

/--
If `k+1` is even, then `k` is odd.
-/
lemma odd_of_succ_even
    {k : ℕ}
    (h : Even (k + 1)) :
    Odd k := by

  rcases h with ⟨t, ht⟩

  refine ⟨t - 1, ?_⟩

  omega

/--
Conversely, if `k` is odd then `k+1` is even.
-/
lemma succ_even_of_odd
    {k : ℕ}
    (h : Odd k) :
    Even (k + 1) := by

  rcases h with ⟨t, ht⟩

  refine ⟨t + 1, ?_⟩

  omega

/-!
## Pairing implies even cardinality
-/

/--
If a finite set is partitioned into 2-element blocks,
its cardinality is even.

This is the arithmetic form of the pairing argument in
part (a).
-/
lemma even_of_card_eq_twice
    {k r : ℕ}
    (h :
      k = 2 * r) :
    Even k := by

  refine ⟨r, ?_⟩

  omega

/--
Equivalent orientation.
-/
lemma even_of_twice_eq_card
    {k r : ℕ}
    (h :
      2 * r = k) :
    Even k := by

  exact
    even_of_card_eq_twice
      h.symm

/-!
## Part (a): hypothetical collision is impossible
-/

/--
This is the exact final parity contradiction in the source's
proof of part (a).

For a hypothetical collision:

* the alternating-circle argument says `k` is odd;
* the red-point pairing argument says `k` is even.

Therefore no such collision can occur.
-/
theorem collision_parity_contradiction
    {k : ℕ}
    (hodd :
      Odd k)
    (heven :
      Even k) :
    False := by

  exact
    not_odd_and_even
      hodd
      heven

/-!
## Version exposing the two geometric outputs
-/

/--
Suppose `Collision` is a proposition describing a particular
pair of frogs colliding, and `k` is the number of intermediate
blue endpoints on the relevant arc.

If geometry proves

    Collision → Odd k

and the pairing argument proves

    Collision → Even k,

then the collision is impossible.
-/
theorem no_collision
    {k : ℕ}
    (Collision : Prop)
    (hodd :
      Collision →
      Odd k)
    (heven :
      Collision →
      Even k) :
    ¬ Collision := by

  intro hcollision

  exact
    collision_parity_contradiction
      (hodd hcollision)
      (heven hcollision)

/-!
## Indexed collision family
-/

/--
Every candidate collision is impossible if it simultaneously
forces odd and even parity of its associated arc count.
-/
theorem no_collision_family
    {ι : Type*}
    (Collision : ι → Prop)
    (k : ι → ℕ)
    (hodd :
      ∀ i,
        Collision i →
        Odd (k i))
    (heven :
      ∀ i,
        Collision i →
        Even (k i)) :
    ∀ i,
      ¬ Collision i := by

  intro i hi

  exact
    collision_parity_contradiction
      (hodd i hi)
      (heven i hi)

/-!
## Pairing form of the odd/even contradiction
-/

/--
If alternation says that `k` is odd, while the geometric
pairing supplies an `r` with

    k = 2r,

then contradiction.
-/
theorem collision_impossible_from_pairing
    {k r : ℕ}
    (hodd :
      Odd k)
    (hpair :
      k = 2 * r) :
    False := by

  have heven :
      Even k :=
    even_of_card_eq_twice
      hpair

  exact
    collision_parity_contradiction
      hodd
      heven

/-!
## Full abstract parity package for IMO 2016 P6
-/

/--
`CanPlace` represents the existence of a frog placement
satisfying Geoff's condition.

For even `n`, if any successful placement would force
`Even (n-1)`, then no successful placement exists.
-/
theorem imo2016_p6_parity_core
    {n : ℕ}
    (hn : 2 ≤ n)
    (CanPlace : Prop)
    (hEvenNecessary :
      Even n →
      CanPlace →
      Even (n - 1)) :
    Even n →
    ¬ CanPlace := by

  intro heven

  exact
    no_success_when_even
      hn
      heven
      CanPlace
      (hEvenNecessary heven)

/-!
## Useful parity equivalence
-/

/--
For positive `n`, evenness of `n` is equivalent to oddness
of `n-1`.
-/
lemma even_iff_pred_odd
    {n : ℕ}
    (hn : 0 < n) :
    Even n ↔ Odd (n - 1) := by

  constructor

  · intro he

    exact
      odd_pred_of_even
        hn
        he

  · intro ho

    rcases ho with ⟨t, ht⟩

    refine ⟨t + 1, ?_⟩

    omega

/-!
## Final clean form of part (b)
-/

/--
If the alternating construction around the arc requires
`n-1` to be even, then `n` must be odd.
-/
theorem odd_n_of_alternating_arc
    {n : ℕ}
    (hn : 2 ≤ n)
    (h :
      Even (n - 1)) :
    Odd n := by

  by_cases he :
      Even n

  · exact
      False.elim
        (even_case_contradiction
          hn
          he
          h)

  · exact
      Nat.not_even_iff_odd.mp
        he

end IMO2016P6
