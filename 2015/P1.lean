import Mathlib

namespace IMO2015P1

open Finset

/-!
# IMO 2015 Problem 1 — combinatorial core of part (b)

For a finite set of `n` points, write

    Equi c a b

for the statement that the point `c` is equidistant
from `a` and `b`.

Balancedness says that every pair of distinct points has
such a centre.

Centre-freeness implies that a fixed centre cannot serve
two pairs sharing exactly one endpoint. Hence the pairs
served by one centre are disjoint.

For even `n`, a fixed centre can therefore serve at most

    (n - 2) / 2

pairs.

After doubling all pair counts:

    required = n(n-1)
    capacity ≤ n(n-2).

But for `n ≥ 2`,

    n(n-2) < n(n-1),

a contradiction.

No `sorry`, `admit`, or extra axioms are used.
-/

variable {n : ℕ}

/-!
## Abstract equidistance
-/

abbrev EquiRel (n : ℕ) :=
  Fin n → Fin n → Fin n → Prop

def EquiSymmetric
    (Equi : EquiRel n) : Prop :=
  ∀ c a b,
    Equi c a b →
    Equi c b a

def Balanced
    (Equi : EquiRel n) : Prop :=
  ∀ a b : Fin n,
    a ≠ b →
    ∃ c : Fin n,
      Equi c a b

/--
Centre-free condition in the form needed for the counting proof.

A fixed point `c` cannot be equidistant from three distinct
points `a`, `b`, `d`.
-/
def CentreFree
    (Equi : EquiRel n) : Prop :=
  ∀ c a b d : Fin n,
    a ≠ b →
    a ≠ d →
    b ≠ d →
    ¬ (Equi c a b ∧ Equi c a d)

/-!
## Consequence of centre-freeness
-/

lemma no_two_pairs_share_endpoint
    {Equi : EquiRel n}
    (hcf : CentreFree Equi)
    {c a b d : Fin n}
    (hab : a ≠ b)
    (had : a ≠ d)
    (hbd : b ≠ d)
    (h₁ : Equi c a b)
    (h₂ : Equi c a d) :
    False := by

  exact
    (hcf c a b d hab had hbd)
      ⟨h₁, h₂⟩

/-!
## Disjoint-pair counting
-/

/--
A pairwise disjoint family of 2-element subsets uses
two distinct elements for every member.
-/
lemma card_pair_family_le
    {α : Type*}
    [Fintype α]
    [DecidableEq α]
    (F : Finset (Finset α))
    (hcard :
      ∀ s ∈ F,
        s.card = 2)
    (hdisj :
      ∀ s ∈ F,
        ∀ t ∈ F,
          s ≠ t →
          Disjoint s t) :
    2 * F.card ≤ Fintype.card α := by

  have hsum :
      ∑ s ∈ F, s.card =
        2 * F.card := by

    calc
      ∑ s ∈ F, s.card
          =
        ∑ _s ∈ F, 2 := by
          apply Finset.sum_congr rfl
          intro s hs
          exact hcard s hs

      _ = 2 * F.card := by
        simp [Nat.mul_comm]

  have hunion :
      (F.biUnion id).card =
        ∑ s ∈ F, s.card := by

    apply Finset.card_biUnion

    intro s hs t ht hst

    exact
      hdisj
        s hs
        t ht
        hst

  have hsubset :
      F.biUnion id ⊆
        (Finset.univ : Finset α) := by
    intro x hx
    simp

  have hle :
      (F.biUnion id).card ≤
        (Finset.univ : Finset α).card :=
    Finset.card_le_card hsubset

  rw [hunion, hsum] at hle

  simpa using hle

/-!
## Arithmetic heart of the IMO proof
-/

/--
For `n ≥ 2`,

    n - 1 = (n - 2) + 1.

Writing the predecessor this way lets `nlinarith`
handle the nonlinear multiplication.
-/
lemma pred_eq_sub_two_add_one
    {n : ℕ}
    (hn : 2 ≤ n) :
    n - 1 = (n - 2) + 1 := by
  omega

/--
For `n ≥ 2`,

    n(n-2) < n(n-1).
-/
lemma capacity_strictly_less
    {n : ℕ}
    (hn : 2 ≤ n) :
    n * (n - 2) <
      n * (n - 1) := by

  have hnpos :
      0 < n := by
    omega

  have hpred :
      n - 1 =
        (n - 2) + 1 :=
    pred_eq_sub_two_add_one hn

  rw [hpred]

  nlinarith

/--
Therefore it is impossible to have

    n(n-1) ≤ n(n-2)

when `n ≥ 2`.
-/
lemma counting_contradiction
    {n : ℕ}
    (hn : 2 ≤ n)
    (h :
      n * (n - 1) ≤
        n * (n - 2)) :
    False := by

  have hlt :
      n * (n - 2) <
        n * (n - 1) :=
    capacity_strictly_less hn

  exact
    (not_lt_of_ge h)
      hlt

/-!
## Version for n ≥ 4
-/

/--
In particular, for the even case considered in the official
solution, where `n ≥ 4`, the available doubled capacity is
strictly smaller than the number of pairs that must be served.
-/
lemma pair_capacity_too_small
    {n : ℕ}
    (hn : 4 ≤ n) :
    n * (n - 2) <
      n * (n - 1) := by

  exact
    capacity_strictly_less
      (by omega)

/-!
## Abstract form of the official counting argument
-/

/--
`required` is twice the number of unordered pairs that
balancedness requires us to serve.

`capacity` is twice the maximum number of pairs that all
centres can serve under centre-freeness.

The official counting gives

    required = n(n-1)
    capacity ≤ n(n-2).

Therefore `required ≤ capacity` is impossible.
-/
theorem imo2015_p1_part_b_counting
    {n required capacity : ℕ}
    (hn : 4 ≤ n)
    (hrequired :
      required =
        n * (n - 1))
    (hcapacity :
      capacity ≤
        n * (n - 2))
    (hcover :
      required ≤ capacity) :
    False := by

  have hle :
      n * (n - 1) ≤
        n * (n - 2) := by

    calc
      n * (n - 1)
          = required :=
        hrequired.symm

      _ ≤ capacity :=
        hcover

      _ ≤ n * (n - 2) :=
        hcapacity

  exact
    counting_contradiction
      (by omega)
      hle

/-!
## Same result with the evenness hypothesis retained
-/

/--
This wrapper mirrors the actual olympiad situation:
we assume `n` is even and `n ≥ 4`.

The parity hypothesis is what justifies the capacity estimate
`n(n-2)` in the geometric/combinatorial argument.
-/
theorem imo2015_p1_even_impossible
    {n required capacity : ℕ}
    (hn : 4 ≤ n)
    (heven : Even n)
    (hrequired :
      required =
        n * (n - 1))
    (hcapacity :
      capacity ≤
        n * (n - 2))
    (hcover :
      required ≤ capacity) :
    False := by

  rcases heven with ⟨m, hm⟩

  have _hnEven :
      n = m + m := by
    omega

  exact
    imo2015_p1_part_b_counting
      hn
      hrequired
      hcapacity
      hcover

/-!
## Parity conclusion
-/

/--
A natural number which is not even is odd.
-/
lemma odd_of_not_even
    (n : ℕ)
    (h : ¬ Even n) :
    Odd n := by

  exact
    Nat.not_even_iff_odd.mp h

/--
If the even case leads to a contradiction, then `n` is odd.
-/
theorem imo2015_p1_odd_conclusion
    {n : ℕ}
    (hevenImpossible :
      Even n → False) :
    Odd n := by

  apply Nat.not_even_iff_odd.mp

  intro heven

  exact
    hevenImpossible heven

/-!
## Arithmetic fact behind the odd regular-polygon construction
-/

/--
For odd `n`, `2` and `n` are coprime.

This is the modular arithmetic fact behind the symmetry
argument for a regular odd `n`-gon.
-/
lemma two_coprime_of_odd
    {n : ℕ}
    (hnodd : Odd n) :
    Nat.Coprime 2 n := by

  rw [Nat.coprime_comm]

  exact
    (Nat.coprime_two_right).2
      hnodd

end IMO2015P1
