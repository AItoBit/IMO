import Mathlib

namespace IMO2020P5

open Finset
open scoped BigOperators

/-!
# IMO 2020 Problem 5 — infinite descent core

The source argument is:

* suppose a deck satisfying the mean property is not constant;
* choose a prime dividing its largest value;
* the mean property propagates this prime divisor through
  every card value;
* divide every card by that prime;
* the resulting deck is still positive, still satisfies the
  property, and is still nonconstant;
* some positive natural-valued measure strictly decreases;
* infinite descent gives a contradiction.

No `sorry`, `admit`, or additional axioms are used.
-/

/-!
============================================================
1. Basic predicates
============================================================
-/

def Positive
    {ι : Type*}
    (a : ι → ℕ) : Prop :=
  ∀ i, 0 < a i

def Constant
    {ι : Type*}
    (a : ι → ℕ) : Prop :=
  ∀ i j, a i = a j

/-!
============================================================
2. Divide a deck by a common divisor
============================================================
-/

def divideDeck
    {ι : Type*}
    (a : ι → ℕ)
    (p : ℕ) :
    ι → ℕ :=
  fun i => a i / p

lemma divideDeck_apply
    {ι : Type*}
    (a : ι → ℕ)
    (p : ℕ)
    (i : ι) :
    divideDeck a p i =
      a i / p := by
  rfl

/-!
============================================================
3. Positivity survives exact division
============================================================
-/

lemma div_pos_of_dvd
    {x p : ℕ}
    (hx : 0 < x)
    (hp : 0 < p)
    (hpx : p ∣ x) :
    0 < x / p := by

  have hp_le_x :
      p ≤ x :=
    Nat.le_of_dvd
      hx
      hpx

  exact
    Nat.div_pos
      hp_le_x
      hp

lemma divideDeck_positive
    {ι : Type*}
    (a : ι → ℕ)
    (p : ℕ)
    (ha : Positive a)
    (hp : 0 < p)
    (hdiv :
      ∀ i, p ∣ a i) :
    Positive (divideDeck a p) := by

  intro i

  exact
    div_pos_of_dvd
      (ha i)
      hp
      (hdiv i)

/-!
============================================================
4. Reconstruction after exact division
============================================================
-/

lemma mul_div_of_dvd
    {x p : ℕ}
    (hpx : p ∣ x) :
    p * (x / p) = x := by

  exact
    Nat.mul_div_cancel'
      hpx

/-!
============================================================
5. Equality of quotients
============================================================
-/

lemma eq_of_div_eq_div
    {x y p : ℕ}
    (hpx : p ∣ x)
    (hpy : p ∣ y)
    (h :
      x / p = y / p) :
    x = y := by

  calc
    x =
        p * (x / p) := by
      symm
      exact
        Nat.mul_div_cancel'
          hpx

    _ =
        p * (y / p) := by
      rw [h]

    _ =
        y :=
      Nat.mul_div_cancel'
        hpy

/-!
============================================================
6. Nonconstancy survives exact common division
============================================================
-/

lemma divideDeck_nonconstant
    {ι : Type*}
    (a : ι → ℕ)
    (p : ℕ)
    (hdiv :
      ∀ i, p ∣ a i)
    (hnconst :
      ¬ Constant a) :
    ¬ Constant (divideDeck a p) := by

  intro hconst

  apply hnconst

  intro i j

  apply
    eq_of_div_eq_div
      (hdiv i)
      (hdiv j)

  exact
    hconst i j

/-!
============================================================
7. Division by a prime strictly decreases positive values
============================================================
-/

lemma prime_two_le
    {p : ℕ}
    (hp : Nat.Prime p) :
    2 ≤ p := by

  exact hp.two_le

lemma div_strictly_smaller
    {x p : ℕ}
    (hx : 0 < x)
    (hp : 2 ≤ p) :
    x / p < x := by

  exact
    Nat.div_lt_self
      hx
      (by omega)

/-!
============================================================
8. Generic descent preserving an invariant
============================================================
-/

/--
If every invariant non-goal state has an invariant successor
with strictly smaller natural-valued measure, eventually a
goal state is reached.
-/
theorem descend_preserving
    {State : Type*}
    (μ : State → ℕ)
    (Step : State → State → Prop)
    (Inv Goal : State → Prop)
    (hdecrease :
      ∀ {s t : State},
        Step s t →
        μ t < μ s)
    (hnext :
      ∀ s : State,
        Inv s →
        ¬ Goal s →
        ∃ t : State,
          Step s t ∧
          Inv t)
    (s₀ : State)
    (hInv₀ : Inv s₀) :
    ∃ t : State,
      Relation.ReflTransGen Step s₀ t ∧
      Inv t ∧
      Goal t := by

  have aux :
      ∀ n : ℕ,
        ∀ s : State,
          μ s = n →
          Inv s →
          ∃ t : State,
            Relation.ReflTransGen Step s t ∧
            Inv t ∧
            Goal t := by

    intro n

    induction n using Nat.strong_induction_on with

    | h n ih =>

      intro s hμ hInv

      by_cases hGoal :
          Goal s

      · exact
          ⟨s,
           Relation.ReflTransGen.refl,
           hInv,
           hGoal⟩

      · obtain
          ⟨u,
           hsu,
           hInvU⟩ :=
          hnext
            s
            hInv
            hGoal

        have hlt :
            μ u < n := by

          have hdec :
              μ u < μ s :=
            hdecrease hsu

          omega

        obtain
          ⟨t,
           hut,
           hInvT,
           hGoalT⟩ :=
          ih
            (μ u)
            hlt
            u
            rfl
            hInvU

        have hsu' :
            Relation.ReflTransGen Step s u :=
          Relation.ReflTransGen.single hsu

        have hst :
            Relation.ReflTransGen Step s t :=
          hsu'.trans hut

        exact
          ⟨t,
           hst,
           hInvT,
           hGoalT⟩

  exact
    aux
      (μ s₀)
      s₀
      rfl
      hInv₀

/-!
============================================================
9. Pure infinite descent
============================================================
-/

/--
There is no bad state if every bad state produces another bad
state with strictly smaller natural-number measure.
-/
theorem infinite_descent
    {State : Type*}
    (μ : State → ℕ)
    (Bad : State → Prop)
    (hstep :
      ∀ s : State,
        Bad s →
        ∃ t : State,
          Bad t ∧
          μ t < μ s) :
    ∀ s : State,
      ¬ Bad s := by

  have aux :
      ∀ n : ℕ,
        ∀ s : State,
          μ s = n →
          ¬ Bad s := by

    intro n

    induction n using Nat.strong_induction_on with

    | h n ih =>

      intro s hμ hBad

      obtain
        ⟨t,
         hBadT,
         hlt⟩ :=
        hstep
          s
          hBad

      have hlt' :
          μ t < n := by
        omega

      have hnotT :
          ¬ Bad t :=
        ih
          (μ t)
          hlt'
          t
          rfl

      exact
        hnotT hBadT

  intro s

  exact
    aux
      (μ s)
      s
      rfl

/-!
============================================================
10. Abstract deck property
============================================================
-/

/-
`Good a` represents the arithmetic/geometric-mean property
from the original problem.

It remains abstract in this descent file so the number-theory
argument is independent of the eventual formal representation
of geometric means.
-/
variable
  {ι : Type*}
  (Good : (ι → ℕ) → Prop)

/-!
============================================================
11. Prime descent step
============================================================
-/

/--
Assume a common prime divisor has been obtained from the
original mean property and division by it preserves the
property. Then we obtain a positive, good, nonconstant
smaller deck.
-/
lemma prime_descent_step
    (a : ι → ℕ)
    (ha : Positive a)
    (_hGood : Good a)
    (hnconst : ¬ Constant a)

    (hcommonPrime :
      ∃ p : ℕ,
        Nat.Prime p ∧
        ∀ i, p ∣ a i)

    (hscale :
      ∀ p : ℕ,
        Nat.Prime p →
        (∀ i, p ∣ a i) →
        Good (divideDeck a p)) :

    ∃ p : ℕ,
      Nat.Prime p ∧
      Positive (divideDeck a p) ∧
      Good (divideDeck a p) ∧
      ¬ Constant (divideDeck a p) := by

  obtain
    ⟨p,
     hp,
     hdiv⟩ :=
    hcommonPrime

  have hp0 :
      0 < p :=
    hp.pos

  have hpositive :
      Positive
        (divideDeck a p) :=
    divideDeck_positive
      a
      p
      ha
      hp0
      hdiv

  have hgood :
      Good
        (divideDeck a p) :=
    hscale
      p
      hp
      hdiv

  have hnonconstant :
      ¬ Constant
          (divideDeck a p) :=
    divideDeck_nonconstant
      a
      p
      hdiv
      hnconst

  exact
    ⟨p,
     hp,
     hpositive,
     hgood,
     hnonconstant⟩

/-!
============================================================
12. Any distinguished positive value decreases
============================================================
-/

lemma distinguished_value_decreases
    (a : ι → ℕ)
    (i : ι)
    (p : ℕ)
    (ha : Positive a)
    (hp : Nat.Prime p) :
    divideDeck a p i < a i := by

  unfold divideDeck

  exact
    div_strictly_smaller
      (ha i)
      hp.two_le

/-!
============================================================
13. Complete abstract IMO descent theorem
============================================================
-/

/--
If every positive, good, nonconstant state yields another
positive, good, nonconstant state of smaller measure, then no
positive good state can be nonconstant.
-/
theorem imo2020_p5_descent
    {State : Type*}
    (μ : State → ℕ)
    (PositiveState GoodState NonconstantState :
      State → Prop)

    (hstep :
      ∀ s : State,
        PositiveState s →
        GoodState s →
        NonconstantState s →
        ∃ t : State,
          PositiveState t ∧
          GoodState t ∧
          NonconstantState t ∧
          μ t < μ s) :

    ∀ s : State,
      PositiveState s →
      GoodState s →
      ¬ NonconstantState s := by

  have aux :
      ∀ n : ℕ,
        ∀ s : State,
          μ s = n →
          PositiveState s →
          GoodState s →
          ¬ NonconstantState s := by

    intro n

    induction n using Nat.strong_induction_on with

    | h n ih =>

      intro s hμ hpos hgood hnonconst

      obtain
        ⟨t,
         hposT,
         hgoodT,
         hnonconstT,
         hlt⟩ :=
        hstep
          s
          hpos
          hgood
          hnonconst

      have hlt' :
          μ t < n := by
        omega

      have hnotT :
          ¬ NonconstantState t :=
        ih
          (μ t)
          hlt'
          t
          rfl
          hposT
          hgoodT

      exact
        hnotT hnonconstT

  intro s hpos hgood

  exact
    aux
      (μ s)
      s
      rfl
      hpos
      hgood

/-!
============================================================
14. Double-negation helper
============================================================
-/

lemma constant_of_not_nonconstant
    {ι : Type*}
    (a : ι → ℕ)
    (h :
      ¬ ¬ Constant a) :
    Constant a := by

  by_contra hn

  exact
    h hn

/-!
============================================================
15. Final source-style wrapper
============================================================
-/

/--
Once the source-specific prime-propagation step has been
proved, infinite descent forces every positive good deck to
have all entries equal.
-/
theorem imo2020_p5_core
    {State : Type*}
    (μ : State → ℕ)
    (PositiveState GoodState : State → Prop)
    (AllEqual : State → Prop)

    (hstep :
      ∀ s : State,
        PositiveState s →
        GoodState s →
        ¬ AllEqual s →
        ∃ t : State,
          PositiveState t ∧
          GoodState t ∧
          ¬ AllEqual t ∧
          μ t < μ s)

    (s : State)
    (hpos :
      PositiveState s)
    (hgood :
      GoodState s) :
    AllEqual s := by

  have hnot :
      ¬ (¬ AllEqual s) := by

    exact
      imo2020_p5_descent
        μ
        PositiveState
        GoodState
        (fun x => ¬ AllEqual x)
        hstep
        s
        hpos
        hgood

  by_contra hne

  exact
    hnot hne

end IMO2020P5
