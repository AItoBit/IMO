import Mathlib

namespace IMO2026P1

/-!
# IMO 2026 Problem 1 — termination and invariance core

A board contains exactly 2026 positive integers.

The source proof uses two central ideas:

1. a natural-valued quantity strictly decreases under every move,
   proving termination;

2. a prime-by-prime invariant is preserved by every move and,
   at a terminal state, determines the unique remaining integer
   greater than 1.

No `sorry`, `admit`, or additional axioms are used.
-/

/-!
============================================================
1. Boards
============================================================
-/

abbrev Board :=
  Fin 2026 → ℕ

def PositiveBoard
    (b : Board) : Prop :=
  ∀ i : Fin 2026,
    1 ≤ b i

def HasLarge
    (b : Board) : Prop :=
  ∃ i : Fin 2026,
    1 < b i

def HasTwoLarge
    (b : Board) : Prop :=
  ∃ i j : Fin 2026,
    i ≠ j ∧
    1 < b i ∧
    1 < b j

def Stopped
    (b : Board) : Prop :=
  ¬ HasTwoLarge b

def ExactlyOneLarge
    (b : Board)
    (M : ℕ) : Prop :=
  1 < M ∧
  ∃ i : Fin 2026,
    b i = M ∧
    ∀ j : Fin 2026,
      j ≠ i →
      b j = 1

/-!
============================================================
2. Finite reachability
============================================================
-/

inductive Reach
    (Step : Board → Board → Prop) :
    Board → Board → Prop

  | refl
      (b : Board) :
      Reach Step b b

  | tail
      {a b c : Board} :
      Reach Step a b →
      Step b c →
      Reach Step a c

/-!
============================================================
3. Predicates preserved by reachability
============================================================
-/

lemma reach_preserves
    {Step : Board → Board → Prop}
    {P : Board → Prop}
    (hstep :
      ∀ {a b : Board},
        Step a b →
        P a →
        P b)
    {a b : Board}
    (hab :
      Reach Step a b)
    (ha :
      P a) :
    P b := by

  induction hab with

  | refl =>
      exact ha

  | tail hab hbc ih =>
      exact
        hstep
          hbc
          ih

/-!
============================================================
4. Numerical invariants preserved by reachability
============================================================
-/

lemma reach_preserves_value
    {Step : Board → Board → Prop}
    (inv : Board → ℕ)
    (hstep :
      ∀ {a b : Board},
        Step a b →
        inv a = inv b)
    {a b : Board}
    (hab :
      Reach Step a b) :
    inv a = inv b := by

  induction hab with

  | refl =>
      rfl

  | tail hab hbc ih =>
      calc
        _ = _ := ih
        _ = _ := hstep hbc

/-!
============================================================
5. Infinite runs
============================================================
-/

def InfiniteRunFrom
    (Step : Board → Board → Prop)
    (start : Board) : Prop :=
  ∃ f : ℕ → Board,
    f 0 = start ∧
    ∀ n : ℕ,
      Step (f n) (f (n + 1))

/-!
============================================================
6. Strict natural descent forbids infinite runs
============================================================
-/

theorem no_infinite_run_of_measure
    (Step : Board → Board → Prop)
    (measure : Board → ℕ)
    (hdecrease :
      ∀ {a b : Board},
        Step a b →
        measure b < measure a)
    (start : Board) :
    ¬ InfiniteRunFrom Step start := by

  intro hinfinite

  rcases hinfinite with
    ⟨f, hf0, hfstep⟩

  have hdrop :
      ∀ n : ℕ,
        measure (f n) + n ≤
          measure (f 0) := by

    intro n

    induction n with

    | zero =>
        simp

    | succ n ih =>

        have hlt :
            measure (f (n + 1)) <
              measure (f n) :=
          hdecrease
            (hfstep n)

        omega

  have hbad :=
    hdrop
      (measure (f 0) + 1)

  omega

/-!
============================================================
7. Terminal positive board has exactly one large entry
============================================================
-/

theorem exactly_one_large_of_stopped
    {b : Board}
    (hpos :
      PositiveBoard b)
    (hlarge :
      HasLarge b)
    (hstop :
      Stopped b) :
    ∃ M : ℕ,
      ExactlyOneLarge b M := by

  rcases hlarge with
    ⟨i, hi⟩

  refine
    ⟨b i,
     hi,
     i,
     rfl,
     ?_⟩

  intro j hji

  have hjpos :
      1 ≤ b j :=
    hpos j

  have hjnot :
      ¬ 1 < b j := by

    intro hj

    apply hstop

    exact
      ⟨i,
       j,
       hji.symm,
       hi,
       hj⟩

  omega

/-!
============================================================
8. Initial-board facts
============================================================
-/

lemma initial_positive
    {b : Board}
    (h :
      ∀ i : Fin 2026,
        1 < b i) :
    PositiveBoard b := by

  intro i

  exact
    Nat.le_of_lt
      (h i)

lemma initial_has_large
    {b : Board}
    (h :
      ∀ i : Fin 2026,
        1 < b i) :
    HasLarge b := by

  exact
    ⟨0, h 0⟩

/-!
============================================================
9. Move-specific source facts
============================================================
-/

/-
For the concrete gcd/lcm operation, the mathematical proof
must provide these facts.

`measure_decrease` gives termination.

`signature_step` is the prime-exponent invariant described in
the source.

`terminal_signature` identifies the invariant with the unique
remaining M at a terminal state.
-/

structure SourceFacts
    (Step : Board → Board → Prop)
    (measure : Board → ℕ)
    (signature : Board → ℕ) : Prop where

  positive_step :
    ∀ {a b : Board},
      Step a b →
      PositiveBoard a →
      PositiveBoard b

  large_step :
    ∀ {a b : Board},
      Step a b →
      HasLarge a →
      HasLarge b

  measure_decrease :
    ∀ {a b : Board},
      Step a b →
      measure b < measure a

  signature_step :
    ∀ {a b : Board},
      Step a b →
      signature a = signature b

  terminal_signature :
    ∀ {b : Board}
      {M : ℕ},
      ExactlyOneLarge b M →
      signature b = M

/-!
============================================================
10. Reachable stopped boards have one survivor
============================================================
-/

theorem terminal_shape
    {Step : Board → Board → Prop}
    {measure signature : Board → ℕ}
    (F :
      SourceFacts
        Step
        measure
        signature)
    {initial final : Board}
    (hinit :
      ∀ i : Fin 2026,
        1 < initial i)
    (hreach :
      Reach Step initial final)
    (hstop :
      Stopped final) :
    ∃ M : ℕ,
      ExactlyOneLarge final M := by

  have hpos0 :
      PositiveBoard initial :=
    initial_positive
      hinit

  have hlarge0 :
      HasLarge initial :=
    initial_has_large
      hinit

  have hpos :
      PositiveBoard final := by

    exact
      reach_preserves
        (Step := Step)
        (P := PositiveBoard)
        (fun {a b} hab hpa =>
          F.positive_step hab hpa)
        hreach
        hpos0

  have hlarge :
      HasLarge final := by

    exact
      reach_preserves
        (Step := Step)
        (P := HasLarge)
        (fun {a b} hab hla =>
          F.large_step hab hla)
        hreach
        hlarge0

  exact
    exactly_one_large_of_stopped
      hpos
      hlarge
      hstop

/-!
============================================================
11. Final value is invariant
============================================================
-/

theorem final_value_unique
    {Step : Board → Board → Prop}
    {measure signature : Board → ℕ}
    (F :
      SourceFacts
        Step
        measure
        signature)
    {initial final₁ final₂ : Board}
    {M₁ M₂ : ℕ}
    (hreach₁ :
      Reach Step initial final₁)
    (hreach₂ :
      Reach Step initial final₂)
    (hfinal₁ :
      ExactlyOneLarge final₁ M₁)
    (hfinal₂ :
      ExactlyOneLarge final₂ M₂) :
    M₁ = M₂ := by

  have hinv₁ :
      signature initial =
        signature final₁ := by

    exact
      reach_preserves_value
        (Step := Step)
        signature
        F.signature_step
        hreach₁

  have hinv₂ :
      signature initial =
        signature final₂ := by

    exact
      reach_preserves_value
        (Step := Step)
        signature
        F.signature_step
        hreach₂

  have hsig₁ :
      signature final₁ = M₁ :=
    F.terminal_signature
      hfinal₁

  have hsig₂ :
      signature final₂ = M₂ :=
    F.terminal_signature
      hfinal₂

  calc
    M₁ =
        signature final₁ :=
      hsig₁.symm

    _ =
        signature initial :=
      hinv₁.symm

    _ =
        signature final₂ :=
      hinv₂

    _ =
        M₂ :=
      hsig₂

/-!
============================================================
12. Every play is finite
============================================================
-/

theorem every_play_is_finite
    {Step : Board → Board → Prop}
    {measure signature : Board → ℕ}
    (F :
      SourceFacts
        Step
        measure
        signature)
    (initial : Board) :
    ¬ InfiniteRunFrom
        Step
        initial := by

  exact
    no_infinite_run_of_measure
      Step
      measure
      F.measure_decrease
      initial

/-!
============================================================
13. Complete proof core
============================================================
-/

theorem imo2026_p1_core
    {Step : Board → Board → Prop}
    {measure signature : Board → ℕ}
    (F :
      SourceFacts
        Step
        measure
        signature)
    (initial : Board)
    (hinit :
      ∀ i : Fin 2026,
        1 < initial i) :

    (¬ InfiniteRunFrom Step initial)
    ∧
    (
      ∀ final : Board,
        Reach Step initial final →
        Stopped final →
        ∃ M : ℕ,
          ExactlyOneLarge final M
    )
    ∧
    (
      ∀ final₁ final₂ : Board,
        ∀ M₁ M₂ : ℕ,
          Reach Step initial final₁ →
          Reach Step initial final₂ →
          ExactlyOneLarge final₁ M₁ →
          ExactlyOneLarge final₂ M₂ →
          M₁ = M₂
    ) := by

  constructor

  · exact
      every_play_is_finite
        F
        initial

  constructor

  · intro final hreach hstop

    exact
      terminal_shape
        F
        hinit
        hreach
        hstop

  · intro final₁ final₂ M₁ M₂ hreach₁ hreach₂ hfinal₁ hfinal₂

    exact
      final_value_unique
        F
        hreach₁
        hreach₂
        hfinal₁
        hfinal₂

end IMO2026P1
