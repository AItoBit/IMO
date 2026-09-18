import Mathlib

/-!
# IMO 2010 Problem 3

Original problem:

Find all functions g : ℕ⁺ → ℕ⁺ such that

    (g(m) + n) (g(n) + m)

is a perfect square for all positive integers m,n.

We use zero-based indices for positive integers:

    Lean index n  ↔  olympiad integer n+1.

Thus the condition becomes

    (g m + (n+1)) * (g n + (m+1))

is a square.

The answer in these coordinates is

    g n = n + 1 + k.

The source proof has a hard number-theoretic lemma showing that
successive values differ by exactly 1.  We package exactly that lemma as
`AdjacentUnit`, and formally prove the complete remaining argument.
 
-/

namespace IMO2010P3

/-! ## Problem predicates -/

/--
The original square condition, with zero-based indexing for the
positive integers.
-/
def Good (g : ℕ → ℕ) : Prop :=
  ∀ m n : ℕ,
    IsSquare
      ((g m + (n + 1)) *
       (g n + (m + 1)))

/--
The key Lemma 2 from the published proof:

successive values differ by exactly one.
-/
def AdjacentUnit (g : ℕ → ℕ) : Prop :=
  ∀ n : ℕ,
    g (n + 1) = g n + 1 ∨
    g n = g (n + 1) + 1

/-! ## Elementary nonsquare lemmas -/

/--
For positive `t`, the product `t(t+1)` cannot be a square.

It lies strictly between `t²` and `(t+1)²`.
-/
lemma not_square_mul_succ
    (t : ℕ)
    (ht : 0 < t) :
    ¬ IsSquare (t * (t + 1)) := by

  rintro ⟨r, hr⟩

  have hl :
      t * t < r * r := by
    rw [← hr]
    nlinarith

  have hu :
      r * r < (t + 1) * (t + 1) := by
    rw [← hr]
    nlinarith

  have htr :
      t < r := by
    by_contra h
    have hle :
        r ≤ t := by
      omega
    nlinarith

  have hrt :
      r < t + 1 := by
    by_contra h
    have hle :
        t + 1 ≤ r := by
      omega
    nlinarith

  omega

/--
For positive `t`, the product `t(t+2)` cannot be a square.

Indeed,

    t² < t(t+2) < (t+1)².
-/
lemma not_square_mul_add_two
    (t : ℕ)
    (ht : 0 < t) :
    ¬ IsSquare (t * (t + 2)) := by

  rintro ⟨r, hr⟩

  have hl :
      t * t < r * r := by
    rw [← hr]
    nlinarith

  have hu :
      r * r < (t + 1) * (t + 1) := by
    rw [← hr]
    nlinarith

  have htr :
      t < r := by
    by_contra h
    have hle :
        r ≤ t := by
      omega
    nlinarith

  have hrt :
      r < t + 1 := by
    by_contra h
    have hle :
        t + 1 ≤ r := by
      omega
    nlinarith

  omega

/-! ## Consequences of the square condition -/

/--
Consecutive values cannot be equal.

This is Lemma 1 of the source solution.
--/
lemma adjacent_ne
    (g : ℕ → ℕ)
    (hgood : Good g) :
    ∀ n : ℕ,
      g n ≠ g (n + 1) := by

  intro n hEq

  have hsquare :=
    hgood n (n + 1)

  have hsquare' :
      IsSquare
        ((g n + (n + 1)) *
         ((g n + (n + 1)) + 1)) := by

    rw [← hEq] at hsquare

    convert hsquare using 1 <;> ring

  have hpos :
      0 < g n + (n + 1) := by
    omega

  exact
    not_square_mul_succ
      (g n + (n + 1))
      hpos
      hsquare'

/--
Values two places apart cannot be equal.

This is what prevents the `+1/-1` direction from changing.
-/
lemma two_apart_ne
    (g : ℕ → ℕ)
    (hgood : Good g) :
    ∀ n : ℕ,
      g n ≠ g (n + 2) := by

  intro n hEq

  have hsquare :=
    hgood n (n + 2)

  have hsquare' :
      IsSquare
        ((g n + (n + 1)) *
         ((g n + (n + 1)) + 2)) := by

    rw [← hEq] at hsquare

    convert hsquare using 1 <;> ring

  have hpos :
      0 < g n + (n + 1) := by
    omega

  exact
    not_square_mul_add_two
      (g n + (n + 1))
      hpos
      hsquare'

/-! ## Once Lemma 2 is established, all steps have the same sign -/

/--
If one step is upward, the next step must also be upward.

Otherwise the values two places apart would be equal.
-/
lemma up_step_propagates
    (g : ℕ → ℕ)
    (hgood : Good g)
    (hunit : AdjacentUnit g)
    (n : ℕ)
    (hup :
      g (n + 1) = g n + 1) :
    g (n + 2) = g (n + 1) + 1 := by

  rcases hunit (n + 1) with hnext | hnext

  · simpa [Nat.add_assoc] using hnext

  · exfalso

    have heq :
        g n = g (n + 2) := by
      omega

    exact
      (two_apart_ne g hgood n)
        heq

/--
Similarly, a downward step forces the next step to be downward.
-/
lemma down_step_propagates
    (g : ℕ → ℕ)
    (hgood : Good g)
    (hunit : AdjacentUnit g)
    (n : ℕ)
    (hdown :
      g n = g (n + 1) + 1) :
    g (n + 1) = g (n + 2) + 1 := by

  rcases hunit (n + 1) with hnext | hnext

  · exfalso

    have heq :
        g n = g (n + 2) := by
      omega

    exact
      (two_apart_ne g hgood n)
        heq

  · simpa [Nat.add_assoc] using hnext

/-!
## The decreasing possibility is impossible
-/

/--
If every step decreases by one, then

    g n + n = g 0.
-/
lemma formula_of_all_down
    (g : ℕ → ℕ)
    (hdown :
      ∀ n : ℕ,
        g n = g (n + 1) + 1) :
    ∀ n : ℕ,
      g n + n = g 0 := by

  intro n

  induction n with

  | zero =>
      simp

  | succ n ih =>
      have hn := hdown n

      have ih' :
          g n + n = g 0 :=
        ih

      omega

/--
An infinite natural-valued sequence cannot decrease by one forever.
-/
lemma not_all_down
    (g : ℕ → ℕ) :
    ¬ (∀ n : ℕ,
        g n = g (n + 1) + 1) := by

  intro hdown

  have hformula :=
    formula_of_all_down g hdown

  have h :=
    hformula (g 0 + 1)

  omega

/-! ## Therefore every step is upward -/

/--
Under the square condition and the source's Lemma 2,
every successive value increases by one.
-/
lemma all_steps_up
    (g : ℕ → ℕ)
    (hgood : Good g)
    (hunit : AdjacentUnit g) :
    ∀ n : ℕ,
      g (n + 1) = g n + 1 := by

  rcases hunit 0 with h0up | h0down

  /- First step upward: propagate forever. -/
  · intro n

    induction n with

    | zero =>
        exact h0up

    | succ n ih =>
        exact
          up_step_propagates
            g hgood hunit n ih

  /- First step downward: it would decrease forever, impossible. -/
  · exfalso

    have hallDown :
        ∀ n : ℕ,
          g n = g (n + 1) + 1 := by

      intro n

      induction n with

      | zero =>
          exact h0down

      | succ n ih =>
          exact
            down_step_propagates
              g hgood hunit n ih

    exact
      not_all_down g hallDown

/-! ## Solve the recurrence -/

/--
If every step increases by one, then

    g n = n + g 0.
-/
lemma formula_of_all_up
    (g : ℕ → ℕ)
    (hup :
      ∀ n : ℕ,
        g (n + 1) = g n + 1) :
    ∀ n : ℕ,
      g n = n + g 0 := by

  intro n

  induction n with

  | zero =>
      simp

  | succ n ih =>
      rw [hup n, ih]
      omega

/--
In the positive-integer coordinates of the problem, the answer is

    g(n+1) = (n+1) + k.

With zero-based Lean indices this is

    g n = n + 1 + k.

Here `k = g 0 - 1`.
-/
theorem imo2010_p3_from_key_lemma
    (g : ℕ → ℕ)
    (hpositive :
      ∀ n : ℕ, 0 < g n)
    (hgood : Good g)
    (hunit : AdjacentUnit g) :
    ∃ k : ℕ,
      ∀ n : ℕ,
        g n = n + 1 + k := by

  have hup :
      ∀ n : ℕ,
        g (n + 1) = g n + 1 :=
    all_steps_up g hgood hunit

  have hformula :
      ∀ n : ℕ,
        g n = n + g 0 :=
    formula_of_all_up g hup

  have hg0 :
      1 ≤ g 0 := by
    exact hpositive 0

  refine ⟨g 0 - 1, ?_⟩

  intro n

  rw [hformula n]

  omega

/-! ## Verification of the answer -/

/--
Every function

    g n = n + 1 + k

satisfies the required perfect-square condition.
-/
lemma affine_is_good
    (k : ℕ) :
    Good (fun n : ℕ => n + 1 + k) := by

  intro m n

  refine
    ⟨m + n + k + 2, ?_⟩

  ring

/--
Such functions are positive.
-/
lemma affine_is_positive
    (k : ℕ) :
    ∀ n : ℕ,
      0 < n + 1 + k := by

  intro n
  omega

/--
Such functions also satisfy the source's adjacent-unit lemma.
-/
lemma affine_has_adjacent_unit
    (k : ℕ) :
    AdjacentUnit
      (fun n : ℕ => n + 1 + k) := by

  intro n

  left

  omega

/--
Complete `sorry`-free characterization once the source's number-theoretic
Lemma 2 (`AdjacentUnit`) has been established.
-/
theorem imo2010_p3_after_lemma2
    (g : ℕ → ℕ)
    (hpositive :
      ∀ n : ℕ, 0 < g n) :
    (Good g ∧ AdjacentUnit g) ↔
      ∃ k : ℕ,
        ∀ n : ℕ,
          g n = n + 1 + k := by

  constructor

  · rintro ⟨hgood, hunit⟩

    exact
      imo2010_p3_from_key_lemma
        g hpositive hgood hunit

  · rintro ⟨k, hk⟩

    have hg :
        g =
          (fun n : ℕ => n + 1 + k) := by
      funext n
      exact hk n

    constructor

    · rw [hg]
      exact affine_is_good k

    · rw [hg]
      exact affine_has_adjacent_unit k

end IMO2010P3
