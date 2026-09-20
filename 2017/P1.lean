import Mathlib

namespace IMO2017P1

/-!
# IMO 2017 Problem 1 — recurrence core

For `x > 1`, the recurrence is

    next(x) = √x       if x is a perfect square,
              x + 3    otherwise.

Instead of depending on a particular API for `Nat.sqrt`,
we encode one transition relationally.

This makes the proof stable across Mathlib versions.

 
-/

/-!
## Perfect squares and one-step transitions
-/

def IsSquare (n : ℕ) : Prop :=
  ∃ r : ℕ, n = r * r

def Step (x y : ℕ) : Prop :=
  (∃ r : ℕ,
      x = r * r ∧
      y = r)
  ∨
  (¬ IsSquare x ∧
      y = x + 3)

/--
A sequence follows the recurrence if every consecutive pair
satisfies `Step`.
-/
def FollowsRecurrence
    (a : ℕ → ℕ) : Prop :=
  ∀ n : ℕ,
    Step (a n) (a (n + 1))

/-!
## Basic square facts
-/

lemma three_not_square :
    ¬ IsSquare 3 := by

  intro h

  rcases h with ⟨r, hr⟩

  unfold IsSquare at *

  nlinarith

lemma six_not_square :
    ¬ IsSquare 6 := by

  intro h

  rcases h with ⟨r, hr⟩

  nlinarith

lemma nine_square :
    IsSquare 9 := by

  refine ⟨3, ?_⟩

  norm_num

/-!
## The transitions 3 → 6 → 9 → 3
-/

lemma step_three
    {y : ℕ}
    (h : Step 3 y) :
    y = 6 := by

  rcases h with hsq | hns

  · rcases hsq with
      ⟨r, hr, hy⟩

    exfalso

    apply three_not_square

    exact ⟨r, hr⟩

  · rcases hns with
      ⟨_, hy⟩

    omega

lemma step_six
    {y : ℕ}
    (h : Step 6 y) :
    y = 9 := by

  rcases h with hsq | hns

  · rcases hsq with
      ⟨r, hr, hy⟩

    exfalso

    apply six_not_square

    exact ⟨r, hr⟩

  · rcases hns with
      ⟨_, hy⟩

    omega

lemma step_nine
    {y : ℕ}
    (h : Step 9 y) :
    y = 3 := by

  rcases h with hsq | hns

  · rcases hsq with
      ⟨r, hr, hy⟩

    have hr3 :
        r = 3 := by
      nlinarith

    rw [hr3] at hy

    exact hy

  · rcases hns with
      ⟨hnot, _⟩

    exact
      False.elim
        (hnot nine_square)

/-!
## The cycle inside any sequence satisfying the recurrence
-/

lemma value_after_three
    {a : ℕ → ℕ}
    (hrec : FollowsRecurrence a)
    {n : ℕ}
    (h : a n = 3) :
    a (n + 1) = 6 := by

  have hs :
      Step (a n) (a (n + 1)) :=
    hrec n

  rw [h] at hs

  exact
    step_three hs

lemma value_after_six
    {a : ℕ → ℕ}
    (hrec : FollowsRecurrence a)
    {n : ℕ}
    (h : a n = 6) :
    a (n + 1) = 9 := by

  have hs :
      Step (a n) (a (n + 1)) :=
    hrec n

  rw [h] at hs

  exact
    step_six hs

lemma value_after_nine
    {a : ℕ → ℕ}
    (hrec : FollowsRecurrence a)
    {n : ℕ}
    (h : a n = 9) :
    a (n + 1) = 3 := by

  have hs :
      Step (a n) (a (n + 1)) :=
    hrec n

  rw [h] at hs

  exact
    step_nine hs

/--
Starting from a `3`, three more steps return to `3`.
-/
lemma cycle_three_steps
    {a : ℕ → ℕ}
    (hrec : FollowsRecurrence a)
    {n : ℕ}
    (h : a n = 3) :
    a (n + 3) = 3 := by

  have h6 :
      a (n + 1) = 6 :=
    value_after_three
      hrec
      h

  have h9 :
      a ((n + 1) + 1) = 9 :=
    value_after_six
      hrec
      h6

  have h3 :
      a (((n + 1) + 1) + 1) = 3 :=
    value_after_nine
      hrec
      h9

  convert h3 using 1 <;> omega

/-!
## Repeating the cycle arbitrarily many times
-/

/--
Once `3` occurs, it occurs every three terms.
-/
lemma three_every_three
    {a : ℕ → ℕ}
    (hrec : FollowsRecurrence a)
    {n : ℕ}
    (h : a n = 3) :
    ∀ k : ℕ,
      a (n + 3 * k) = 3 := by

  intro k

  induction k with

  | zero =>
      simpa using h

  | succ k ih =>

      have hnext :
          a ((n + 3 * k) + 3) = 3 :=
        cycle_three_steps
          hrec
          ih

      convert hnext using 1 <;>
        omega

/--
Therefore, after reaching `3`, the value `3`
occurs arbitrarily far out in the sequence.
-/
theorem three_occurs_infinitely_often
    {a : ℕ → ℕ}
    (hrec : FollowsRecurrence a)
    {n₀ : ℕ}
    (h₀ : a n₀ = 3) :
    ∀ N : ℕ,
      ∃ n : ℕ,
        N ≤ n ∧
        a n = 3 := by

  intro N

  let k : ℕ :=
    N + 1

  let n : ℕ :=
    n₀ + 3 * k

  refine ⟨n, ?_, ?_⟩

  · dsimp [n, k]
    omega

  · dsimp [n, k]

    exact
      three_every_three
        hrec
        h₀
        (N + 1)

/-!
## Entering the cycle at 6 or 9
-/

lemma six_reaches_three
    {a : ℕ → ℕ}
    (hrec : FollowsRecurrence a)
    {n : ℕ}
    (h : a n = 6) :
    a (n + 2) = 3 := by

  have h9 :
      a (n + 1) = 9 :=
    value_after_six
      hrec
      h

  have h3 :
      a ((n + 1) + 1) = 3 :=
    value_after_nine
      hrec
      h9

  convert h3 using 1 <;>
    omega

lemma nine_reaches_three
    {a : ℕ → ℕ}
    (hrec : FollowsRecurrence a)
    {n : ℕ}
    (h : a n = 9) :
    a (n + 1) = 3 := by

  exact
    value_after_nine
      hrec
      h

/--
Entering any of `3,6,9` implies infinitely many later
occurrences of `3`.
-/
theorem cycle_entry_gives_infinite_repetition
    {a : ℕ → ℕ}
    (hrec : FollowsRecurrence a)
    {n₀ : ℕ}
    (h :
      a n₀ = 3 ∨
      a n₀ = 6 ∨
      a n₀ = 9) :
    ∀ N : ℕ,
      ∃ n : ℕ,
        N ≤ n ∧
        a n = 3 := by

  rcases h with h3 | h6 | h9

  · exact
      three_occurs_infinitely_often
        hrec
        h3

  · have hreach :
        a (n₀ + 2) = 3 :=
      six_reaches_three
        hrec
        h6

    exact
      three_occurs_infinitely_often
        hrec
        hreach

  · have hreach :
        a (n₀ + 1) = 3 :=
      nine_reaches_three
        hrec
        h9

    exact
      three_occurs_infinitely_often
        hrec
        hreach

/-!
## Divisibility by 3 and squares
-/

/--
If `3 ∣ r²`, then `3 ∣ r`.
-/
lemma three_dvd_of_square
    {r : ℕ}
    (h :
      3 ∣ r * r) :
    3 ∣ r := by

  have hp :
      Nat.Prime 3 := by
    norm_num

  rcases hp.dvd_mul.mp h with hr | hr

  · exact hr

  · exact hr

/--
If a perfect square is divisible by `3`, its square root
is divisible by `3`.
-/
lemma square_root_three_dvd
    {x r : ℕ}
    (hx :
      x = r * r)
    (h3 :
      3 ∣ x) :
    3 ∣ r := by

  rw [hx] at h3

  exact
    three_dvd_of_square
      h3

/--
One recurrence step preserves divisibility by `3`.
-/
lemma step_preserves_three_dvd
    {x y : ℕ}
    (hx :
      3 ∣ x)
    (hstep :
      Step x y) :
    3 ∣ y := by

  rcases hstep with hsq | hplus

  · rcases hsq with
      ⟨r, hrx, hry⟩

    rw [hry]

    exact
      square_root_three_dvd
        hrx
        hx

  · rcases hplus with
      ⟨_, hy⟩

    rw [hy]

    exact
      dvd_add
        hx
        (by norm_num)

/--
If the initial term is divisible by `3`,
all subsequent terms are divisible by `3`.
-/
theorem recurrence_preserves_three_dvd
    {a : ℕ → ℕ}
    (hrec :
      FollowsRecurrence a)
    (h0 :
      3 ∣ a 0) :
    ∀ n : ℕ,
      3 ∣ a n := by

  intro n

  induction n with

  | zero =>
      exact h0

  | succ n ih =>

      exact
        step_preserves_three_dvd
          ih
          (hrec n)

/-!
## Squares modulo 3
-/

/--
A square cannot be congruent to `2` modulo `3`.
-/
lemma square_mod_three_ne_two
    (r : ℕ) :
    (r * r) % 3 ≠ 2 := by

  have hr :
      r % 3 = 0 ∨
      r % 3 = 1 ∨
      r % 3 = 2 := by
    omega

  rcases hr with hr | hr | hr

  · have :
        (r * r) % 3 = 0 := by
      omega
    omega

  · have :
        (r * r) % 3 = 1 := by
      omega
    omega

  · have :
        (r * r) % 3 = 1 := by
      omega
    omega

/--
Therefore a number congruent to `2 mod 3`
cannot be a perfect square.
-/
lemma mod_three_two_not_square
    {x : ℕ}
    (hx :
      x % 3 = 2) :
    ¬ IsSquare x := by

  intro hs

  rcases hs with ⟨r, hr⟩

  rw [hr] at hx

  exact
    square_mod_three_ne_two r
      hx

/-!
## Numbers congruent to 2 mod 3 just increase by 3
-/

/--
If `x ≡ 2 (mod 3)`, then the recurrence cannot take
a square-root step, so the next value is `x+3`.
-/
lemma step_of_mod_three_two
    {x y : ℕ}
    (hx :
      x % 3 = 2)
    (h :
      Step x y) :
    y = x + 3 := by

  rcases h with hsq | hplus

  · rcases hsq with
      ⟨r, hrx, _⟩

    exfalso

    apply
      mod_three_two_not_square
        hx

    exact ⟨r, hrx⟩

  · exact hplus.2

/-!
## Useful source identities
-/

/--
The three-term cycle.
-/
theorem explicit_cycle :
    Step 3 6 ∧
    Step 6 9 ∧
    Step 9 3 := by

  constructor

  · right
    exact
      ⟨three_not_square,
       by norm_num⟩

  · constructor

    · right
      exact
        ⟨six_not_square,
         by norm_num⟩

    · left
      exact
        ⟨3,
         by norm_num,
         by norm_num⟩

/--
If `3 ∣ a₀` and a term of the sequence reaches one
of `3,6,9`, then the source's required infinite repetition
property follows.
-/
theorem divisible_three_and_cycle_entry
    {a : ℕ → ℕ}
    (hrec :
      FollowsRecurrence a)
    (h0 :
      3 ∣ a 0)
    {n₀ : ℕ}
    (hcycle :
      a n₀ = 3 ∨
      a n₀ = 6 ∨
      a n₀ = 9) :
    (∀ n : ℕ, 3 ∣ a n) ∧
    (∀ N : ℕ,
      ∃ n : ℕ,
        N ≤ n ∧
        a n = 3) := by

  constructor

  · exact
      recurrence_preserves_three_dvd
        hrec
        h0

  · exact
      cycle_entry_gives_infinite_repetition
        hrec
        hcycle

end IMO2017P1
