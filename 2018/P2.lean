import Mathlib

namespace IMO2018P2

open Finset
open scoped BigOperators

/-!
# IMO 2018 Problem 2

Find all `n ≥ 3` for which there exist real numbers

    a₁, ..., aₙ₊₂

such that

    aₙ₊₁ = a₁,
    aₙ₊₂ = a₂,

and

    aᵢ * aᵢ₊₁ + 1 = aᵢ₊₂

for `i = 1,...,n`.

We encode this as a periodic infinite sequence.

The final theorem is

    Admissible n ↔ 3 ∣ n.

No `sorry`, `admit`, or extra axioms.
-/

/-!
## Periodic formulation
-/

def Admissible (n : ℕ) : Prop :=
  ∃ a : ℕ → ℝ,
    (∀ i : ℕ, a (i + n) = a i) ∧
    (∀ i : ℕ,
      a i * a (i + 1) + 1 =
        a (i + 2))

/-!
## Periodicity lemmas
-/

/--
If `p` is a period, then every multiple of `p`
is also a period.
-/
lemma periodic_mul
    (a : ℕ → ℝ)
    (p : ℕ)
    (hper :
      ∀ i : ℕ,
        a (i + p) = a i) :
    ∀ i k : ℕ,
      a (i + k * p) = a i := by

  intro i k

  induction k with

  | zero =>
      simp

  | succ k ih =>

      have hs :
          a ((i + k * p) + p) =
            a (i + k * p) :=
        hper (i + k * p)

      have hstep :
          a (i + (k + 1) * p) =
            a (i + k * p) := by

        simpa [Nat.succ_mul, Nat.add_assoc] using hs

      exact hstep.trans ih

/--
Reduce an index modulo a period.
-/
lemma periodic_reduce_mod
    (a : ℕ → ℝ)
    (p : ℕ)
    (hper :
      ∀ i : ℕ,
        a (i + p) = a i)
    (i : ℕ) :
    a i = a (i % p) := by

  let r : ℕ :=
    i % p

  let q : ℕ :=
    i / p

  have hdecomp :
      r + p * q = i := by

    simpa [r, q] using
      Nat.mod_add_div i p

  have hmul :
      a (r + q * p) =
        a r :=
    periodic_mul
      a
      p
      hper
      r
      q

  calc
    a i
        =
      a (r + q * p) := by

        congr 1

        calc
          i = r + p * q :=
            hdecomp.symm

          _ = r + q * p := by
            ac_rfl

    _ = a r :=
      hmul

    _ = a (i % p) := by
      rfl

/-!
## Cyclic finite sums
-/

/--
Shifting a sum over one complete period by one
does not change it.
-/
lemma sum_shift_one
    (f : ℕ → ℝ)
    (n : ℕ)
    (hwrap :
      f n = f 0) :
    (∑ i ∈ Finset.range n, f (i + 1))
      =
    ∑ i ∈ Finset.range n, f i := by

  have h₁ :=
    Finset.sum_range_succ' f n

  have h₂ :=
    Finset.sum_range_succ f n

  linarith

/--
A fixed shift does not change the sum over
one complete period.
-/
lemma sum_shift
    (f : ℕ → ℝ)
    (n : ℕ)
    (hper :
      ∀ i : ℕ,
        f (i + n) = f i) :
    ∀ k : ℕ,
      (∑ i ∈ Finset.range n,
          f (i + k))
        =
      ∑ i ∈ Finset.range n,
        f i := by

  intro k

  induction k with

  | zero =>
      simp

  | succ k ih =>

      have hwrap :
          (fun j => f (j + k)) n =
            (fun j => f (j + k)) 0 := by

        dsimp

        have hp :=
          hper k

        simpa [
          Nat.add_assoc,
          Nat.add_comm,
          Nat.add_left_comm
        ] using hp

      have hs :=
        sum_shift_one
          (fun j => f (j + k))
          n
          hwrap

      calc
        (∑ i ∈ Finset.range n,
            f (i + (k + 1)))
            =
          ∑ i ∈ Finset.range n,
            f ((i + 1) + k) := by

              apply Finset.sum_congr rfl

              intro i hi

              congr 1

              omega

        _ =
          ∑ i ∈ Finset.range n,
            f (i + k) :=
              hs

        _ =
          ∑ i ∈ Finset.range n,
            f i :=
              ih

/-!
## Two algebraic consequences of the recurrence
-/

/--
Multiply

    aᵢ aᵢ₊₁ + 1 = aᵢ₊₂

by `aᵢ₊₂`.
-/
lemma recurrence_mul_next
    {a : ℕ → ℝ}
    (hrec :
      ∀ i : ℕ,
        a i * a (i + 1) + 1 =
          a (i + 2))
    (i : ℕ) :
    a i * a (i + 1) * a (i + 2) +
        a (i + 2)
      =
    (a (i + 2)) ^ 2 := by

  calc
    a i * a (i + 1) * a (i + 2) +
        a (i + 2)
        =
      (a i * a (i + 1) + 1) *
        a (i + 2) := by
          ring

    _ =
      a (i + 2) * a (i + 2) := by
        rw [hrec i]

    _ =
      (a (i + 2)) ^ 2 := by
        ring

/--
Use the recurrence one step later and multiply by `aᵢ`.
-/
lemma recurrence_mul_previous
    {a : ℕ → ℝ}
    (hrec :
      ∀ i : ℕ,
        a i * a (i + 1) + 1 =
          a (i + 2))
    (i : ℕ) :
    a i * a (i + 1) * a (i + 2) +
        a i
      =
    a i * a (i + 3) := by

  calc
    a i * a (i + 1) * a (i + 2) +
        a i
        =
      a i *
        (a (i + 1) * a (i + 2) + 1) := by
          ring

    _ =
      a i * a (i + 3) := by
        rw [hrec (i + 1)]

/-!
## Main summed identity
-/

/--
For a periodic solution,

    Σ aᵢ² = Σ aᵢ aᵢ₊₃.
-/
lemma sum_square_eq_cross
    {a : ℕ → ℝ}
    {n : ℕ}
    (hper :
      ∀ i : ℕ,
        a (i + n) = a i)
    (hrec :
      ∀ i : ℕ,
        a i * a (i + 1) + 1 =
          a (i + 2)) :
    (∑ i ∈ Finset.range n,
        (a i) ^ 2)
      =
    ∑ i ∈ Finset.range n,
      a i * a (i + 3) := by

  have hsum₁ :
      (∑ i ∈ Finset.range n,
          (a i * a (i + 1) * a (i + 2) +
           a (i + 2)))
        =
      ∑ i ∈ Finset.range n,
        (a (i + 2)) ^ 2 := by

    apply Finset.sum_congr rfl

    intro i hi

    exact
      recurrence_mul_next
        hrec
        i

  have hsum₂ :
      (∑ i ∈ Finset.range n,
          (a i * a (i + 1) * a (i + 2) +
           a i))
        =
      ∑ i ∈ Finset.range n,
        a i * a (i + 3) := by

    apply Finset.sum_congr rfl

    intro i hi

    exact
      recurrence_mul_previous
        hrec
        i

  rw [Finset.sum_add_distrib] at hsum₁
  rw [Finset.sum_add_distrib] at hsum₂

  have hshift₂ :
      (∑ i ∈ Finset.range n,
          a (i + 2))
        =
      ∑ i ∈ Finset.range n,
        a i :=
    sum_shift
      a
      n
      hper
      2

  have hper_sq :
      ∀ i : ℕ,
        (a (i + n)) ^ 2 =
          (a i) ^ 2 := by

    intro i

    rw [hper i]

  have hshift₂sq :
      (∑ i ∈ Finset.range n,
          (a (i + 2)) ^ 2)
        =
      ∑ i ∈ Finset.range n,
        (a i) ^ 2 :=
    sum_shift
      (fun i => (a i) ^ 2)
      n
      hper_sq
      2

  rw [hshift₂, hshift₂sq] at hsum₁

  linarith

/-!
## Sum of squared three-step differences
-/

/--
The identity above yields

    Σ (aᵢ-aᵢ₊₃)² = 0.
-/
lemma sum_three_step_sq_eq_zero
    {a : ℕ → ℝ}
    {n : ℕ}
    (hper :
      ∀ i : ℕ,
        a (i + n) = a i)
    (hrec :
      ∀ i : ℕ,
        a i * a (i + 1) + 1 =
          a (i + 2)) :
    (∑ i ∈ Finset.range n,
        (a i - a (i + 3)) ^ 2)
      =
    0 := by

  have hcross :
      (∑ i ∈ Finset.range n,
          (a i) ^ 2)
        =
      ∑ i ∈ Finset.range n,
        a i * a (i + 3) :=
    sum_square_eq_cross
      hper
      hrec

  have hper_sq :
      ∀ i : ℕ,
        (a (i + n)) ^ 2 =
          (a i) ^ 2 := by

    intro i

    rw [hper i]

  have hshift₃sq :
      (∑ i ∈ Finset.range n,
          (a (i + 3)) ^ 2)
        =
      ∑ i ∈ Finset.range n,
        (a i) ^ 2 :=
    sum_shift
      (fun i => (a i) ^ 2)
      n
      hper_sq
      3

  calc
    (∑ i ∈ Finset.range n,
        (a i - a (i + 3)) ^ 2)
        =
      ∑ i ∈ Finset.range n,
        ((a i) ^ 2 +
         (a (i + 3)) ^ 2 -
         2 * (a i * a (i + 3))) := by

          apply Finset.sum_congr rfl

          intro i hi

          ring

    _ =
      (∑ i ∈ Finset.range n,
          (a i) ^ 2)
        +
      (∑ i ∈ Finset.range n,
          (a (i + 3)) ^ 2)
        -
      2 *
      (∑ i ∈ Finset.range n,
          a i * a (i + 3)) := by

          rw [
            Finset.sum_sub_distrib,
            Finset.sum_add_distrib,
            ← Finset.mul_sum
          ]

    _ = 0 := by

      rw [hshift₃sq, ← hcross]

      ring

/-!
## Pointwise three-step equality
-/

/--
Every index in the first full period satisfies

    aᵢ = aᵢ₊₃.
-/
lemma three_step_local
    {a : ℕ → ℝ}
    {n : ℕ}
    (hper :
      ∀ i : ℕ,
        a (i + n) = a i)
    (hrec :
      ∀ i : ℕ,
        a i * a (i + 1) + 1 =
          a (i + 2))
    {i : ℕ}
    (hi :
      i < n) :
    a i = a (i + 3) := by

  have hsum :
      (∑ j ∈ Finset.range n,
          (a j - a (j + 3)) ^ 2)
        =
      0 :=
    sum_three_step_sq_eq_zero
      hper
      hrec

  have hmem :
      i ∈ Finset.range n :=
    Finset.mem_range.mpr hi

  have hle :
      (a i - a (i + 3)) ^ 2
        ≤
      ∑ j ∈ Finset.range n,
        (a j - a (j + 3)) ^ 2 := by

    exact
      Finset.single_le_sum
        (fun j hj =>
          sq_nonneg
            (a j - a (j + 3)))
        hmem

  rw [hsum] at hle

  have hz :
      (a i - a (i + 3)) ^ 2 =
        0 := by

    exact
      le_antisymm
        hle
        (sq_nonneg
          (a i - a (i + 3)))

  nlinarith

/--
The relation `a(i+3)=a(i)` holds globally.
-/
lemma three_step_global
    {a : ℕ → ℝ}
    {n : ℕ}
    (hn :
      0 < n)
    (hper :
      ∀ i : ℕ,
        a (i + n) = a i)
    (hrec :
      ∀ i : ℕ,
        a i * a (i + 1) + 1 =
          a (i + 2)) :
    ∀ i : ℕ,
      a (i + 3) = a i := by

  intro i

  let r : ℕ :=
    i % n

  let q : ℕ :=
    i / n

  have hr :
      r < n := by

    dsimp [r]

    exact
      Nat.mod_lt
        i
        hn

  have hlocal :
      a r = a (r + 3) :=
    three_step_local
      hper
      hrec
      hr

  have hdecomp :
      r + n * q = i := by

    simpa [r, q] using
      Nat.mod_add_div i n

  have hi :
      i = r + q * n := by

    calc
      i =
        r + n * q :=
          hdecomp.symm

      _ =
        r + q * n := by
          ac_rfl

  have hperiod_i :
      a i = a r := by

    rw [hi]

    exact
      periodic_mul
        a
        n
        hper
        r
        q

  have hperiod_i3 :
      a (i + 3) =
        a (r + 3) := by

    have hp :
        a ((r + 3) + q * n)
          =
        a (r + 3) :=
      periodic_mul
        a
        n
        hper
        (r + 3)
        q

    calc
      a (i + 3)
          =
        a ((r + 3) + q * n) := by

          congr 1

          rw [hi]

          omega

      _ =
        a (r + 3) :=
          hp

  calc
    a (i + 3)
        =
      a (r + 3) :=
        hperiod_i3

    _ =
      a r :=
        hlocal.symm

    _ =
      a i :=
        hperiod_i.symm

/-!
## Combining periods n and 3
-/

/--
If the sequence has periods `n` and `3`, but `3 ∤ n`,
then its first three entries coincide.
-/
lemma first_three_equal_of_not_three_dvd
    {a : ℕ → ℝ}
    {n : ℕ}
    (hper :
      ∀ i : ℕ,
        a (i + n) = a i)
    (hthree :
      ∀ i : ℕ,
        a (i + 3) = a i)
    (hnot :
      ¬ 3 ∣ n) :
    a 0 = a 1 ∧
    a 1 = a 2 := by

  have hmod_ne :
      n % 3 ≠ 0 := by

    intro hz

    apply hnot

    refine
      ⟨n / 3, ?_⟩

    have hd :=
      Nat.mod_add_div n 3

    rw [hz] at hd

    omega

  have hmod_lt :
      n % 3 < 3 :=
    Nat.mod_lt
      n
      (by norm_num)

  have hcases :
      n % 3 = 1 ∨
      n % 3 = 2 := by

    omega

  have hn0 :
      a n = a 0 := by

    simpa using
      hper 0

  have hn1 :
      a (n + 1) = a 1 := by

    have hp :=
      hper 1

    simpa [
      Nat.add_comm,
      Nat.add_left_comm,
      Nat.add_assoc
    ] using hp

  have hred_n :
      a n = a (n % 3) :=
    periodic_reduce_mod
      a
      3
      hthree
      n

  have hred_n1 :
      a (n + 1) =
        a ((n + 1) % 3) :=
    periodic_reduce_mod
      a
      3
      hthree
      (n + 1)

  rcases hcases with
    hmod1 | hmod2

  · have hnext :
        (n + 1) % 3 = 2 := by
      omega

    constructor

    · calc
        a 0 =
          a n :=
            hn0.symm

        _ =
          a (n % 3) :=
            hred_n

        _ =
          a 1 := by
            rw [hmod1]

    · calc
        a 1 =
          a (n + 1) :=
            hn1.symm

        _ =
          a ((n + 1) % 3) :=
            hred_n1

        _ =
          a 2 := by
            rw [hnext]

  · have hnext :
        (n + 1) % 3 = 0 := by
      omega

    have h02 :
        a 0 = a 2 := by

      calc
        a 0 =
          a n :=
            hn0.symm

        _ =
          a (n % 3) :=
            hred_n

        _ =
          a 2 := by
            rw [hmod2]

    have h10 :
        a 1 = a 0 := by

      calc
        a 1 =
          a (n + 1) :=
            hn1.symm

        _ =
          a ((n + 1) % 3) :=
            hred_n1

        _ =
          a 0 := by
            rw [hnext]

    constructor

    · exact h10.symm

    · calc
        a 1 =
          a 0 :=
            h10

        _ =
          a 2 :=
            h02

/-!
## Necessity
-/

/--
Any admissible `n ≥ 3` must satisfy `3 ∣ n`.
-/
theorem three_dvd_of_admissible
    {n : ℕ}
    (hn :
      3 ≤ n)
    (h :
      Admissible n) :
    3 ∣ n := by

  rcases h with
    ⟨a, hper, hrec⟩

  by_contra hnot

  have hthree :
      ∀ i : ℕ,
        a (i + 3) = a i :=
    three_step_global
      (by omega)
      hper
      hrec

  have heq :
      a 0 = a 1 ∧
      a 1 = a 2 :=
    first_three_equal_of_not_three_dvd
      hper
      hthree
      hnot

  have h01 :
      a 0 = a 1 :=
    heq.1

  have h12 :
      a 1 = a 2 :=
    heq.2

  have h0 :=
    hrec 0

  norm_num at h0

  rw [h01, h12] at h0

  have hsquare :
      0 ≤
        (a 1 - (1 / 2 : ℝ)) ^ 2 :=
    sq_nonneg
      (a 1 - (1 / 2 : ℝ))

  nlinarith

/-!
## Construction
-/

/--
The repeating solution

    2, -1, -1, 2, -1, -1, ...
-/
def pattern (i : ℕ) : ℝ :=
  if i % 3 = 0
    then 2
    else -1

/--
The `2,-1,-1` pattern satisfies

    aᵢ aᵢ₊₁ + 1 = aᵢ₊₂.
-/
lemma pattern_recurrence
    (i : ℕ) :
    pattern i *
        pattern (i + 1) + 1
      =
    pattern (i + 2) := by

  have hr :
      i % 3 = 0 ∨
      i % 3 = 1 ∨
      i % 3 = 2 := by

    have hlt :
        i % 3 < 3 :=
      Nat.mod_lt
        i
        (by norm_num)

    omega

  rcases hr with
    h0 | h1 | h2

  · have hnext1 :
        (i + 1) % 3 = 1 := by
      omega

    have hnext2 :
        (i + 2) % 3 = 2 := by
      omega

    norm_num [
      pattern,
      h0,
      hnext1,
      hnext2
    ]

  · have hnext1 :
        (i + 1) % 3 = 2 := by
      omega

    have hnext2 :
        (i + 2) % 3 = 0 := by
      omega

    norm_num [
      pattern,
      h1,
      hnext1,
      hnext2
    ]

  · have hnext1 :
        (i + 1) % 3 = 0 := by
      omega

    have hnext2 :
        (i + 2) % 3 = 1 := by
      omega

    norm_num [
      pattern,
      h2,
      hnext1,
      hnext2
    ]

/--
Every multiple of `3` is a period of the pattern.
-/
lemma pattern_period
    {n : ℕ}
    (h :
      3 ∣ n) :
    ∀ i : ℕ,
      pattern (i + n) =
        pattern i := by

  rcases h with
    ⟨k, rfl⟩

  intro i

  unfold pattern

  have hmod :
      (i + 3 * k) % 3 =
        i % 3 := by

    omega

  rw [hmod]

/--
If `3 ∣ n`, then `n` is admissible.
-/
theorem admissible_of_three_dvd
    {n : ℕ}
    (h :
      3 ∣ n) :
    Admissible n := by

  refine
    ⟨pattern,
     pattern_period h,
     ?_⟩

  intro i

  exact
    pattern_recurrence
      i

/-!
## Complete classification
-/

/--
IMO 2018 Problem 2.

For every `n ≥ 3`, a cyclic real solution exists
if and only if `n` is divisible by `3`.
-/
theorem imo2018_p2
    (n : ℕ)
    (hn :
      3 ≤ n) :
    Admissible n ↔ 3 ∣ n := by

  constructor

  · intro h

    exact
      three_dvd_of_admissible
        hn
        h

  · intro h

    exact
      admissible_of_three_dvd
        h

end IMO2018P2
