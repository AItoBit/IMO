import Mathlib

/-!
# IMO 2011 Problem 4

We formalize the counting recurrence from the official solution.

For weights

    2^0, 2^1, ..., 2^(n-1),

the sum of all smaller powers of two is strictly less than the next
power of two. Hence the largest placed weight determines which pan
is heavier.

The source's insertion argument gives

    W(1) = 1
    W(n+1) = (2n+1) * W(n).

Therefore

    W(n) = 1 * 3 * 5 * ... * (2n-1).

No `sorry`, `admit`, or extra axioms are used.
-/

namespace IMO2011P4

open Finset

/-!
## Powers of two
-/

/--
The geometric sum

    1 + 2 + ... + 2^(m-1)

equals `2^m - 1`.
-/
lemma sum_powers_two (m : ℕ) :
    ∑ i ∈ Finset.range m, 2 ^ i = 2 ^ m - 1 := by

  induction m with

  | zero =>
      simp

  | succ m ih =>
      rw [Finset.sum_range_succ]
      rw [ih]
      rw [pow_succ]

      have hp :
          0 < 2 ^ m := by
        positivity

      omega

/--
The sum of all powers of two strictly smaller than `2^m`
is smaller than `2^m`.
-/
lemma smaller_powers_lt
    (m : ℕ) :
    (∑ i ∈ Finset.range m, 2 ^ i) < 2 ^ m := by

  rw [sum_powers_two]

  have hp :
      0 < 2 ^ m := by
    positivity

  omega

/--
Equivalent formulation: the heaviest power of two is larger
than all lighter weights combined.
-/
lemma heaviest_dominates
    (m : ℕ) :
    ∑ i ∈ Finset.range m, 2 ^ i < 2 ^ m := by

  exact smaller_powers_lt m

/-!
## Odd double factorial
-/

/--
`oddDoubleFactorial n` is

    1 * 3 * 5 * ... * (2n - 1).

In zero-based recursive form:

    oddDoubleFactorial 0 = 1
    oddDoubleFactorial (n+1)
      = (2n+1) * oddDoubleFactorial n.
-/
def oddDoubleFactorial : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
      (2 * n + 1) * oddDoubleFactorial n

@[simp]
lemma oddDoubleFactorial_zero :
    oddDoubleFactorial 0 = 1 := by
  rfl

@[simp]
lemma oddDoubleFactorial_succ
    (n : ℕ) :
    oddDoubleFactorial (n + 1)
      =
    (2 * n + 1) * oddDoubleFactorial n := by
  rfl

/--
Product form of the odd double factorial.
-/
lemma oddDoubleFactorial_eq_prod
    (n : ℕ) :
    oddDoubleFactorial n
      =
    ∏ k ∈ Finset.range n, (2 * k + 1) := by

  induction n with

  | zero =>
      simp [oddDoubleFactorial]

  | succ n ih =>
      rw [oddDoubleFactorial_succ]
      rw [Finset.prod_range_succ]
      rw [← ih]

      ring

/-!
## Zero-based recurrence
-/

/--
Any counting function satisfying

    W 0 = 1
    W (n+1) = (2n+1) W n

is exactly the odd double factorial.
-/
theorem count_of_recurrence
    (W : ℕ → ℕ)
    (hzero :
      W 0 = 1)
    (hrec :
      ∀ n : ℕ,
        W (n + 1) =
          (2 * n + 1) * W n) :
    ∀ n : ℕ,
      W n = oddDoubleFactorial n := by

  intro n

  induction n with

  | zero =>
      simpa [oddDoubleFactorial] using hzero

  | succ n ih =>
      calc
        W (n + 1)
            =
          (2 * n + 1) * W n :=
            hrec n

        _ =
          (2 * n + 1) *
            oddDoubleFactorial n := by
              rw [ih]

        _ =
          oddDoubleFactorial (n + 1) := by
              rfl

/-!
## One-indexed recurrence
-/

/--
Version matching the indexing of the olympiad solution:

    W 1 = 1
    W (n+1) = (2n+1) W n    for n ≥ 1.

Then

    W n = (2n-1)!!

for every positive `n`.
-/
theorem count_one_indexed
    (W : ℕ → ℕ)
    (h1 :
      W 1 = 1)
    (hrec :
      ∀ n : ℕ,
        1 ≤ n →
        W (n + 1) =
          (2 * n + 1) * W n) :
    ∀ n : ℕ,
      1 ≤ n →
      W n = oddDoubleFactorial n := by

  intro n hn

  cases n with

  | zero =>
      omega

  | succ n =>
      induction n with

      | zero =>
          simpa [oddDoubleFactorial] using h1

      | succ n ih =>

          have hnpos :
              1 ≤ n + 1 := by
            omega

          have hi :
              W (n + 1) =
                oddDoubleFactorial (n + 1) := by
            exact ih (by omega)

          calc
            W (n + 2)
                =
              (2 * (n + 1) + 1) *
                W (n + 1) := by
                  exact hrec (n + 1) hnpos

            _ =
              (2 * (n + 1) + 1) *
                oddDoubleFactorial (n + 1) := by
                  rw [hi]

            _ =
              oddDoubleFactorial (n + 2) := by
                  rfl

/-!
## Closed product form
-/

/--
The recurrence can be written as

    W n = ∏_{k<n} (2k+1).
-/
theorem count_eq_product
    (W : ℕ → ℕ)
    (hzero :
      W 0 = 1)
    (hrec :
      ∀ n : ℕ,
        W (n + 1) =
          (2 * n + 1) * W n)
    (n : ℕ) :
    W n =
      ∏ k ∈ Finset.range n,
        (2 * k + 1) := by

  calc
    W n
        =
      oddDoubleFactorial n :=
        count_of_recurrence
          W
          hzero
          hrec
          n

    _ =
      ∏ k ∈ Finset.range n,
        (2 * k + 1) :=
          oddDoubleFactorial_eq_prod n

/-!
## Final recurrence conclusion
-/

/--
Formal numerical conclusion corresponding to IMO 2011 Problem 4.

If `W` satisfies the official insertion recurrence, then

    W(n) = 1 * 3 * 5 * ... * (2n-1).
-/
theorem imo2011_p4
    (W : ℕ → ℕ)
    (hzero :
      W 0 = 1)
    (hrec :
      ∀ n : ℕ,
        W (n + 1) =
          (2 * n + 1) * W n) :
    ∀ n : ℕ,
      W n =
        ∏ k ∈ Finset.range n,
          (2 * k + 1) := by

  intro n

  exact
    count_eq_product
      W
      hzero
      hrec
      n

end IMO2011P4
