import Mathlib

namespace IMO2016P2

/-!
# IMO 2016 Problem 2 — counting/divisibility core

The source first observes that `3 ∣ n`, so write

    n = 3k.

The double-counting argument then gives

    total number of I-cells
      = 4k² - 3a,

while the row condition gives

    total number of I-cells
      = 3k².

Hence

    4k² - 3a = 3k²,

so

    k² = 3a.

Therefore `3 ∣ k²`. Since `3` is prime, `3 ∣ k`,
and consequently

    9 ∣ n.

No `sorry`, `admit`, or additional axioms are used.
-/

/-!
## Algebraic form of the double count
-/

/--
The equality

    4k² - 3a = 3k²

implies

    k² = 3a.

We formulate it over `ℤ` to avoid truncated subtraction.
-/
lemma counting_rearrangement
    (k a : ℕ)
    (h :
      4 * (k : ℤ) * (k : ℤ) -
          3 * (a : ℤ)
        =
      3 * (k : ℤ) * (k : ℤ)) :
    (k : ℤ) * (k : ℤ) =
      3 * (a : ℤ) := by
  linarith

/-!
## From k² = 3a to 3 | k
-/

/--
If `k² = 3a`, then `3 ∣ k²`.
-/
lemma three_dvd_square
    {k a : ℕ}
    (h :
      k * k = 3 * a) :
    3 ∣ k * k := by

  refine ⟨a, ?_⟩

  exact h

/--
Since `3` is prime, if it divides `k*k`, then it divides `k`.
-/
lemma three_dvd_of_three_dvd_square
    {k : ℕ}
    (h :
      3 ∣ k * k) :
    3 ∣ k := by

  have hp :
      Nat.Prime 3 := by
    norm_num

  rcases hp.dvd_mul.mp h with hk | hk

  · exact hk

  · exact hk

/--
Therefore `k² = 3a` implies `3 ∣ k`.
-/
lemma three_dvd_k_of_square_eq
    {k a : ℕ}
    (h :
      k * k = 3 * a) :
    3 ∣ k := by

  apply three_dvd_of_three_dvd_square

  exact
    three_dvd_square h

/-!
## Main divisibility step
-/

/--
If

    n = 3k

and

    k² = 3a,

then

    9 ∣ n.
-/
lemma nine_dvd_of_reduced_count
    {n k a : ℕ}
    (hn :
      n = 3 * k)
    (hcount :
      k * k = 3 * a) :
    9 ∣ n := by

  have hk :
      3 ∣ k :=
    three_dvd_k_of_square_eq
      hcount

  rcases hk with
    ⟨t, ht⟩

  refine ⟨t, ?_⟩

  rw [hn, ht]

  ring

/-!
## Version directly from the integer double-count equation
-/

/--
This version mirrors the source most closely.

Assume

    n = 3k

and the double count gives

    4k² - 3a = 3k².

Then `9 ∣ n`.
-/
theorem imo2016_p2_counting_core
    {n k a : ℕ}
    (hn :
      n = 3 * k)
    (hdouble :
      4 * (k : ℤ) * (k : ℤ) -
          3 * (a : ℤ)
        =
      3 * (k : ℤ) * (k : ℤ)) :
    9 ∣ n := by

  have hkZ :
      (k : ℤ) * (k : ℤ) =
        3 * (a : ℤ) :=
    counting_rearrangement
      k
      a
      hdouble

  have hkNat :
      k * k = 3 * a := by
    exact_mod_cast hkZ

  exact
    nine_dvd_of_reduced_count
      hn
      hkNat

/-!
## Source count written with n = 3k
-/

/--
When `n = 3k`,

    n² / 9 = k².

Rather than using natural-number division, which makes
formal proofs unnecessarily awkward, we use the equivalent
multiplicative identity

    n² = 9k².
-/
lemma square_of_triple
    {n k : ℕ}
    (hn :
      n = 3 * k) :
    n * n =
      9 * (k * k) := by

  rw [hn]

  ring

/-!
## An abstract version of the source's cardinality count
-/

/--
Suppose:

* `d₁ = k²` cells of the first relevant diagonal type contain `I`;
* `d₂ = k²` cells of the second relevant diagonal type contain `I`;
* their intersection has `a` cells;
* after adding the relevant rows and columns, the source's
  inclusion-exclusion count gives `4k² - 3a`;
* the row count gives `3k²`.

Then `9 ∣ n`.
-/
theorem imo2016_p2_from_counts
    {n k a totalI : ℕ}
    (hn :
      n = 3 * k)
    (htotal :
      (totalI : ℤ) =
        4 * (k : ℤ) * (k : ℤ) -
          3 * (a : ℤ))
    (hrows :
      (totalI : ℤ) =
        3 * (k : ℤ) * (k : ℤ)) :
    9 ∣ n := by

  have hdouble :
      4 * (k : ℤ) * (k : ℤ) -
          3 * (a : ℤ)
        =
      3 * (k : ℤ) * (k : ℤ) := by

    calc
      4 * (k : ℤ) * (k : ℤ) -
          3 * (a : ℤ)
          =
        (totalI : ℤ) := by
          exact htotal.symm

      _ =
        3 * (k : ℤ) * (k : ℤ) :=
          hrows

  exact
    imo2016_p2_counting_core
      hn
      hdouble

/-!
## The crucial prime-divisibility argument separately
-/

/--
A compact reusable number-theoretic lemma:

    3 ∣ k²  →  3 ∣ k.
-/
lemma three_dvd_of_sq
    (k : ℕ)
    (h :
      3 ∣ k ^ 2) :
    3 ∣ k := by

  have hp :
      Nat.Prime 3 := by
    norm_num

  have hm :
      3 ∣ k * k := by
    simpa [pow_two] using h

  rcases hp.dvd_mul.mp hm with hk | hk

  · exact hk

  · exact hk

/-!
## Final necessity theorem
-/

/--
Arithmetic conclusion of the official counting argument:

any table satisfying the source's counting identities has
side length divisible by `9`.
-/
theorem imo2016_p2_necessity
    {n k a : ℕ}
    (hn :
      n = 3 * k)
    (hcount :
      3 * a = k * k) :
    9 ∣ n := by

  have hcount' :
      k * k = 3 * a :=
    hcount.symm

  exact
    nine_dvd_of_reduced_count
      hn
      hcount'

/-!
## Converse at the arithmetic level
-/

/--
If `9 ∣ n`, then in particular `3 ∣ n`.
-/
lemma three_dvd_of_nine_dvd
    {n : ℕ}
    (h :
      9 ∣ n) :
    3 ∣ n := by

  rcases h with ⟨t, rfl⟩

  refine ⟨3 * t, ?_⟩

  ring

/--
`9 ∣ n` can be written as `n = 9t`.
-/
lemma eq_nine_mul_of_nine_dvd
    {n : ℕ}
    (h :
      9 ∣ n) :
    ∃ t : ℕ,
      n = 9 * t := by

  exact h

end IMO2016P2
