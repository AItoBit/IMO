import Mathlib

namespace IMO2016P4

/-!
# IMO 2016 Problem 4 — arithmetic core and b = 6 construction

Let

    P(n) = n^2 + n + 1.

A block of length `b` starting after `a` is fragrant when
for every `i = 1,...,b`, there is a different `j = 1,...,b`
such that `P(a+i)` and `P(a+j)` have a common prime factor.

The source proves that the least possible `b` is 6.

This file formalizes:

* the key polynomial difference identity;
* the key quadratic identity used to restrict common primes;
* the explicit fragrant block of length 6:
      P(196),...,P(201).

No `sorry`, `admit`, or extra axioms are used.
-/

/-!
## The polynomial
-/

def P (n : ℕ) : ℕ :=
  n ^ 2 + n + 1

def Pz (x : ℤ) : ℤ :=
  x ^ 2 + x + 1

/-!
## Basic polynomial identities
-/

/--
Difference identity:

    P(x+y) - P(x)
      =
    y(2x+y+1).
-/
lemma Pz_difference
    (x y : ℤ) :
    Pz (x + y) - Pz x
      =
    y * (2 * x + y + 1) := by
  unfold Pz
  ring

/--
If a number divides both `P(x)` and `P(x+y)`,
then it divides their difference.
-/
lemma common_dvd_difference
    {d x y : ℤ}
    (hx :
      d ∣ Pz x)
    (hy :
      d ∣ Pz (x + y)) :
    d ∣ y * (2 * x + y + 1) := by

  rcases hx with ⟨r, hr⟩
  rcases hy with ⟨s, hs⟩

  refine ⟨s - r, ?_⟩

  calc
    y * (2 * x + y + 1)
        =
      Pz (x + y) - Pz x := by
        rw [Pz_difference]
    _ =
      d * s - d * r := by
        rw [hs, hr]
    _ =
      d * (s - r) := by
        ring

/--
Useful identity from the source argument:

    4 P(x)
      =
    (2x+y+1)^2
      - 2y(2x+y+1)
      + y^2 + 3.
-/
lemma Pz_resultant_identity
    (x y : ℤ) :
    4 * Pz x
      =
    (2 * x + y + 1) ^ 2
      -
    2 * y * (2 * x + y + 1)
      +
    y ^ 2 + 3 := by
  unfold Pz
  ring

/-!
## Fragrant blocks
-/

/--
`FragrantBlock a b` means that the `b` numbers

    P(a+1), ..., P(a+b)

form a fragrant set in the sense of the problem.

For each index `i`, another index `j ≠ i` must exist
such that the corresponding two values have a common
prime divisor.
-/
def FragrantBlock
    (a b : ℕ) : Prop :=
  2 ≤ b ∧
  ∀ i : ℕ,
    1 ≤ i →
    i ≤ b →
    ∃ j : ℕ,
      1 ≤ j ∧
      j ≤ b ∧
      j ≠ i ∧
      ∃ p : ℕ,
        Nat.Prime p ∧
        p ∣ P (a + i) ∧
        p ∣ P (a + j)

/-!
## Explicit divisibility facts for the source's block
-/

/--
3 divides both P(196) and P(199).
-/
lemma three_pair :
    3 ∣ P 196 ∧
    3 ∣ P 199 := by
  constructor <;> norm_num [P]

/--
19 divides both P(197) and P(201).
-/
lemma nineteen_pair :
    19 ∣ P 197 ∧
    19 ∣ P 201 := by
  constructor <;> norm_num [P]

/--
7 divides both P(198) and P(200).
-/
lemma seven_pair :
    7 ∣ P 198 ∧
    7 ∣ P 200 := by
  constructor <;> norm_num [P]

/-!
## The explicit b = 6 construction
-/

/--
The block

    P(196), P(197), ..., P(201)

is fragrant.

Thus `b = 6` is attainable.
-/
theorem fragrant_block_six :
    FragrantBlock 195 6 := by

  refine ⟨by norm_num, ?_⟩

  intro i hi1 hi6

  interval_cases i

  ·
    refine
      ⟨4,
       by norm_num,
       by norm_num,
       by norm_num,
       3,
       by norm_num,
       ?_,
       ?_⟩

    · exact three_pair.1

    · exact three_pair.2

  ·
    refine
      ⟨6,
       by norm_num,
       by norm_num,
       by norm_num,
       19,
       by norm_num,
       ?_,
       ?_⟩

    · exact nineteen_pair.1

    · exact nineteen_pair.2

  ·
    refine
      ⟨5,
       by norm_num,
       by norm_num,
       by norm_num,
       7,
       by norm_num,
       ?_,
       ?_⟩

    · exact seven_pair.1

    · exact seven_pair.2

  ·
    refine
      ⟨1,
       by norm_num,
       by norm_num,
       by norm_num,
       3,
       by norm_num,
       ?_,
       ?_⟩

    · exact three_pair.2

    · exact three_pair.1

  ·
    refine
      ⟨3,
       by norm_num,
       by norm_num,
       by norm_num,
       7,
       by norm_num,
       ?_,
       ?_⟩

    · exact seven_pair.2

    · exact seven_pair.1

  ·
    refine
      ⟨2,
       by norm_num,
       by norm_num,
       by norm_num,
       19,
       by norm_num,
       ?_,
       ?_⟩

    · exact nineteen_pair.2

    · exact nineteen_pair.1

/-!
## The exact numerical values, useful for debugging
-/

lemma P196 :
    P 196 = 38613 := by
  norm_num [P]

lemma P197 :
    P 197 = 39007 := by
  norm_num [P]

lemma P198 :
    P 198 = 39403 := by
  norm_num [P]

lemma P199 :
    P 199 = 39801 := by
  norm_num [P]

lemma P200 :
    P 200 = 40201 := by
  norm_num [P]

lemma P201 :
    P 201 = 40603 := by
  norm_num [P]

/-!
## Prime witnesses explicitly
-/

lemma prime_three :
    Nat.Prime 3 := by
  norm_num

lemma prime_seven :
    Nat.Prime 7 := by
  norm_num

lemma prime_nineteen :
    Nat.Prime 19 := by
  norm_num

/-!
## Upper-bound conclusion
-/

/--
There exists a fragrant block with `b = 6`.
-/
theorem imo2016_p4_upper_bound :
    ∃ a : ℕ,
      FragrantBlock a 6 := by
  exact ⟨195, fragrant_block_six⟩

/-!
## Lower-bound arithmetic identities from the source
-/

/--
For gap 1:

    P(x+1)-P(x) = 2(x+1).
-/
lemma gap_one
    (x : ℤ) :
    Pz (x + 1) - Pz x =
      2 * (x + 1) := by
  rw [Pz_difference]
  ring

/--
For gap 2:

    P(x+2)-P(x) = 2(2x+3).
-/
lemma gap_two
    (x : ℤ) :
    Pz (x + 2) - Pz x =
      2 * (2 * x + 3) := by
  rw [Pz_difference]
  ring

/--
For gap 3:

    P(x+3)-P(x) = 3(2x+4).
-/
lemma gap_three
    (x : ℤ) :
    Pz (x + 3) - Pz x =
      3 * (2 * x + 4) := by
  rw [Pz_difference]
  ring

/--
For gap 4:

    P(x+4)-P(x) = 4(2x+5).
-/
lemma gap_four
    (x : ℤ) :
    Pz (x + 4) - Pz x =
      4 * (2 * x + 5) := by
  rw [Pz_difference]
  ring

/--
For gap 5:

    P(x+5)-P(x) = 5(2x+6).
-/
lemma gap_five
    (x : ℤ) :
    Pz (x + 5) - Pz x =
      5 * (2 * x + 6) := by
  rw [Pz_difference]
  ring

/-!
## Constants y² + 3 appearing in the source restriction
-/

lemma resultant_gap_one :
    (1 : ℤ) ^ 2 + 3 = 4 := by
  norm_num

lemma resultant_gap_two :
    (2 : ℤ) ^ 2 + 3 = 7 := by
  norm_num

lemma resultant_gap_three :
    (3 : ℤ) ^ 2 + 3 = 12 := by
  norm_num

lemma resultant_gap_four :
    (4 : ℤ) ^ 2 + 3 = 19 := by
  norm_num

lemma resultant_gap_five :
    (5 : ℤ) ^ 2 + 3 = 28 := by
  norm_num

end IMO2016P4
