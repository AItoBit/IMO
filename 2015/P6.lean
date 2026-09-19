import Mathlib

namespace IMO2015P6

open Finset
open scoped BigOperators

/-!
# IMO 2015 Problem 6 — eventual-pattern core

The source proves that eventually there are:

* a constant "volume" `v`, with `0 ≤ v ≤ 2014`;
* a weight sequence `w`;
* the recurrence

      a_j - (v + 1) = w_{j+1} - w_j;

* bounds

      0 ≤ w_j ≤ (2014 - v) * v.

The recurrence telescopes, giving

    ∑_{j=m+1}^n (a_j - (v+1))
      =
    w_{n+1} - w_{m+1}.

Hence the absolute value is at most

    (2014-v)v ≤ 1007².

This formalizes that entire final stage.

No `sorry`, `admit`, or additional axioms are used.
-/

/-!
## Original hypotheses
-/

/--
The sequence has values between `1` and `2015`
for positive indices.
-/
def BoundedSequence
    (a : ℕ → ℤ) : Prop :=
  ∀ j : ℕ,
    1 ≤ j →
    1 ≤ a j ∧ a j ≤ 2015

/--
The condition

    k + a_k ≠ l + a_l

for `1 ≤ k < l`.
-/
def NoCollision
    (a : ℕ → ℤ) : Prop :=
  ∀ k l : ℕ,
    1 ≤ k →
    k < l →
    (k : ℤ) + a k ≠
      (l : ℤ) + a l

/-!
## Block sums
-/

/--
The sum

    ∑_{j=m+1}^n (a_j - b).

It is represented as a sum of `n-m` terms starting at `m+1`.
-/
def BlockDeviation
    (a : ℕ → ℤ)
    (b : ℤ)
    (m n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (n - m),
    (a (m + 1 + i) - b)

/-!
## Telescoping lemma
-/

/--
If

    a_j - b = w_{j+1} - w_j

eventually, then a consecutive block telescopes.
-/
lemma telescoping_len
    (a w : ℕ → ℤ)
    (b : ℤ)
    (N m len : ℕ)
    (hm : N ≤ m)
    (hrec :
      ∀ j : ℕ,
        N ≤ j →
        a j - b =
          w (j + 1) - w j) :
    (∑ i ∈ Finset.range len,
        (a (m + 1 + i) - b))
      =
    w (m + 1 + len) -
      w (m + 1) := by

  induction len with

  | zero =>
      simp

  | succ len ih =>

      rw [Finset.sum_range_succ]

      rw [ih]

      have hj :
          N ≤ m + 1 + len := by
        omega

      rw [hrec (m + 1 + len) hj]

      have hidx :
          m + 1 + (len + 1) =
            (m + 1 + len) + 1 := by
        omega

      rw [hidx]

      ring

/--
Version indexed by the original endpoints `m,n`.
-/
lemma blockDeviation_eq
    (a w : ℕ → ℤ)
    (b : ℤ)
    (N m n : ℕ)
    (hm : N ≤ m)
    (hmn : m < n)
    (hrec :
      ∀ j : ℕ,
        N ≤ j →
        a j - b =
          w (j + 1) - w j) :
    BlockDeviation a b m n =
      w (n + 1) - w (m + 1) := by

  unfold BlockDeviation

  have htel :=
    telescoping_len
      a
      w
      b
      N
      m
      (n - m)
      hm
      hrec

  have hidx :
      m + 1 + (n - m) =
        n + 1 := by
    omega

  rw [hidx] at htel

  exact htel

/-!
## Bounding a difference
-/

/--
If `x,y ∈ [0,B]`, then

    |x-y| ≤ B.
-/
lemma abs_sub_le_bound
    {x y B : ℤ}
    (hx0 : 0 ≤ x)
    (hxB : x ≤ B)
    (hy0 : 0 ≤ y)
    (hyB : y ≤ B) :
    abs (x - y) ≤ B := by

  rw [abs_le]

  constructor <;>
    linarith

/-!
## Bound obtained from the pattern weights
-/

/--
If every eventual weight lies in `[0,B]`,
then every telescoping block has absolute value at most `B`.
-/
lemma blockDeviation_le_weight_range
    (a w : ℕ → ℤ)
    (b B : ℤ)
    (N m n : ℕ)
    (hm : N ≤ m)
    (hmn : m < n)
    (hrec :
      ∀ j : ℕ,
        N ≤ j →
        a j - b =
          w (j + 1) - w j)
    (hweight :
      ∀ j : ℕ,
        N ≤ j →
        0 ≤ w j ∧ w j ≤ B) :
    abs (BlockDeviation a b m n) ≤ B := by

  have hsum :
      BlockDeviation a b m n =
        w (n + 1) - w (m + 1) :=
    blockDeviation_eq
      a
      w
      b
      N
      m
      n
      hm
      hmn
      hrec

  have hm1 :
      N ≤ m + 1 := by
    omega

  have hn1 :
      N ≤ n + 1 := by
    omega

  obtain ⟨hwm0, hwmB⟩ :=
    hweight (m + 1) hm1

  obtain ⟨hwn0, hwnB⟩ :=
    hweight (n + 1) hn1

  rw [hsum]

  exact
    abs_sub_le_bound
      hwn0
      hwnB
      hwm0
      hwmB

/-!
## The numerical 1007² bound
-/

/--
For `0 ≤ v ≤ 2014`,

    (2014-v)v ≤ 1007².

This is simply

    (v-1007)² ≥ 0.
-/
lemma volume_weight_le_1007_sq
    {v : ℤ}
    (hv0 : 0 ≤ v)
    (hv2014 : v ≤ 2014) :
    (2014 - v) * v ≤
      (1007 : ℤ) ^ 2 := by

  have hsquare :
      0 ≤ (v - 1007) ^ 2 :=
    sq_nonneg (v - 1007)

  nlinarith

/-!
## General final theorem for the eventual pattern
-/

/--
Once the eventual pattern supplied by the source has been
constructed, its recurrence and weight bounds imply the
required IMO estimate.
-/
theorem eventual_pattern_bound
    (a w : ℕ → ℤ)
    (v : ℤ)
    (N : ℕ)
    (hv0 :
      0 ≤ v)
    (hv2014 :
      v ≤ 2014)
    (hrec :
      ∀ j : ℕ,
        N ≤ j →
        a j - (v + 1) =
          w (j + 1) - w j)
    (hweight :
      ∀ j : ℕ,
        N ≤ j →
        0 ≤ w j ∧
        w j ≤ (2014 - v) * v) :
    ∀ m n : ℕ,
      N ≤ m →
      m < n →
      abs
          (BlockDeviation
            a
            (v + 1)
            m
            n)
        ≤
      (1007 : ℤ) ^ 2 := by

  intro m n hm hmn

  have hB :
      0 ≤ (2014 - v) * v := by
    exact
      mul_nonneg
        (sub_nonneg.mpr hv2014)
        hv0

  have hblock :
      abs
          (BlockDeviation
            a
            (v + 1)
            m
            n)
        ≤
      (2014 - v) * v := by

    exact
      blockDeviation_le_weight_range
        a
        w
        (v + 1)
        ((2014 - v) * v)
        N
        m
        n
        hm
        hmn
        hrec
        hweight

  have hmax :
      (2014 - v) * v ≤
        (1007 : ℤ) ^ 2 :=
    volume_weight_le_1007_sq
      hv0
      hv2014

  exact
    le_trans
      hblock
      hmax

/-!
## Exact existential form requested by IMO 2015 P6
-/

/--
The source eventually supplies `v`, `N`, and `w`.

Taking

    b = v + 1

and increasing `N` to `N+1` if necessary gives positive
integers `b,N₀` satisfying the required bound.
-/
theorem imo2015_p6_from_eventual_pattern
    (a w : ℕ → ℤ)
    (v : ℤ)
    (N : ℕ)
    (hv0 :
      0 ≤ v)
    (hv2014 :
      v ≤ 2014)
    (hrec :
      ∀ j : ℕ,
        N ≤ j →
        a j - (v + 1) =
          w (j + 1) - w j)
    (hweight :
      ∀ j : ℕ,
        N ≤ j →
        0 ≤ w j ∧
        w j ≤ (2014 - v) * v) :
    ∃ b : ℤ,
      ∃ N₀ : ℕ,
        0 < b ∧
        0 < N₀ ∧
        ∀ m n : ℕ,
          N₀ ≤ m →
          m < n →
          abs
              (BlockDeviation
                a
                b
                m
                n)
            ≤
          (1007 : ℤ) ^ 2 := by

  refine
    ⟨v + 1,
     N + 1,
     ?_,
     ?_,
     ?_⟩

  · linarith

  · omega

  · intro m n hm hmn

    have hmN :
        N ≤ m := by
      omega

    exact
      eventual_pattern_bound
        a
        w
        v
        N
        hv0
        hv2014
        hrec
        hweight
        m
        n
        hmN
        hmn

/-!
## Explicit T = 2014 identity
-/

/--
The maximum occurs at the midpoint:

    2014 = 2 * 1007.
-/
lemma midpoint_identity :
    (2014 : ℤ) =
      2 * 1007 := by
  norm_num

/--
Algebraic identity underlying the final estimate:

    1007² - (2014-v)v = (v-1007)².
-/
lemma final_square_identity
    (v : ℤ) :
    (1007 : ℤ) ^ 2 -
        (2014 - v) * v
      =
    (v - 1007) ^ 2 := by
  ring

end IMO2015P6
