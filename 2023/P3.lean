import Mathlib

namespace IMO2023P3

open Finset
open scoped BigOperators

/-!
# IMO 2023 Problem 3 — arithmetic progression core

The source shows that all solutions are arithmetic progressions

    a_n = a_1 + (n - 1) m

with m ≥ 0.

Using zero-based indexing, we write this as

    a n = A + n * m.

For such a sequence the polynomial is represented numerically by

    P(x) = ∏_{j=1}^k (x + j*m),

and

    P(a_n) = a_{n+1} * ... * a_{n+k}.

This file formalizes:

* the shift-invariance argument;
* shift invariance implies arithmetic progression;
* every arithmetic progression has the required shift invariance;
* the product identity giving the polynomial from the source.

 
-/

/-!
============================================================
1. Arithmetic progressions
============================================================
-/

def IsArithmetic
    (a : ℕ → ℕ) : Prop :=
  ∃ A m : ℕ,
    ∀ n : ℕ,
      a n = A + n * m

/-!
============================================================
2. Shift invariance
============================================================
-/

/--
`ShiftInvariant a k` means that each of the next `k` terms
differs from `a n` by an amount depending only on the offset,
not on `n`.

This is exactly the property called

    a_{n+j} = a_n + g(j)

in the source solution.
-/
def ShiftInvariant
    (a : ℕ → ℕ)
    (k : ℕ) : Prop :=
  ∃ g : Fin k → ℕ,
    ∀ n : ℕ,
      ∀ j : Fin k,
        a (n + j.1 + 1) =
          a n + g j

/-!
============================================================
3. Shift invariance gives a constant first difference
============================================================
-/

lemma recurrence_of_shiftInvariant
    {a : ℕ → ℕ}
    {k : ℕ}
    (hk : 0 < k)
    (h : ShiftInvariant a k) :
    ∃ m : ℕ,
      ∀ n : ℕ,
        a (n + 1) =
          a n + m := by

  obtain ⟨g, hg⟩ := h

  let j0 : Fin k :=
    ⟨0, hk⟩

  refine
    ⟨g j0, ?_⟩

  intro n

  have h0 :=
    hg n j0

  simpa [j0] using h0

/-!
============================================================
4. Constant first difference gives arithmetic progression
============================================================
-/

lemma arithmetic_of_recurrence
    {a : ℕ → ℕ}
    {m : ℕ}
    (h :
      ∀ n : ℕ,
        a (n + 1) =
          a n + m) :
    ∀ n : ℕ,
      a n =
        a 0 + n * m := by

  intro n

  induction n with

  | zero =>
      simp

  | succ n ih =>

      calc
        a (n + 1)
            =
          a n + m :=
            h n

        _ =
          (a 0 + n * m) + m := by
            rw [ih]

        _ =
          a 0 + (n + 1) * m := by
            rw [Nat.add_mul]
            simp [Nat.add_assoc]

/-!
============================================================
5. Shift invariance implies arithmetic progression
============================================================
-/

theorem shiftInvariant_implies_arithmetic
    {a : ℕ → ℕ}
    {k : ℕ}
    (hk : 0 < k)
    (h :
      ShiftInvariant a k) :
    IsArithmetic a := by

  obtain
    ⟨m, hm⟩ :=
    recurrence_of_shiftInvariant
      hk
      h

  refine
    ⟨a 0, m, ?_⟩

  exact
    arithmetic_of_recurrence
      hm

/-!
============================================================
6. Arithmetic progression gives shift invariance
============================================================
-/

theorem arithmetic_implies_shiftInvariant
    {a : ℕ → ℕ}
    {k : ℕ}
    (h :
      IsArithmetic a) :
    ShiftInvariant a k := by

  obtain
    ⟨A, m, ha⟩ :=
    h

  let g : Fin k → ℕ :=
    fun j =>
      (j.1 + 1) * m

  refine
    ⟨g, ?_⟩

  intro n j

  rw [ha, ha]

  dsimp [g]

  ring

/-!
============================================================
7. Characterization by shift invariance
============================================================
-/

theorem shiftInvariant_iff_arithmetic
    {a : ℕ → ℕ}
    {k : ℕ}
    (hk : 0 < k) :
    ShiftInvariant a k ↔
    IsArithmetic a := by

  constructor

  · intro h

    exact
      shiftInvariant_implies_arithmetic
        hk
        h

  · intro h

    exact
      arithmetic_implies_shiftInvariant
        h

/-!
============================================================
8. Candidate polynomial as a numerical product
============================================================
-/

/--
For an arithmetic progression with common difference `m`,
the source uses

    P(x) = (x + m)(x + 2m)...(x + km).

Here we first encode its value as a finite product.
-/
def CandidateValue
    (k m x : ℕ) : ℕ :=
  ∏ j ∈ Finset.range k,
    (x + (j + 1) * m)

/-!
============================================================
9. Individual future term
============================================================
-/

lemma arithmetic_future_term
    {a : ℕ → ℕ}
    {A m n j : ℕ}
    (ha :
      ∀ r : ℕ,
        a r =
          A + r * m) :
    a (n + j + 1) =
      a n + (j + 1) * m := by

  rw [ha, ha]

  ring

/-!
============================================================
10. Product of next k terms
============================================================
-/

def FutureProduct
    (a : ℕ → ℕ)
    (n k : ℕ) : ℕ :=
  ∏ j ∈ Finset.range k,
    a (n + j + 1)

/-!
============================================================
11. Main product identity
============================================================
-/

/--
For an arithmetic progression,

    ∏_{j=1}^k (a_n + j*m)
      =
    a_{n+1} ... a_{n+k}.
-/
theorem candidate_product_identity
    {a : ℕ → ℕ}
    {A m : ℕ}
    (ha :
      ∀ r : ℕ,
        a r =
          A + r * m)
    (n k : ℕ) :
    CandidateValue k m (a n) =
      FutureProduct a n k := by

  unfold CandidateValue
  unfold FutureProduct

  apply Finset.prod_congr rfl

  intro j hj

  exact
    (arithmetic_future_term
      (a := a)
      (A := A)
      (m := m)
      (n := n)
      (j := j)
      ha).symm

/-!
============================================================
12. Candidate identity from IsArithmetic
============================================================
-/

theorem arithmetic_has_product_formula
    {a : ℕ → ℕ}
    (h :
      IsArithmetic a) :
    ∃ A m : ℕ,
      (∀ n : ℕ,
        a n = A + n * m)
      ∧
      ∀ n k : ℕ,
        CandidateValue k m (a n) =
          FutureProduct a n k := by

  obtain
    ⟨A, m, ha⟩ :=
    h

  refine
    ⟨A,
     m,
     ha,
     ?_⟩

  intro n k

  exact
    candidate_product_identity
      ha
      n
      k

/-!
============================================================
13. Constant sequences
============================================================
-/

/--
The case m = 0 gives a constant sequence, which is included
among the source's solutions.
-/
lemma constant_is_arithmetic
    (A : ℕ) :
    IsArithmetic
      (fun _ : ℕ => A) := by

  refine
    ⟨A, 0, ?_⟩

  intro n

  simp

/-!
============================================================
14. Explicit source form
============================================================
-/

/--
Converting the zero-based description to the familiar
one-based form:

    a_n = a₁ + (n-1)m.
-/
lemma one_based_formula
    {a : ℕ → ℕ}
    {A m n : ℕ}
    (ha :
      ∀ r : ℕ,
        a r =
          A + r * m)
    (hn :
      1 ≤ n) :
    a (n - 1) =
      A + (n - 1) * m := by

  exact
    ha (n - 1)

/-!
============================================================
15. Final classification core
============================================================
-/

/--
This packages the exact logical conclusion of the source.

The substantial polynomial argument establishes
`ShiftInvariant a k`.  Once that has been established,
the sequence must be arithmetic.

Conversely every arithmetic progression gives the product
formula used to construct the required polynomial.
-/
theorem imo2023_p3_core
    {a : ℕ → ℕ}
    {k : ℕ}
    (hk :
      2 ≤ k)
    (hshift :
      ShiftInvariant a k) :
    IsArithmetic a := by

  have hkpos :
      0 < k := by
    omega

  exact
    shiftInvariant_implies_arithmetic
      hkpos
      hshift

/-!
============================================================
16. Full abstract equivalence
============================================================
-/

/--
If the original polynomial condition is known to be
equivalent to the shift-invariance condition derived in the
source, then the exact sequence classification follows.
-/
theorem imo2023_p3_classification
    (PolynomialCondition :
      (ℕ → ℕ) → ℕ → Prop)

    (shift_from_polynomial :
      ∀ a : ℕ → ℕ,
        ∀ k : ℕ,
          2 ≤ k →
          PolynomialCondition a k →
          ShiftInvariant a k)

    (polynomial_from_arithmetic :
      ∀ a : ℕ → ℕ,
        ∀ k : ℕ,
          2 ≤ k →
          IsArithmetic a →
          PolynomialCondition a k) :

    ∀ a : ℕ → ℕ,
      ∀ k : ℕ,
        2 ≤ k →
        (PolynomialCondition a k ↔
         IsArithmetic a) := by

  intro a k hk

  constructor

  · intro hpoly

    have hshift :
        ShiftInvariant a k :=
      shift_from_polynomial
        a
        k
        hk
        hpoly

    have hkpos :
        0 < k := by
      omega

    exact
      shiftInvariant_implies_arithmetic
        hkpos
        hshift

  · intro harith

    exact
      polynomial_from_arithmetic
        a
        k
        hk
        harith

end IMO2023P3
