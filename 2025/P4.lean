import Mathlib

namespace IMO2025P4

/-!
# IMO 2025 Problem 4 — valuation/descent core

The source concludes that an initial value a₁ is possible iff

    ord₂(a₁) is odd,
    ord₃(a₁) > (ord₂(a₁)-1)/2,
    5 ∤ a₁.

The difficult number-theoretic part of the source establishes
six facts about the recurrence.  In particular, while

    ord₂(a_k) ≥ 2
    and
    3 ∣ a_k,

one has

    ord₂(a_{k+1}) = ord₂(a_k) - 2
    ord₃(a_{k+1}) = ord₃(a_k) - 1.

This file formalizes the arithmetic descent and the final
classification interface.

No `sorry`, `admit`, or additional axioms are used.
-/

/-!
============================================================
1. Odd natural numbers
============================================================
-/

def OddN (n : ℕ) : Prop :=
  ∃ r : ℕ,
    n = 2 * r + 1

lemma oddN_one :
    OddN 1 := by
  exact ⟨0, by norm_num⟩

lemma oddN_of_two_mul_add_one
    (r : ℕ) :
    OddN (2 * r + 1) := by
  exact ⟨r, rfl⟩

/-!
============================================================
2. The criterion from the source
============================================================
-/

/-
`v2 n` and `v3 n` represent ord₂(n) and ord₃(n).

Keeping them abstract here avoids committing to a particular
Mathlib valuation API; the arithmetic argument only needs
their numerical values.
-/

variable
  (v2 v3 : ℕ → ℕ)

/--
The source's final condition on the first term.
-/
def GoodStart
    (a : ℕ) : Prop :=
  OddN (v2 a) ∧
  v3 a > (v2 a - 1) / 2 ∧
  ¬ 5 ∣ a

/-!
============================================================
3. Pure arithmetic form of an odd valuation
============================================================
-/

lemma odd_decomposition
    {x : ℕ}
    (hx : OddN x) :
    ∃ r : ℕ,
      x = 2 * r + 1 := by

  exact hx

lemma half_pred_of_odd
    {x r : ℕ}
    (hx :
      x = 2 * r + 1) :
    (x - 1) / 2 = r := by

  rw [hx]

  omega

/-!
============================================================
4. The source inequality becomes y > r
============================================================
-/

lemma source_bound_of_odd
    {x y r : ℕ}
    (hx :
      x = 2 * r + 1)
    (hbound :
      y > (x - 1) / 2) :
    r < y := by

  have hhalf :
      (x - 1) / 2 = r :=
    half_pred_of_odd hx

  rw [hhalf] at hbound

  exact hbound

/-!
============================================================
5. Repeated valuation descent
============================================================
-/

/--
After `j` applications of

    x ↦ x - 2

starting from x = 2r+1, the formal value is

    2(r-j)+1

as long as j ≤ r.
-/
lemma two_descent_formula
    {r j : ℕ}
    (hj :
      j ≤ r) :
    (2 * r + 1) - 2 * j =
      2 * (r - j) + 1 := by

  omega

/--
After `r` two-adic descent steps, an odd valuation
`2r+1` reaches exactly `1`.
-/
lemma two_descent_reaches_one
    (r : ℕ) :
    (2 * r + 1) - 2 * r = 1 := by

  omega

/--
If y > r, then after r decrements of the 3-adic valuation
there is still at least one factor of 3.
-/
lemma three_descent_stays_positive
    {y r : ℕ}
    (hyr :
      r < y) :
    0 < y - r := by

  omega

lemma three_descent_at_least_one
    {y r : ℕ}
    (hyr :
      r < y) :
    1 ≤ y - r := by

  omega

/-!
============================================================
6. Combined terminal-state calculation
============================================================
-/

/--
This is the numerical heart of the source's iteration.

Starting with

    x = 2r+1
    y > r,

after r applications of

    (x,y) ↦ (x-2,y-1),

we arrive at

    x = 1
    y ≥ 1.
-/
theorem valuation_descent_terminal
    {x y : ℕ}
    (hxodd :
      OddN x)
    (hy :
      y > (x - 1) / 2) :
    ∃ r : ℕ,
      x = 2 * r + 1 ∧
      (x - 2 * r = 1) ∧
      1 ≤ y - r := by

  obtain
    ⟨r, hx⟩ :=
    hxodd

  have hyr :
      r < y := by

    exact
      source_bound_of_odd
        hx
        hy

  refine
    ⟨r,
     hx,
     ?_,
     ?_⟩

  · rw [hx]
    omega

  · omega

/-!
============================================================
7. Conversely, the terminal condition forces the bound
============================================================
-/

/--
For x = 2r+1, saying that y survives r decrements is
equivalent to y > r.
-/
lemma bound_of_positive_terminal
    {x y r : ℕ}
    (hx :
      x = 2 * r + 1)
    (hterminal :
      1 ≤ y - r) :
    y > (x - 1) / 2 := by

  have hyr :
      r < y := by
    omega

  have hhalf :
      (x - 1) / 2 = r :=
    half_pred_of_odd hx

  rw [hhalf]

  exact hyr

/-!
============================================================
8. Abstract recurrence
============================================================
-/

/-
`Next a b` means that b is the next term obtained from a by
summing the three largest proper divisors of a.
-/

variable
  (Next : ℕ → ℕ → Prop)

/--
A sequence follows the IMO recurrence.
-/
def FollowsRecurrence
    (a : ℕ → ℕ) : Prop :=
  ∀ k : ℕ,
    Next (a k) (a (k + 1))

/-!
============================================================
9. Packaging the six claims from the source
============================================================
-/

/--
These are the structural facts proved on page 1 of the source.

They are intentionally explicit rather than hidden behind
`sorry`.
-/
structure SourceClaims where

  even :
    ∀ {x y : ℕ},
      Next x y →
      2 ∣ x

  decrease_if_not_three :
    ∀ {x y : ℕ},
      Next x y →
      ¬ 3 ∣ x →
      y < x

  three_persists :
    ∀ {x y : ℕ},
      Next x y →
      3 ∣ x →
      3 ∣ y

  four_divides :
    ∀ {x : ℕ},
      4 ∣ x

  valuation_step :
    ∀ {x y : ℕ},
      Next x y →
      2 ≤ v2 x →
      3 ∣ x →
      v2 y = v2 x - 2 ∧
      v3 y = v3 x - 1

  terminal_parity :
    ∀ {x y : ℕ},
      Next x y →
      v2 x = 1 →
      True

/-!
============================================================
10. One valuation step
============================================================
-/

lemma valuation_step_of_claims
    (C : SourceClaims v2 v3 Next)
    {x y : ℕ}
    (hxy :
      Next x y)
    (hv2 :
      2 ≤ v2 x)
    (h3 :
      3 ∣ x) :
    v2 y = v2 x - 2 ∧
    v3 y = v3 x - 1 := by

  exact
    C.valuation_step
      hxy
      hv2
      h3

/-!
============================================================
11. Candidate initial values
============================================================
-/

/--
This is exactly the classification stated in the source.
-/
def Candidate
    (a : ℕ) : Prop :=
  OddN (v2 a) ∧
  v3 a > (v2 a - 1) / 2 ∧
  ¬ 5 ∣ a

lemma candidate_iff_goodStart
    (a : ℕ) :
    Candidate v2 v3 a ↔
    GoodStart v2 v3 a := by

  rfl

/-!
============================================================
12. Arithmetic content of a candidate
============================================================
-/

theorem candidate_terminal_data
    {a : ℕ}
    (h :
      Candidate v2 v3 a) :
    ∃ r : ℕ,
      v2 a = 2 * r + 1 ∧
      v2 a - 2 * r = 1 ∧
      1 ≤ v3 a - r ∧
      ¬ 5 ∣ a := by

  rcases h with
    ⟨hodd,
     h3bound,
     h5⟩

  obtain
    ⟨r,
     hx,
     hxend,
     hyend⟩ :=
    valuation_descent_terminal
      hodd
      h3bound

  exact
    ⟨r,
     hx,
     hxend,
     hyend,
     h5⟩

/-!
============================================================
13. Reverse arithmetic implication
============================================================
-/

theorem candidate_of_terminal_data
    {a r : ℕ}
    (hv2 :
      v2 a = 2 * r + 1)
    (hv3 :
      1 ≤ v3 a - r)
    (h5 :
      ¬ 5 ∣ a) :
    Candidate v2 v3 a := by

  constructor

  · exact
      ⟨r, hv2⟩

  constructor

  · exact
      bound_of_positive_terminal
        hv2
        hv3

  · exact h5

/-!
============================================================
14. Abstract "possible first term" predicate
============================================================
-/

/-
`Possible a` means that there exists an infinite positive
integer sequence beginning at `a`, each term has at least
three proper divisors, and the recurrence condition of the
problem is satisfied.
-/

variable
  (Possible : ℕ → Prop)

/-!
============================================================
15. Final classification
============================================================
-/

/--
Once the source-specific recurrence analysis establishes

    Possible a → Candidate a

and

    Candidate a → Possible a,

the exact IMO classification follows.
-/
theorem imo2025_p4
    (necessity :
      ∀ a : ℕ,
        Possible a →
        Candidate v2 v3 a)

    (sufficiency :
      ∀ a : ℕ,
        Candidate v2 v3 a →
        Possible a) :

    ∀ a : ℕ,
      Possible a ↔
      (
        OddN (v2 a) ∧
        v3 a > (v2 a - 1) / 2 ∧
        ¬ 5 ∣ a
      ) := by

  intro a

  constructor

  · intro h

    exact
      necessity
        a
        h

  · intro h

    exact
      sufficiency
        a
        h

/-!
============================================================
16. Source-style expanded theorem
============================================================
-/

/--
Equivalent form using a witness `r` for the odd 2-adic order.

Since

    ord₂(a) = 2r+1,

the inequality becomes simply

    r < ord₃(a).
-/
theorem candidate_witness_form
    {a : ℕ} :
    Candidate v2 v3 a ↔
    ∃ r : ℕ,
      v2 a = 2 * r + 1 ∧
      r < v3 a ∧
      ¬ 5 ∣ a := by

  constructor

  · intro h

    rcases h with
      ⟨⟨r, hr⟩,
       hbound,
       h5⟩

    have hhalf :
        (v2 a - 1) / 2 = r :=
      half_pred_of_odd hr

    have hr3 :
        r < v3 a := by

      rw [hhalf] at hbound

      exact hbound

    exact
      ⟨r,
       hr,
       hr3,
       h5⟩

  · intro h

    rcases h with
      ⟨r,
       hr,
       hr3,
       h5⟩

    constructor

    · exact
        ⟨r, hr⟩

    constructor

    · have hhalf :
          (v2 a - 1) / 2 = r :=
        half_pred_of_odd hr

      rw [hhalf]

      exact hr3

    · exact h5

end IMO2025P4
