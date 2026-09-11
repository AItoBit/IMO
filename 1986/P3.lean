import Mathlib

/-!
# IMO 1986, Problem 3 (Algebraic Core of Solution 1)

This formalizes the algebraic core of the monovariant method


The problem assigns five integers to the vertices of a pentagon.
We represent these as a 5-tuple `(x₁, x₂, x₃, x₄, x₅)`.
The operation replaces `(x₃, x₄, x₅)` with `(x₃ + x₄, -x₄, x₅ + x₄)`
when `x₄ < 0`.

Solution 1 defines the semi-invariant function:
  f(x) = Σ (x_i - x_{i+2})^2
and claims that the change in `f` after one operation is exactly `2 * S * x₄`,
where `S` is the invariant sum of the five entries. Since `S > 0` and `x₄ < 0`, 
this difference is strictly negative, proving termination.

We formalize this exact algebraic difference identity.
-/

namespace IMO1986P3

/-- The semi-invariant function f for the 5-tuple. -/
def f (v₁ v₂ v₃ v₄ v₅ : ℤ) : ℤ :=
  (v₁ - v₃)^2 + (v₂ - v₄)^2 + (v₃ - v₅)^2 + (v₄ - v₁)^2 + (v₅ - v₂)^2

theorem solution1_algebraic_core
    (x₁ x₂ x₃ x₄ x₅ : ℤ) :
    f x₁ x₂ (x₃ + x₄) (-x₄) (x₅ + x₄) - f x₁ x₂ x₃ x₄ x₅ =
    2 * (x₁ + x₂ + x₃ + x₄ + x₅) * x₄ := by
  
  -- Unfold the definition of the semi-invariant function
  dsimp [f]
  
  -- The identity is a pure polynomial equivalence, verifiable by ring
  ring

end IMO1986P3
