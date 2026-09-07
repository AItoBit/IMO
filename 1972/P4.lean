/-
# IMO 1972, Problem 4

Find all solutions `(x₁, x₂, x₃, x₄, x₅)` of positive reals of the system

  `(x₁² - x₃x₅)(x₂² - x₃x₅) ≤ 0`
  `(x₂² - x₄x₁)(x₃² - x₄x₁) ≤ 0`
  `(x₃² - x₅x₂)(x₄² - x₅x₂) ≤ 0`
  `(x₄² - x₁x₃)(x₅² - x₁x₃) ≤ 0`
  `(x₅² - x₂x₄)(x₁² - x₂x₄) ≤ 0`

"Find all solutions" is formalized as an `iff`: the system holds exactly when
`x₁ = x₂ = x₃ = x₄ = x₅`.

## Proof

Twice the sum of the five left-hand sides equals a sum of ten squares:

  `2 ∑ = ∑ᵢ xᵢ² (xᵢ₊₁ - xᵢ₊₃)² + ∑ᵢ xᵢ² (xᵢ₊₂ - xᵢ₊₄)²`   (indices mod 5),

which `ring` verifies (`key` below).  If the system holds the right-hand side is
`≤ 0`, and each summand is `≥ 0`, so each summand vanishes.  Since the `xᵢ` are
positive, the first four give `x₂ = x₄`, `x₃ = x₅`, `x₄ = x₁`, `x₅ = x₂`, and
hence all five are equal.

The converse is immediate: when all the variables agree, every factor is `0`.
-/

import Mathlib

namespace Imo1972P4

/-- From `a² * b² = 0` with `a > 0` we get `b = 0`. -/
private lemma eq_zero_of_sq_mul_sq {a b : ℝ} (ha : 0 < a) (h : a ^ 2 * b ^ 2 = 0) : b = 0 := by
  rcases mul_eq_zero.mp h with h' | h'
  · exact absurd h' (pow_ne_zero 2 ha.ne')
  · exact sq_eq_zero_iff.mp h'

/-- The algebraic identity behind the solution: twice the sum of the five
left-hand sides is a sum of ten squares. -/
private lemma key (x₁ x₂ x₃ x₄ x₅ : ℝ) :
    x₁ ^ 2 * (x₂ - x₄) ^ 2 + x₂ ^ 2 * (x₃ - x₅) ^ 2 + x₃ ^ 2 * (x₄ - x₁) ^ 2
      + x₄ ^ 2 * (x₅ - x₂) ^ 2 + x₅ ^ 2 * (x₁ - x₃) ^ 2
      + x₁ ^ 2 * (x₃ - x₅) ^ 2 + x₂ ^ 2 * (x₄ - x₁) ^ 2 + x₃ ^ 2 * (x₅ - x₂) ^ 2
      + x₄ ^ 2 * (x₁ - x₃) ^ 2 + x₅ ^ 2 * (x₂ - x₄) ^ 2
    = 2 * ((x₁ ^ 2 - x₃ * x₅) * (x₂ ^ 2 - x₃ * x₅)
         + (x₂ ^ 2 - x₄ * x₁) * (x₃ ^ 2 - x₄ * x₁)
         + (x₃ ^ 2 - x₅ * x₂) * (x₄ ^ 2 - x₅ * x₂)
         + (x₄ ^ 2 - x₁ * x₃) * (x₅ ^ 2 - x₁ * x₃)
         + (x₅ ^ 2 - x₂ * x₄) * (x₁ ^ 2 - x₂ * x₄)) := by
  ring

/-- **IMO 1972, Problem 4.**  The only positive solutions of the system are the
constant ones. -/
theorem imo1972_p4 (x₁ x₂ x₃ x₄ x₅ : ℝ)
    (h₁ : 0 < x₁) (h₂ : 0 < x₂) (h₃ : 0 < x₃) (h₄ : 0 < x₄) (h₅ : 0 < x₅) :
    ((x₁ ^ 2 - x₃ * x₅) * (x₂ ^ 2 - x₃ * x₅) ≤ 0 ∧
     (x₂ ^ 2 - x₄ * x₁) * (x₃ ^ 2 - x₄ * x₁) ≤ 0 ∧
     (x₃ ^ 2 - x₅ * x₂) * (x₄ ^ 2 - x₅ * x₂) ≤ 0 ∧
     (x₄ ^ 2 - x₁ * x₃) * (x₅ ^ 2 - x₁ * x₃) ≤ 0 ∧
     (x₅ ^ 2 - x₂ * x₄) * (x₁ ^ 2 - x₂ * x₄) ≤ 0)
    ↔ (x₁ = x₂ ∧ x₁ = x₃ ∧ x₁ = x₄ ∧ x₁ = x₅) := by
  constructor
  · rintro ⟨e₁, e₂, e₃, e₄, e₅⟩
    -- the sum of the ten squares is `≤ 0`
    have hsum : x₁ ^ 2 * (x₂ - x₄) ^ 2 + x₂ ^ 2 * (x₃ - x₅) ^ 2 + x₃ ^ 2 * (x₄ - x₁) ^ 2
        + x₄ ^ 2 * (x₅ - x₂) ^ 2 + x₅ ^ 2 * (x₁ - x₃) ^ 2
        + x₁ ^ 2 * (x₃ - x₅) ^ 2 + x₂ ^ 2 * (x₄ - x₁) ^ 2 + x₃ ^ 2 * (x₅ - x₂) ^ 2
        + x₄ ^ 2 * (x₁ - x₃) ^ 2 + x₅ ^ 2 * (x₂ - x₄) ^ 2 ≤ 0 := by
      rw [key]
      linarith
    -- every summand is nonnegative
    have n1 : (0:ℝ) ≤ x₁ ^ 2 * (x₂ - x₄) ^ 2 := by positivity
    have n2 : (0:ℝ) ≤ x₂ ^ 2 * (x₃ - x₅) ^ 2 := by positivity
    have n3 : (0:ℝ) ≤ x₃ ^ 2 * (x₄ - x₁) ^ 2 := by positivity
    have n4 : (0:ℝ) ≤ x₄ ^ 2 * (x₅ - x₂) ^ 2 := by positivity
    have n5 : (0:ℝ) ≤ x₅ ^ 2 * (x₁ - x₃) ^ 2 := by positivity
    have n6 : (0:ℝ) ≤ x₁ ^ 2 * (x₃ - x₅) ^ 2 := by positivity
    have n7 : (0:ℝ) ≤ x₂ ^ 2 * (x₄ - x₁) ^ 2 := by positivity
    have n8 : (0:ℝ) ≤ x₃ ^ 2 * (x₅ - x₂) ^ 2 := by positivity
    have n9 : (0:ℝ) ≤ x₄ ^ 2 * (x₁ - x₃) ^ 2 := by positivity
    have n10 : (0:ℝ) ≤ x₅ ^ 2 * (x₂ - x₄) ^ 2 := by positivity
    -- hence each of them vanishes
    have z1 : x₁ ^ 2 * (x₂ - x₄) ^ 2 = 0 := by linarith
    have z2 : x₂ ^ 2 * (x₃ - x₅) ^ 2 = 0 := by linarith
    have z3 : x₃ ^ 2 * (x₄ - x₁) ^ 2 = 0 := by linarith
    have z4 : x₄ ^ 2 * (x₅ - x₂) ^ 2 = 0 := by linarith
    have d1 : x₂ - x₄ = 0 := eq_zero_of_sq_mul_sq h₁ z1
    have d2 : x₃ - x₅ = 0 := eq_zero_of_sq_mul_sq h₂ z2
    have d3 : x₄ - x₁ = 0 := eq_zero_of_sq_mul_sq h₃ z3
    have d4 : x₅ - x₂ = 0 := eq_zero_of_sq_mul_sq h₄ z4
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith [sq_nonneg x₁]

end Imo1972P4
