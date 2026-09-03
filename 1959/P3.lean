import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

/-- The leading coefficient of the quadratic in `cos (2 * x)`. -/
def imo1959P3F₀ (a _b _c : ℝ) : ℝ := a ^ 2

/-- The linear coefficient of the quadratic in `cos (2 * x)`. -/
def imo1959P3F₁ (a b c : ℝ) : ℝ := 2 * a ^ 2 + 4 * a * c - 2 * b ^ 2

/-- The constant coefficient of the quadratic in `cos (2 * x)`. -/
def imo1959P3F₂ (a b c : ℝ) : ℝ := a ^ 2 + 4 * a * c + 4 * c ^ 2 - 2 * b ^ 2

-- note: https://artofproblemsolving.com/community/c6h54819p27098808  suggests that the question should be "whose roots include" rather than "whose roots are the same as", otherwise $a = b = 1, c = 0$ is a counterexample. As a result we use `→` not `↔`.
/--
Let $a,b,c$ be real numbers. Given the equation for $\cos x$: $$a\cos^2x+b\cos x+c=0,$$ form a quadratic equation in $\cos{2x}$ whose roots are the same values of $x$. Compare the equations in $\cos x$ and $\cos{2x}$ for $a=4,b=2,c=-1$. -/
theorem imo_1959_p3 :
    ∃ f₀ f₁ f₂ : ℝ → ℝ → ℝ → ℝ,
      ∀ (a b c x : ℝ) (_h : a ≠ 0),
        f₀ a b c ≠ 0 ∧
          (a * Real.cos x ^ 2 + b * Real.cos x + c = 0 →
            f₀ a b c * Real.cos (2 * x) ^ 2 + f₁ a b c * Real.cos (2 * x) + f₂ a b c = 0) := by
  refine ⟨imo1959P3F₀, imo1959P3F₁, imo1959P3F₂, fun a b c x ha => ⟨?_, fun hx => ?_⟩⟩
  · simpa [imo1959P3F₀] using pow_ne_zero 2 ha
  · have h2 : Real.cos (2 * x) = 2 * Real.cos x ^ 2 - 1 := Real.cos_two_mul x
    simp only [imo1959P3F₀, imo1959P3F₁, imo1959P3F₂, h2]
    linear_combination (4 * (a * Real.cos x ^ 2 - b * Real.cos x + c)) * hx

/-- Comparison for `a = 4`, `b = 2`, `c = -1`: after dividing by the common factor `4`, the
equation in `cos (2 * x)` is `4 * y ^ 2 + 2 * y - 1 = 0`, i.e. exactly the same quadratic as the
original one in `cos x`. -/
theorem imo_1959_p3_special_case (y : ℝ) :
    imo1959P3F₀ 4 2 (-1) * y ^ 2 + imo1959P3F₁ 4 2 (-1) * y + imo1959P3F₂ 4 2 (-1)
      = 4 * (4 * y ^ 2 + 2 * y - 1) := by
  simp only [imo1959P3F₀, imo1959P3F₁, imo1959P3F₂]
  ring
