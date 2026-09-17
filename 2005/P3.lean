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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Imo2005P3

/-- Cauchy–Schwarz style estimate: for positive reals,
`(x² + y² + z²)² ≤ (x⁵ + y² + z²) * (1/x + y² + z²)`.
Equivalently, the difference equals `(y² + z²) * (x³ - 1)² / x ≥ 0`. -/
lemma sq_sum_sq_le_mul (x y z : ℝ) (hx : 0 < x) :
    (x ^ 2 + y ^ 2 + z ^ 2) ^ 2 ≤ (x ^ 5 + y ^ 2 + z ^ 2) * (1 / x + y ^ 2 + z ^ 2) := by
  rw [← sub_nonneg]
  have hkey : (x ^ 5 + y ^ 2 + z ^ 2) * (1 / x + y ^ 2 + z ^ 2) - (x ^ 2 + y ^ 2 + z ^ 2) ^ 2
      = (y ^ 2 + z ^ 2) * (x ^ 3 - 1) ^ 2 / x := by
    field_simp
    ring
  rw [hkey]
  positivity

/-- The single-variable estimate:
`(x⁵ - x²)/(x⁵ + y² + z²) ≥ 1 - (1/x + y² + z²)/(x² + y² + z²)`. -/
lemma term_bound (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    1 - (1 / x + y ^ 2 + z ^ 2) / (x ^ 2 + y ^ 2 + z ^ 2)
      ≤ (x ^ 5 - x ^ 2) / (x ^ 5 + y ^ 2 + z ^ 2) := by
  have hd : (0 : ℝ) < x ^ 5 + y ^ 2 + z ^ 2 := by positivity
  have hs : (0 : ℝ) < x ^ 2 + y ^ 2 + z ^ 2 := by positivity
  have h1 := sq_sum_sq_le_mul x y z hx
  have h2 : (x ^ 2 + y ^ 2 + z ^ 2) / (x ^ 5 + y ^ 2 + z ^ 2)
      ≤ (1 / x + y ^ 2 + z ^ 2) / (x ^ 2 + y ^ 2 + z ^ 2) := by
    rw [div_le_div_iff₀ hd hs]
    nlinarith [h1]
  have h3 : (x ^ 5 - x ^ 2) / (x ^ 5 + y ^ 2 + z ^ 2)
      = 1 - (x ^ 2 + y ^ 2 + z ^ 2) / (x ^ 5 + y ^ 2 + z ^ 2) := by
    field_simp
    ring
  rw [h3]
  linarith

/-- From `xyz ≥ 1` and positivity: `1/x + 1/y + 1/z ≤ x² + y² + z²`. -/
lemma inv_sum_le_sq_sum (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : 1 ≤ x * y * z) : 1 / x + 1 / y + 1 / z ≤ x ^ 2 + y ^ 2 + z ^ 2 := by
  have hinvx : 1 / x ≤ y * z := by
    rw [div_le_iff₀ hx]; nlinarith
  have hinvy : 1 / y ≤ x * z := by
    rw [div_le_iff₀ hy]; nlinarith
  have hinvz : 1 / z ≤ x * y := by
    rw [div_le_iff₀ hz]; nlinarith
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (x - z)]

/-- **IMO 2005, Problem 3.** For positive reals `x, y, z` with `xyz ≥ 1`,
`(x⁵ - x²)/(x⁵ + y² + z²) + (y⁵ - y²)/(x² + y⁵ + z²) + (z⁵ - z²)/(x² + y² + z⁵) ≥ 0`. -/
theorem imo2005_p3 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : 1 ≤ x * y * z) :
    0 ≤ (x ^ 5 - x ^ 2) / (x ^ 5 + y ^ 2 + z ^ 2)
      + (y ^ 5 - y ^ 2) / (x ^ 2 + y ^ 5 + z ^ 2)
      + (z ^ 5 - z ^ 2) / (x ^ 2 + y ^ 2 + z ^ 5) := by
  have hs : (0 : ℝ) < x ^ 2 + y ^ 2 + z ^ 2 := by positivity
  have hbx := term_bound x y z hx hy hz
  have hby := term_bound y x z hy hx hz
  have hbz := term_bound z x y hz hx hy
  have ey : (x ^ 2 + y ^ 5 + z ^ 2) = y ^ 5 + x ^ 2 + z ^ 2 := by ring
  have ez : (x ^ 2 + y ^ 2 + z ^ 5) = z ^ 5 + x ^ 2 + y ^ 2 := by ring
  have esy : (y ^ 2 + x ^ 2 + z ^ 2) = x ^ 2 + y ^ 2 + z ^ 2 := by ring
  have esz : (z ^ 2 + x ^ 2 + y ^ 2) = x ^ 2 + y ^ 2 + z ^ 2 := by ring
  rw [ey, ez]
  rw [esy] at hby
  rw [esz] at hbz
  -- the three lower bounds add up to `1 - (1/x + 1/y + 1/z)/(x² + y² + z²)`
  have hsum : (1 / x + y ^ 2 + z ^ 2) / (x ^ 2 + y ^ 2 + z ^ 2)
      + (1 / y + x ^ 2 + z ^ 2) / (x ^ 2 + y ^ 2 + z ^ 2)
      + (1 / z + x ^ 2 + y ^ 2) / (x ^ 2 + y ^ 2 + z ^ 2)
      = (1 / x + 1 / y + 1 / z) / (x ^ 2 + y ^ 2 + z ^ 2) + 2 := by
    field_simp
    ring
  have hfin : (1 / x + 1 / y + 1 / z) / (x ^ 2 + y ^ 2 + z ^ 2) ≤ 1 := by
    rw [div_le_one hs]
    exact inv_sum_le_sq_sum x y z hx hy hz h
  linarith

end Imo2005P3
