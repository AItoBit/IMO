import Mathlib

open Real

/-
Formalization of the algebraic core of the solution".
The solution relies on the area/perimeter identity of the right triangle and 
the calculation of the collinearity of the centers based on the radii relations.
-/

/-- The identity used to calculate the inradius r of the right triangle -/
lemma imo1969_p4_area_identity (a b c : ℝ) (h_pythagoras : a^2 + b^2 = c^2) :
    (a + b + c) * (a + b - c) = 2 * a * b := by
  calc (a + b + c) * (a + b - c)
    _ = a^2 + 2 * a * b + b^2 - c^2 := by ring
    _ = (a^2 + b^2) + 2 * a * b - c^2 := by ring
    _ = c^2 + 2 * a * b - c^2 := by rw [h_pythagoras]
    _ = 2 * a * b := by ring

/-- The proof that the arithmetic mean of r₂ and r₃ is exactly the inradius r -/
theorem imo1969_p4_radii (a b c r r₂ r₃ : ℝ)
    (hc : c ≠ 0)
    (h_pythagoras : a^2 + b^2 = c^2)
    (hr : r = (a + b - c) / 2)
    (hr₂ : r₂ = a - a^2 / c)
    (hr₃ : r₃ = b - b^2 / c) :
    (r₂ + r₃) / 2 = r := by
  -- Substitute the given definitions of the radii
  rw [hr, hr₂, hr₃]
  
  -- Group the terms algebraically over the common denominator c
  have h1 : a - a^2 / c + (b - b^2 / c) = a + b - (a^2 + b^2) / c := by ring
  
  calc (a - a^2 / c + (b - b^2 / c)) / 2
    _ = (a + b - (a^2 + b^2) / c) / 2 := by rw [h1]
    _ = (a + b - c^2 / c) / 2 := by rw [h_pythagoras]
    _ = (a + b - c) / 2 := by
      -- Simplify c^2 / c to c
      have h2 : c^2 / c = c := by
        calc c^2 / c = (c * c) / c := by rw [sq]
        _ = c := mul_div_cancel_right₀ c hc
      rw [h2]
