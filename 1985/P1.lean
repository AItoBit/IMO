import Mathlib

/-!
# IMO 1985, Problem 1 (Algebraic Core)

By evaluating the lengths of the tangent segments in terms of the circle's 
radius `r` and the angles at vertices `A` and `B`, we get:
  AD = r * cot A + r * tan (B / 2)
  BC = r * cot B + r * tan (A / 2)
  AB = r * csc A + r * csc B
  
To prove AD + BC = AB, we must algebraically verify the identity:
  cot θ + tan (θ / 2) = csc θ

We substitute the half-angle formulas:
  sin θ = 2xy
  cos θ = 2y² - 1
where x = sin(θ/2) and y = cos(θ/2), ensuring x² + y² = 1.
-/

namespace IMO1985P1

theorem imo1985_p1_algebraic_core
    (r xA yA xB yB : ℝ)
    (hA_unit : xA^2 + yA^2 = 1)
    (hB_unit : xB^2 + yB^2 = 1)
    (hxA : xA ≠ 0) (hyA : yA ≠ 0)
    (hxB : xB ≠ 0) (hyB : yB ≠ 0) :
    (r * ((2 * yA^2 - 1) / (2 * xA * yA)) + r * (xB / yB)) + 
    (r * ((2 * yB^2 - 1) / (2 * xB * yB)) + r * (xA / yA)) = 
    r * (1 / (2 * xA * yA)) + r * (1 / (2 * xB * yB)) := by
  
  -- Verify the identity for angle A
  have hA : ((2 * yA^2 - 1) / (2 * xA * yA)) + xA / yA = 1 / (2 * xA * yA) := by
    have h1 : xA / yA = (2 * xA^2) / (2 * xA * yA) := by
      rw [div_eq_div_iff hyA (mul_ne_zero (mul_ne_zero (by norm_num) hxA) hyA)]
      ring
    rw [h1, ← add_div]
    have h2 : 2 * yA^2 - 1 + 2 * xA^2 = 1 := by
      calc 2 * yA^2 - 1 + 2 * xA^2 = 2 * (xA^2 + yA^2) - 1 := by ring
        _ = 2 * (1) - 1 := by rw [hA_unit]
        _ = 1 := by ring
    rw [h2]
  
  -- Verify the identity for angle B
  have hB : ((2 * yB^2 - 1) / (2 * xB * yB)) + xB / yB = 1 / (2 * xB * yB) := by
    have h1 : xB / yB = (2 * xB^2) / (2 * xB * yB) := by
      rw [div_eq_div_iff hyB (mul_ne_zero (mul_ne_zero (by norm_num) hxB) hyB)]
      ring
    rw [h1, ← add_div]
    have h2 : 2 * yB^2 - 1 + 2 * xB^2 = 1 := by
      calc 2 * yB^2 - 1 + 2 * xB^2 = 2 * (xB^2 + yB^2) - 1 := by ring
        _ = 2 * (1) - 1 := by rw [hB_unit]
        _ = 1 := by ring
    rw [h2]
    
  -- Combine the evaluated segments
  calc (r * ((2 * yA^2 - 1) / (2 * xA * yA)) + r * (xB / yB)) + 
       (r * ((2 * yB^2 - 1) / (2 * xB * yB)) + r * (xA / yA))
    _ = r * (((2 * yA^2 - 1) / (2 * xA * yA)) + xA / yA) + 
        r * (((2 * yB^2 - 1) / (2 * xB * yB)) + xB / yB) := by ring
    _ = r * (1 / (2 * xA * yA)) + r * (1 / (2 * xB * yB)) := by rw [hA, hB]

end IMO1985P1
