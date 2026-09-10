import Mathlib

/-!
# IMO 1984, Problem 4 (Algebraic Core of Solution 2)

This formalizes the core algebraic equivalence from Solution 2 of p4 1984.pdf.
Let `M` and `N` be the midpoints of `AB` and `CD`.
Let `AM` be the radius of the circle on `AB`, and `DN` be the radius of the circle on `CD`.
Let `d_M` be the distance from `M` to `CD`, and `d_N` be the distance from `N` to `AB`.

The areas of triangles `AMN` and `DMN` are:
  [AMN] = (1 / 2) * AM * d_N
  [DMN] = (1 / 2) * DN * d_M

The condition that `CD` is tangent to the circle on `AB` means `d_M = AM`.
The condition that `AB` is tangent to the circle on `CD` means `d_N = DN`.
The geometric property `AD || BC` is equivalent to the area equality `[AMN] = [DMN]`.

We prove that given `d_M = AM`, the second tangency holds if and only if the areas are equal.
-/

namespace IMO1984P4

/-- The algebraic core of Solution 2. -/
theorem imo1984_p4_solution2_core
  (AM DN d_M d_N : ℝ)
  (hAM_pos : 0 < AM)
  (tangent_CD : d_M = AM) :
  d_N = DN ↔ (1 / 2 : ℝ) * AM * d_N = (1 / 2 : ℝ) * DN * d_M := by
  constructor
  · intro h_tangent_AB
    rw [tangent_CD, h_tangent_AB]
    ring
  · intro h_area
    rw [tangent_CD] at h_area
    -- Re-arrange the right side to match the left side's prefix
    have h1 : (1 / 2 : ℝ) * AM * d_N = (1 / 2 : ℝ) * AM * DN := by
      calc (1 / 2 : ℝ) * AM * d_N = (1 / 2 : ℝ) * DN * AM := h_area
        _ = (1 / 2 : ℝ) * AM * DN := by ring
    
    -- Prove the multiplicative factor is non-zero to enable cancellation
    have h2 : (1 / 2 : ℝ) * AM ≠ 0 := by positivity
    
    -- Cancel the (1/2) * AM from both sides
    exact mul_left_cancel₀ h2 h1

end IMO1984P4
