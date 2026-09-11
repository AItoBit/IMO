import Mathlib

/-!
# IMO 1987, Problem 2 (Algebraic Core of Solution 4)
 

From geometric similarities, the ratio of the side lengths is established as:
  KM / BC = AL / AN

The area of the quadrilateral AKNM is given by:
  Area(AKNM) = (1 / 2) * KM * AN

The area of the triangle ABC is given by:
  Area(ABC) = (1 / 2) * BC * AL

We prove that the similarity ratio directly forces the equality of the two areas.
-/

namespace IMO1987P2

theorem solution4_area_equality
    (KM BC AL AN Area_AKNM Area_ABC : ℝ)
    (h_BC_pos : BC ≠ 0)
    (h_AN_pos : AN ≠ 0)
    (h_ratio : KM / BC = AL / AN)
    (h_area_quad : Area_AKNM = (1 / 2) * KM * AN)
    (h_area_tri : Area_ABC = (1 / 2) * BC * AL) :
    Area_AKNM = Area_ABC := by
  
  -- Step 1: Cross-multiply the similarity ratio
  have h_cross : KM * AN = BC * AL := by
    -- Multiply both sides by BC and AN
    calc KM * AN = (KM / BC) * BC * AN := by
           rw [div_mul_cancel₀ _ h_BC_pos]
         _ = (AL / AN) * BC * AN := by rw [h_ratio]
         _ = (AL / AN) * AN * BC := by ring
         _ = AL * BC := by rw [div_mul_cancel₀ _ h_AN_pos]
         _ = BC * AL := by ring

  -- Step 2: Substitute the cross-multiplied identity into the area formulas
  calc Area_AKNM = (1 / 2) * (KM * AN) := by
         have h_assoc : (1 / 2 : ℝ) * KM * AN = (1 / 2 : ℝ) * (KM * AN) := by ring
         rw [h_area_quad, h_assoc]
       _ = (1 / 2) * (BC * AL) := by rw [h_cross]
       _ = (1 / 2) * BC * AL := by ring
       _ = Area_ABC := h_area_tri.symm

end IMO1987P2
