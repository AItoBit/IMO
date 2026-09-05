import Mathlib

open Real

/--
Formalization of the algebraic conclusion.
After setting up the geometry, the volume of the tetrahedron is bounded by
`(x / 6) * (1 - x^2 / 4)`, where `x` is the length of edge AB and `0 < x ≤ 1`.
We prove that this is at most `1 / 8`, and that this inequality is equivalent
to `(1 - x) * (3 - x - x^2) ≥ 0` exactly as stated in the solution.
-/
theorem imo1967_p2_solution_algebra (x : ℝ) (hx_pos : 0 < x) (hx_le : x ≤ 1) :
    (1 / 8 - (x / 6) * (1 - x^2 / 4) ≥ 0 ↔ (1 - x) * (3 - x - x^2) ≥ 0) ∧
    (x / 6) * (1 - x^2 / 4) ≤ 1 / 8 := by
  
  -- The algebraic expansion proving the equivalence stated in the solution text
  have h_eq : 1 / 8 - (x / 6) * (1 - x^2 / 4) = (1 - x) * (3 - x - x^2) / 24 := by
    ring
  
  have h_equiv : 1 / 8 - (x / 6) * (1 - x^2 / 4) ≥ 0 ↔ (1 - x) * (3 - x - x^2) ≥ 0 := by
    rw [h_eq]
    constructor
    · intro h; linarith
    · intro h; linarith

  -- Proving the factored form is non-negative using 0 < x ≤ 1
  have h_factor1 : 0 ≤ 1 - x := by 
    linarith
  
  have h_factor2 : 0 ≤ 3 - x - x^2 := by
    have hx0 : 0 ≤ x := by linarith
    -- Since 0 ≤ x ≤ 1, it follows that x^2 ≤ 1
    have hx2 : x^2 ≤ 1 := by nlinarith [hx0, hx_le]
    linarith
  
  -- The product of two non-negative factors is non-negative
  have h_prod : 0 ≤ (1 - x) * (3 - x - x^2) := mul_nonneg h_factor1 h_factor2
  
  -- Concluding the main volume bound via the equivalence
  have h_bound : (x / 6) * (1 - x^2 / 4) ≤ 1 / 8 := by
    have h_pos : 0 ≤ 1 / 8 - (x / 6) * (1 - x^2 / 4) := h_equiv.mpr h_prod
    linarith
    
  exact ⟨h_equiv, h_bound⟩
