import Mathlib

open Real

/-- Formalization of the system derivation.
Assume `a₁ > a₂ > a₃ > a₄` (so all absolute values become signed differences)
and that the three linear relations obtained by pairwise subtraction hold:
  -x₁ + x₂ + x₃ + x₄ = 0
  -x₁ - x₂ - x₃ + x₄ = 0
  -x₁ - x₂ + x₃ + x₄ = 0
Then `x₂ = x₃ = 0`, hence `x₁ = x₄`, and substituting back gives
`x₁ = x₄ = 1/(a₁-a₄)`. -/
theorem system_solution
    (a1 a2 a3 a4 x1 x2 x3 x4 : ℝ)
    (ha : a1 > a2 ∧ a2 > a3 ∧ a3 > a4)
    (h0 : (a1 - a2) * x2 + (a1 - a3) * x3 + (a1 - a4) * x4 = 1)
    (h1 : -x1 + x2 + x3 + x4 = 0)
    (h2 : -x1 - x2 - x3 + x4 = 0)
    (h3 : -x1 - x2 + x3 + x4 = 0)
    (_hneq : a1 ≠ a4) :
    x2 = 0 ∧ x3 = 0 ∧ x1 = x4 ∧ x1 = 1 / (a1 - a4) := by
  -- Add the three equations pairwise to isolate variables
  have eq12 : 2 * x4 - 2 * x1 + (x2 + x3 - x2 - x3) = 0 := by linarith [h1, h2]
  have eq13 : 2 * x4 - 2 * x1 + (x3 - x3 + x2 - x2) = 0 := by linarith [h1, h3]
  have eq23 : 2 * x4 - 2 * x1 + (-x3 - x3 + x2 - x2) = 0 := by linarith [h2, h3]

  -- From h1+h2:  -2x1 + 2x4 = 0  => x1 = x4
  have h_x1_x4 : x1 = x4 := by
    have : -x1 + x4 + (x1 - x1) + (x2 - x2) + (x3 - x3) = 0 := by linarith [h1, h2]
    linarith

  -- Substitute x1 = x4 into h1 => x2 + x3 = 0
  have h_x2_x3 : x2 + x3 = 0 := by
    linarith [h_x1_x4, h1]

  -- Substitute x1 = x4 into h2 => -x2 - x3 = 0 => x2 = -x3
  have h_x2_neg_x3 : x2 = -x3 := by
    linarith [h_x1_x4, h2]

  -- Hence x2 = x3 = 0
  have h_x2_0 : x2 = 0 := by
    linarith [h_x2_neg_x3, h_x2_x3]

  have h_x3_0 : x3 = 0 := by 
    linarith [h_x2_0, h_x2_x3]

  -- So x1 = x4 remains; now use original equation (e.g. (a1-a4)x1 = 1)
  have h_x1_val : x1 = 1 / (a1 - a4) := by
    -- The first derived relation gives (a1-a4)·x1 = 1
    have h_eq : (a1 - a4) * x1 = 1 := by
      calc (a1 - a4) * x1 = (a1 - a2) * 0 + (a1 - a3) * 0 + (a1 - a4) * x4 := by
            rw [← h_x1_x4]
            ring
        _ = (a1 - a2) * x2 + (a1 - a3) * x3 + (a1 - a4) * x4 := by rw [h_x2_0, h_x3_0]
        _ = 1 := h0
    
    -- Verify the denominator isn't 0 and rearrange the equivalence
    have hd : a1 - a4 ≠ 0 := by linarith [ha.1, ha.2.1, ha.2.2]
    calc x1 = x1 * (a1 - a4) / (a1 - a4) := (mul_div_cancel_right₀ x1 hd).symm
         _ = (a1 - a4) * x1 / (a1 - a4) := by rw [mul_comm]
         _ = 1 / (a1 - a4) := by rw [h_eq]

  exact ⟨h_x2_0, h_x3_0, h_x1_x4, h_x1_val⟩
