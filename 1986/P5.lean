import Mathlib

/-!
# IMO 1986, Problem 5 (Algebraic Core of Solution 2)

For `0 ≤ y < 2`, we let `F = f(y)`. The functional equation and the 
root condition `f(x) = 0 ↔ x ≥ 2` yield two strict inequalities:
1. `2 ≤ (2 - y) * F`
2. `2 ≤ y + 2 / F`

We prove algebraically that these strict conditions force `F = 2 / (2 - y)`.
-/

namespace IMO1986P5

theorem solution2_bounds (y F : ℝ)
    (hy1 : 0 ≤ y) (hy2 : y < 2)
    (hF_pos : 0 < F)
    (h_lower : 2 ≤ (2 - y) * F)
    (h_upper : 2 ≤ y + 2 / F) :
    F = 2 / (2 - y) := by
  
  -- Establish that the denominator is strictly positive
  have hy_pos : 0 < 2 - y := by linarith

  -- Prove the lower bound: 2 / (2 - y) ≤ F
  have h1 : 2 / (2 - y) ≤ F := by
    rw [div_le_iff₀ hy_pos]
    calc 2 ≤ (2 - y) * F := h_lower
         _ = F * (2 - y) := by ring

  -- Prove the upper bound: F ≤ 2 / (2 - y)
  have h2 : F ≤ 2 / (2 - y) := by
    -- Rearrange the addition inequality
    have step1 : 2 - y ≤ 2 / F := by linarith [h_upper]
    
    -- Multiply both sides of both inequalities by their respective positive denominators
    rw [le_div_iff₀ hy_pos]
    rw [le_div_iff₀ hF_pos] at step1
    
    calc F * (2 - y) = (2 - y) * F := by ring
      _ ≤ 2 := step1

  -- Combine the bounds to prove strict equality
  exact le_antisymm h2 h1

end IMO1986P5
