import Mathlib

/-!
# IMO 1988, Problem 4 (Algebraic Core)

This formalizes the final algebraic and arithmetic deduction 

The problem reduces to finding the sum of the lengths of the intervals, 
which is given by `Σ r_i - Σ k`, where `k` ranges from 1 to 70.
We are given:
  1. `Σ k = 35 * 71`
  2. The polynomial leading coefficient `a_70 = 5`
  3. The polynomial `x^69` coefficient `a_69 = -5 * (Σ k) - 4 * (Σ k)`
  4. By Vieta's formulas, the sum of the roots `Σ r_i = -a_69 / a_70`

We prove that the total length `Σ r_i - Σ k` exactly equals 1988.
-/

namespace IMO1988P4

theorem sum_of_lengths_eq_1988 
    (sum_k sum_r a_70 a_69 : ℚ)
    (h_sum_k : sum_k = 35 * 71)
    (h_a70 : a_70 = 5)
    (h_a69 : a_69 = -5 * sum_k - 4 * sum_k)
    (h_vieta : sum_r = -a_69 / a_70) :
    sum_r - sum_k = 1988 := by
  
  -- Substitute the given definitions into the length formula
  calc sum_r - sum_k = (-a_69 / a_70) - sum_k := by rw [h_vieta]
    _ = (- (-5 * sum_k - 4 * sum_k) / 5) - sum_k := by rw [h_a69, h_a70]
    
    -- Simplify the algebraic expression
    _ = (9 * sum_k / 5) - sum_k := by ring
    
    -- Substitute the arithmetic value of the sum and evaluate
    _ = (9 * (35 * 71) / 5) - (35 * 71) := by rw [h_sum_k]
    _ = 1988 := by norm_num

end IMO1988P4
