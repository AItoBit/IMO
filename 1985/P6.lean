import Mathlib

/-!
# IMO 1985, Problem 6 (Algebraic Core of Solution 1)

This formalizes the uniqueness bound .
If two sequences x_n and y_n satisfy the problem's recursive relation
and the lower bound x_n >= 1 - 1/n, their difference must strictly grow.
-/

namespace IMO1985P6

theorem uniqueness_step (n xn yn : ℝ)
  (hn : 1 ≤ n)
  (h_order : xn ≤ yn)
  (hx : 1 - 1 / n ≤ xn) :
  yn * (yn + 1 / n) - xn * (xn + 1 / n) ≥ yn - xn := by
  
  -- Factor the difference of the recursive evaluations
  have h1 : yn * (yn + 1 / n) - xn * (xn + 1 / n) = (yn - xn) * (yn + xn + 1 / n) := by ring
  
  -- Establish positivity of n to safely handle division inequalities
  have hn_pos : 0 < n := by linarith
  
  -- Prove that 1/n <= 1 given n >= 1
  have h2 : 1 / n ≤ 1 := by
    rw [div_le_iff₀ hn_pos]
    linarith
    
  -- Isolate the bounds of the two polynomial factors
  have h_diff : 0 ≤ yn - xn := by linarith
  have h_sum : 1 ≤ yn + xn + 1 / n := by linarith
  
  -- nlinarith leverages the non-negative products: 
  -- (yn - xn) >= 0 and (yn + xn + 1/n - 1) >= 0
  nlinarith

end IMO1985P6
