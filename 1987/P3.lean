import Mathlib

/-!
# IMO 1987, Problem 3 (Algebraic Core of Solution 2)

This formalizes the Cauchy-Schwarz bounding deduction 

Given the abstracted sums:
  S_a = Σ a_i^2
  S_x = Σ x_i^2
  S_ax = Σ a_i |x_i|

By Cauchy-Schwarz, S_ax^2 ≤ S_a * S_x.
We are given the condition S_x = 1, and the maximum absolute value
of a_i is (k - 1), meaning S_a ≤ n * (k - 1)^2.

We prove algebraically that these conditions strictly force:
S_ax ≤ √n * (k - 1).
-/

namespace IMO1987P3

theorem solution2_codomain_bound
    (S_a S_x S_ax n k : ℝ)
    (h_CS : S_ax^2 ≤ S_a * S_x)
    (h_Sx : S_x = 1)
    (h_Sa : S_a ≤ n * (k - 1)^2)
    (hn : 0 ≤ n)
    (hk : 1 ≤ k)
    (h_Sax_nonneg : 0 ≤ S_ax) :
    S_ax ≤ Real.sqrt n * (k - 1) := by

  -- Step 1: Establish S_ax^2 <= n * (k - 1)^2
  have h1 : S_ax^2 ≤ n * (k - 1)^2 := by
    calc S_ax^2 ≤ S_a * S_x := h_CS
      _ = S_a * 1 := by rw [h_Sx]
      _ = S_a := by ring
      _ ≤ n * (k - 1)^2 := h_Sa

  -- Step 2: Set up the bounding target and ensure non-negativity
  have hk_sub : 0 ≤ k - 1 := by linarith
  have hB_nonneg : 0 ≤ Real.sqrt n * (k - 1) := mul_nonneg (Real.sqrt_nonneg n) hk_sub

  -- Step 3: Expand the square of the target bound
  have hB_sq : (Real.sqrt n * (k - 1))^2 = n * (k - 1)^2 := by
    calc (Real.sqrt n * (k - 1))^2 = (Real.sqrt n)^2 * (k - 1)^2 := by ring
      _ = n * (k - 1)^2 := by rw [Real.sq_sqrt hn]

  -- Step 4: Relate the squared terms
  have h2 : S_ax^2 ≤ (Real.sqrt n * (k - 1))^2 := by
    calc S_ax^2 ≤ n * (k - 1)^2 := h1
      _ = (Real.sqrt n * (k - 1))^2 := hB_sq.symm

  -- Step 5: Extract the square root to finalize the deduction
  have h3 : Real.sqrt (S_ax^2) ≤ Real.sqrt ((Real.sqrt n * (k - 1))^2) := Real.sqrt_le_sqrt h2
  rw [Real.sqrt_sq h_Sax_nonneg, Real.sqrt_sq hB_nonneg] at h3

  exact h3

end IMO1987P3
