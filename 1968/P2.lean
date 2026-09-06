import Mathlib

/--

Let P be the product of the digits of a natural number x. We have the constraints:
1. P ≤ x (a known property of the digit product for natural numbers)
2. P ≥ 0 (since digits are non-negative)
3. P = x^2 - 10x - 22 (from the problem statement)

We prove that these constraints uniquely determine x = 12 and P = 2.
-/
theorem digit_product_equation (x P : ℤ)
    (hP_le_x : P ≤ x)
    (hP_nonneg : 0 ≤ P)
    (h_eq : P = x^2 - 10 * x - 22) :
    x = 12 ∧ P = 2 := by
  have h1 : x^2 - 11 * x - 22 ≤ 0 := by linarith
  have h2 : 0 ≤ x^2 - 10 * x - 22 := by linarith

  -- Bound x from above
  have h_upper : x ≤ 12 := by
    by_contra h_gt
    have h13 : x ≥ 13 := by omega
    have h_step : (x - 13) * x ≥ 0 := by
      have hA : x - 13 ≥ 0 := by omega
      have hB : x ≥ 0 := by omega
      nlinarith
    have h_contra : x^2 - 11 * x - 22 > 0 := by
      calc x^2 - 11 * x - 22 = (x - 13) * x + 2 * x - 22 := by ring
      _ > 0 := by linarith [h_step, h13]
    linarith

  -- Bound x from below
  have h_lower : x ≥ 12 := by
    by_contra h_lt
    have h11 : x ≤ 11 := by omega
    have hx_nonneg : x ≥ 0 := by omega
    have h_fac : (x - 11) * (x + 1) ≤ 0 := by
      have hA : x - 11 ≤ 0 := by omega
      have hB : x + 1 ≥ 0 := by omega
      nlinarith
    have h_contra : x^2 - 10 * x - 22 < 0 := by
      calc x^2 - 10 * x - 22 = (x - 11) * (x + 1) - 11 := by ring
      _ < 0 := by linarith [h_fac]
    linarith

  -- x is forced to be exactly 12
  have hx12 : x = 12 := by omega

  -- Evaluate P given x = 12
  have hP2 : P = 2 := by
    calc P = x^2 - 10 * x - 22 := h_eq
         _ = 12^2 - 10 * 12 - 22 := by rw [hx12]
         _ = 2 := by norm_num

  exact ⟨hx12, hP2⟩
