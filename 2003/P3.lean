import Mathlib

open Real

/-- 
Formalization of the median step from IMO 2005 Problem 5:
"Suppose a triangle has side lengths a, b, c and the length of the median 
to the midpoint of side length c is m. Then applying the cosine rule twice 
we get m^2 = a^2/2 + b^2/2 - c^2/4. So if m^2 = 3/4 c^2, it follows that 
a^2 + b^2 = 2c^2. Similarly, b^2 + c^2 = 2a^2. Subtracting, a = c. 
Similarly for the other pairs of sides."
-/
lemma imo2005_p5_median_step (a b c m_a m_b m_c : ℝ)
  (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
  (hmc : m_c^2 = a^2 / 2 + b^2 / 2 - c^2 / 4)
  (hmc_val : m_c^2 = 3 / 4 * c^2)
  (hma : m_a^2 = b^2 / 2 + c^2 / 2 - a^2 / 4)
  (hma_val : m_a^2 = 3 / 4 * a^2)
  (hmb : m_b^2 = c^2 / 2 + a^2 / 2 - b^2 / 4)
  (hmb_val : m_b^2 = 3 / 4 * b^2) :
  a = b ∧ b = c := by
  -- Step 1: Derive the relation between the squares of the sides
  have h1 : a^2 + b^2 = 2 * c^2 := by linarith
  have h2 : b^2 + c^2 = 2 * a^2 := by linarith
  have h3 : c^2 + a^2 = 2 * b^2 := by linarith
  
  -- Step 2: Show the squares are equal
  have hab_sq : a^2 = b^2 := by linarith
  have hbc_sq : b^2 = c^2 := by linarith
  
  -- Step 3: Prove a = b from a^2 = b^2 and non-negativity
  have hab : a = b := by
    have h_mul : (a - b) * (a + b) = 0 := by
      calc (a - b) * (a + b) = a^2 - b^2 := by ring
      _ = 0 := by linarith
    cases mul_eq_zero.mp h_mul with
    | inl h_minus => linarith
    | inr h_plus => 
      have ha_zero : a = 0 := by linarith
      have hb_zero : b = 0 := by linarith
      linarith

  -- Step 4: Prove b = c from b^2 = c^2 and non-negativity
  have hbc : b = c := by
    have h_mul : (b - c) * (b + c) = 0 := by
      calc (b - c) * (b + c) = b^2 - c^2 := by ring
      _ = 0 := by linarith
    cases mul_eq_zero.mp h_mul with
    | inl h_minus => linarith
    | inr h_plus => 
      have hb_zero : b = 0 := by linarith
      have hc_zero : c = 0 := by linarith
      linarith

  -- Conclude the triangle is equilateral
  exact ⟨hab, hbc⟩
