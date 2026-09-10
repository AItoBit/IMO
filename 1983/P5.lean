import Mathlib

/-!
# IMO 1984, Problem B2 (Coordinate Algebra)

Formalization of the algebraic system arising from the coordinate geometry
solution to IMO 1984 Problem B2, as presented in the reference text.

The text establishes a system of equations by comparing the coordinates of 
points M and N on the lines. 
Here, `s3` represents `√3`. We prove that this system uniquely forces `r^2 = 1/3`.
-/

namespace IMO1984B2

theorem imo1984_b2_coordinate_algebra
  (x k1 k2 r s3 : ℝ)
  (hs3 : s3 ≠ 0)
  (hM_x : k1 + (1 - k1) * x = 3 * r / 2)
  (hM_y : k1 * s3 = (1 - r) * s3 + r * s3 / 2)
  (hN_x : k2 + (1 - k2) * x = 3 * (1 - r) / 2)
  (hN_y : k2 * s3 = (1 - r) * s3 / 2) :
  r^2 = 1 / 3 := by
  
  -- 1. Extract k1 in terms of r from the y-coordinate of M
  have hH1 : k1 - (1 - r / 2) = 0 := by
    have h_mult : (k1 - (1 - r / 2)) * s3 = 0 := by
      calc (k1 - (1 - r / 2)) * s3 = k1 * s3 - (1 - r) * s3 - r * s3 / 2 := by ring
        _ = ((1 - r) * s3 + r * s3 / 2) - (1 - r) * s3 - r * s3 / 2 := by rw [hM_y]
        _ = 0 := by ring
    cases mul_eq_zero.mp h_mult with
    | inl h => exact h
    | inr h => exact False.elim (hs3 h)

  -- 2. Extract k2 in terms of r from the y-coordinate of N
  have hH3 : k2 - (1 - r) / 2 = 0 := by
    have h_mult : (k2 - (1 - r) / 2) * s3 = 0 := by
      calc (k2 - (1 - r) / 2) * s3 = k2 * s3 - (1 - r) * s3 / 2 := by ring
        _ = (1 - r) * s3 / 2 - (1 - r) * s3 / 2 := by rw [hN_y]
        _ = 0 := by ring
    cases mul_eq_zero.mp h_mult with
    | inl h => exact h
    | inr h => exact False.elim (hs3 h)

  -- 3. Rearrange the x-coordinate equations to equal 0
  have hH2 : k1 + (1 - k1) * x - 3 * r / 2 = 0 := by
    calc k1 + (1 - k1) * x - 3 * r / 2 = (3 * r / 2) - 3 * r / 2 := by rw [hM_x]
      _ = 0 := by ring

  have hH4 : k2 + (1 - k2) * x - 3 * (1 - r) / 2 = 0 := by
    calc k2 + (1 - k2) * x - 3 * (1 - r) / 2 = (3 * (1 - r) / 2) - 3 * (1 - r) / 2 := by rw [hN_x]
      _ = 0 := by ring

  -- 4. Construct the polynomial linear combination that isolates r
  -- (This rigorous identity cleanly bypasses solving quadratics explicitly)
  have h_comb : 3 * r^2 - 1 =
      (r + 1) * (1 - x) * (k1 - (1 - r / 2))
    - (r + 1) * (k1 + (1 - k1) * x - 3 * r / 2)
    - r * (1 - x) * (k2 - (1 - r) / 2)
    + r * (k2 + (1 - k2) * x - 3 * (1 - r) / 2) := by ring

  -- 5. Substitute our zeroed equations into the combination
  have h_eq_zero : 3 * r^2 - 1 = 0 := by
    calc 3 * r^2 - 1 =
        (r + 1) * (1 - x) * (k1 - (1 - r / 2))
      - (r + 1) * (k1 + (1 - k1) * x - 3 * r / 2)
      - r * (1 - x) * (k2 - (1 - r) / 2)
      + r * (k2 + (1 - k2) * x - 3 * (1 - r) / 2) := h_comb
      _ = (r + 1) * (1 - x) * 0 - (r + 1) * 0 - r * (1 - x) * 0 + r * 0 := by rw [hH1, hH2, hH3, hH4]
      _ = 0 := by ring

  -- 6. Conclude the final value for r^2
  have h_3r2 : 3 * r^2 = 1 := by linarith [h_eq_zero]
  
  calc r^2 = (3 * r^2) / 3 := by ring
    _ = 1 / 3 := by rw [h_3r2]

end IMO1984B2
