import Mathlib

open scoped Real

namespace IMO1994P5

/--
The unique solution to IMO 1994 Problem 5 is f(x) = -x / (x + 1).
We formalize the exact algebraic verification that this function satisfies the 
primary functional equation condition on the domain x, y ≠ -1.
-/
noncomputable def f (x : ℝ) : ℝ := -x / (x + 1)

theorem imo1994_p5_condition1 (x y : ℝ) (hx : x + 1 ≠ 0) (hy : y + 1 ≠ 0) :
    f (x + f y + x * f y) = y + f x + y * f x := by
  have h_fy : f y = -y / (y + 1) := rfl
  have h_fx : f x = -x / (x + 1) := rfl

  -- LHS simplification to (x - y) / (y + 1)
  have h_lhs_arg : x + f y + x * f y = (x - y) / (y + 1) := by
    rw [h_fy]
    have H1 : (-y / (y + 1)) * (y + 1) = -y := by exact div_mul_cancel₀ _ hy
    have H2 : (x * (-y / (y + 1))) * (y + 1) = x * -y := by
      calc (x * (-y / (y + 1))) * (y + 1)
        _ = x * ((-y / (y + 1)) * (y + 1)) := by ring
        _ = x * -y := by rw [H1]
    have H3 : (x + -y / (y + 1) + x * (-y / (y + 1))) * (y + 1) = x - y := by
      calc (x + -y / (y + 1) + x * (-y / (y + 1))) * (y + 1)
        _ = x * (y + 1) + (-y / (y + 1)) * (y + 1) + (x * (-y / (y + 1))) * (y + 1) := by ring
        _ = x * (y + 1) + -y + x * -y := by rw [H1, H2]
        _ = x - y := by ring
    calc x + -y / (y + 1) + x * (-y / (y + 1))
      _ = (x + -y / (y + 1) + x * (-y / (y + 1))) * (y + 1) / (y + 1) := by rw [mul_div_cancel_right₀ _ hy]
      _ = (x - y) / (y + 1) := by rw [H3]

  -- RHS simplification to (y - x) / (x + 1)
  have h_rhs : y + f x + y * f x = (y - x) / (x + 1) := by
    rw [h_fx]
    have H1 : (-x / (x + 1)) * (x + 1) = -x := by exact div_mul_cancel₀ _ hx
    have H2 : (y * (-x / (x + 1))) * (x + 1) = y * -x := by
      calc (y * (-x / (x + 1))) * (x + 1)
        _ = y * ((-x / (x + 1)) * (x + 1)) := by ring
        _ = y * -x := by rw [H1]
    have H3 : (y + -x / (x + 1) + y * (-x / (x + 1))) * (x + 1) = y - x := by
      calc (y + -x / (x + 1) + y * (-x / (x + 1))) * (x + 1)
        _ = y * (x + 1) + (-x / (x + 1)) * (x + 1) + (y * (-x / (x + 1))) * (x + 1) := by ring
        _ = y * (x + 1) + -x + y * -x := by rw [H1, H2]
        _ = y - x := by ring
    calc y + -x / (x + 1) + y * (-x / (x + 1))
      _ = (y + -x / (x + 1) + y * (-x / (x + 1))) * (x + 1) / (x + 1) := by rw [mul_div_cancel_right₀ _ hx]
      _ = (y - x) / (x + 1) := by rw [H3]

  -- Apply the internal simplification reductions
  rw [h_lhs_arg, h_rhs]
  unfold f

  have hA : -((x - y) / (y + 1)) = (y - x) / (y + 1) := by
    have H1 : (-((x - y) / (y + 1))) * (y + 1) = y - x := by
      calc (-((x - y) / (y + 1))) * (y + 1)
        _ = -(((x - y) / (y + 1)) * (y + 1)) := by ring
        _ = -(x - y) := by rw [div_mul_cancel₀ _ hy]
        _ = y - x := by ring
    calc -((x - y) / (y + 1))
      _ = (-((x - y) / (y + 1))) * (y + 1) / (y + 1) := by rw [mul_div_cancel_right₀ _ hy]
      _ = (y - x) / (y + 1) := by rw [H1]

  have hB : ((x - y) / (y + 1)) + 1 = (x + 1) / (y + 1) := by
    have H1 : (((x - y) / (y + 1)) + 1) * (y + 1) = x + 1 := by
      calc (((x - y) / (y + 1)) + 1) * (y + 1)
        _ = ((x - y) / (y + 1)) * (y + 1) + (y + 1) := by ring
        _ = (x - y) + (y + 1) := by rw [div_mul_cancel₀ _ hy]
        _ = x + 1 := by ring
    calc ((x - y) / (y + 1)) + 1
      _ = (((x - y) / (y + 1)) + 1) * (y + 1) / (y + 1) := by rw [mul_div_cancel_right₀ _ hy]
      _ = (x + 1) / (y + 1) := by rw [H1]

  rw [hA, hB]

  have hB_ne_zero : (x + 1) / (y + 1) ≠ 0 := by
    intro h
    have h2 : ((x + 1) / (y + 1)) * (y + 1) = 0 * (y + 1) := by rw [h]
    rw [div_mul_cancel₀ _ hy, zero_mul] at h2
    exact hx h2

  -- Final cross-multiplication equivalent for division of fractions
  have h_CB : ((y - x) / (x + 1)) * ((x + 1) / (y + 1)) = (y - x) / (y + 1) := by
    have H1 : (((y - x) / (x + 1)) * ((x + 1) / (y + 1))) * (y + 1) = y - x := by
      calc (((y - x) / (x + 1)) * ((x + 1) / (y + 1))) * (y + 1)
        _ = ((y - x) / (x + 1)) * (((x + 1) / (y + 1)) * (y + 1)) := by ring
        _ = ((y - x) / (x + 1)) * (x + 1) := by rw [div_mul_cancel₀ _ hy]
        _ = y - x := by rw [div_mul_cancel₀ _ hx]
    calc ((y - x) / (x + 1)) * ((x + 1) / (y + 1))
      _ = (((y - x) / (x + 1)) * ((x + 1) / (y + 1))) * (y + 1) / (y + 1) := by rw [mul_div_cancel_right₀ _ hy]
      _ = (y - x) / (y + 1) := by rw [H1]

  calc ((y - x) / (y + 1)) / ((x + 1) / (y + 1))
    _ = (((y - x) / (x + 1)) * ((x + 1) / (y + 1))) / ((x + 1) / (y + 1)) := by rw [← h_CB]
    _ = (y - x) / (x + 1) := by rw [mul_div_cancel_right₀ _ hB_ne_zero]

end IMO1994P5
