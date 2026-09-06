import Mathlib

/--
Formalization of the final algebraic deduction in the solution for IMO 1970 Problem 2.
It demonstrates how the strict inequality between the highest-degree terms' ratios
directly implies the strict inequality between the remainders' ratios.
-/
theorem imo1970_p2_deduction (An A_prev Bn B_prev xn_an xn_bn : ℝ)
    (hAn_ne : An ≠ 0) (hBn_ne : Bn ≠ 0)
    (hA : An = A_prev + xn_an)
    (hB : Bn = B_prev + xn_bn)
    (h_ineq : xn_an / An > xn_bn / Bn) :
    A_prev / An < B_prev / Bn := by
  
  -- Express the ratio A_{n-1} / A_n as 1 - (x_n * a^n) / A_n
  have hA_div : A_prev / An = 1 - xn_an / An := by
    have h_sub : A_prev = An - xn_an := by linarith [hA]
    calc A_prev / An
      _ = (An - xn_an) / An := by rw [h_sub]
      _ = An / An - xn_an / An := sub_div An xn_an An
      _ = 1 - xn_an / An := by rw [div_self hAn_ne]
      
  -- Express the ratio B_{n-1} / B_n as 1 - (x_n * b^n) / B_n
  have hB_div : B_prev / Bn = 1 - xn_bn / Bn := by
    have h_sub : B_prev = Bn - xn_bn := by linarith [hB]
    calc B_prev / Bn
      _ = (Bn - xn_bn) / Bn := by rw [h_sub]
      _ = Bn / Bn - xn_bn / Bn := sub_div Bn xn_bn Bn
      _ = 1 - xn_bn / Bn := by rw [div_self hBn_ne]
      
  -- Substitute the simplified forms and apply the given inequality
  rw [hA_div, hB_div]
  linarith
