import Mathlib

open Real

/--
Formalization of the algebraic identity and bounding step from the solution in "image_9a3b4a.png".
For the term b_n = 2 - 2 / sqrt(a_n), we prove that if a_n > 1, then b_n < 2.
-/
theorem imo_solution_bound (an : ℝ) (ha : an > 1) :
    2 - 2 / sqrt an < 2 := by
  have h_sqrt_pos : 0 < sqrt an := by
    have h_pos : 0 < an := by linarith
    exact sqrt_pos.mpr h_pos
  have h_div_pos : 0 < 2 / sqrt an := by positivity
  linarith
