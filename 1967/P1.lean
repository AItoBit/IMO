import Mathlib

open Real

/--
Formalization of the boundary case calculations from the solution to IMO 1967 Problem 1.
  the solution simplifies the geometric
condition to a set of algebraic and trigonometric calculations for the maximum bounding case.
-/
theorem imo1967_p1_solution_calculations
    (x a α : ℝ)
    (hx_nonneg : 0 ≤ x)
    (h_pythagoras : 1^2 + x^2 = 2^2)
    (h_cos : cos α = 1 / 2)
    (h_sin : sin α = sqrt 3 / 2)
    (h_a_bound : a ≤ cos α + sqrt 3 * sin α) :
    x = sqrt 3 ∧ a ≤ 2 := by
  
  -- "Using the Pythagorean theorem we conclude: 1^2 + x^2 = 2^2 => x = \sqrt{3}"
  have hx_sq : x^2 = 3 := by 
    linarith [h_pythagoras]
  
  have hx_val : x = sqrt 3 := by
    have h_sqrt : sqrt (x^2) = sqrt 3 := by rw [hx_sq]
    rwa [sqrt_sq hx_nonneg] at h_sqrt

  -- "a ≤ \cos \alpha + \sqrt{3} \sin \alpha ... a ≤ 2"
  have ha_eval : cos α + sqrt 3 * sin α = 2 := by
    rw [h_cos, h_sin]
    have h3 : sqrt 3 * sqrt 3 = 3 := mul_self_sqrt (by positivity)
    calc
      1 / 2 + sqrt 3 * (sqrt 3 / 2) = 1 / 2 + (sqrt 3 * sqrt 3) / 2 := by ring
      _ = 1 / 2 + 3 / 2 := by rw [h3]
      _ = 2 := by norm_num

  -- Combine both conclusions to finish the proof
  exact ⟨hx_val, by linarith [h_a_bound, ha_eval]⟩
