import Mathlib

open Real

/--
Formalization of the algebraic and trigonometric core of IMO 1967 Problem 4.
The geometric solution relies on showing that a side length `BC` of the constructed
triangle is proportional to the chord length `PB` in a fixed circle.
Since `PB = D * sin θ` (where `D` is the diameter of the circumcircle `C_B`),
`PB` is maximized when `θ = π / 2` (i.e. `PB` is the diameter).
Because `BC = k * PB` for a fixed positive constant `k` (due to the similarity 
of all triangles `PBC`), maximizing `PB` directly maximizes `BC`.
-/
theorem imo1967_p4_maximization (D k θ : ℝ) (hD : 0 ≤ D) (hk : 0 ≤ k) :
    k * (D * sin θ) ≤ k * D ∧ (θ = π / 2 → k * (D * sin θ) = k * D) := by
  constructor
  · -- Prove BC ≤ k * D
    have h_sin : sin θ ≤ 1 := sin_le_one θ
    have h_PB_le : D * sin θ ≤ D := by
      calc D * sin θ ≤ D * 1 := mul_le_mul_of_nonneg_left h_sin hD
           _ = D := mul_one D
    exact mul_le_mul_of_nonneg_left h_PB_le hk
  · -- Prove equality at θ = π / 2
    intro hθ
    have h_sin_pi_div_two : sin (π / 2) = 1 := sin_pi_div_two
    calc k * (D * sin θ) = k * (D * sin (π / 2)) := by rw [hθ]
         _ = k * (D * 1) := by rw [h_sin_pi_div_two]
         _ = k * D := by ring
