import Mathlib

/-!
# IMO 1985, Problem 5 (Algebraic Core of Solution 5)


We are given the following angular relations:
1. `θ + φ = 90` (Step 1)
2. `θ = η + lam` (Step 2)
3. `angle_AON = 2 * (η + lam)` (Step 4, combined)
4. `angle_AMN = 2 * φ` (Step 3 conclusion)
5. `angle_OMN = φ` (Step 5, derived from cyclic quad AOMN)
6. `angle_MNB = θ` (Step 5)

We prove that `angle_AON + angle_AMN = 180` (establishing that AOMN is cyclic),
and subsequently that `angle_OMB = angle_OMN + angle_MNB = 90`.
-/

namespace IMO1985P5

theorem solution5_angle_chasing
    (θ φ η lam angle_AON angle_AMN angle_OMN angle_MNB angle_OMB : ℝ)
    (h1 : θ + φ = 90)
    (h2 : θ = η + lam)
    (h3 : angle_AON = 2 * η + 2 * lam)
    (h4 : angle_AMN = 2 * φ)
    (h5 : angle_OMN = φ)
    (h6 : angle_MNB = θ)
    (h7 : angle_OMB = angle_OMN + angle_MNB) :
    (angle_AON + angle_AMN = 180) ∧ (angle_OMB = 90) := by
  
  constructor
  · -- Prove angle_AON + angle_AMN = 180
    calc angle_AON + angle_AMN = (2 * η + 2 * lam) + 2 * φ := by rw [h3, h4]
      _ = 2 * (η + lam) + 2 * φ := by ring
      _ = 2 * θ + 2 * φ := by rw [← h2]
      _ = 2 * (θ + φ) := by ring
      _ = 2 * 90 := by rw [h1]
      _ = 180 := by norm_num
  
  · -- Prove angle_OMB = 90
    calc angle_OMB = angle_OMN + angle_MNB := h7
      _ = φ + θ := by rw [h5, h6]
      _ = θ + φ := by ring
      _ = 90 := h1

end IMO1985P5
