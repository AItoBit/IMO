import Mathlib

namespace Imo2007P4

/-!
Formalization of the algebraic core of IMO 2007 Problem 4.
Proves that the areas of triangles RQL and RPK are equal given the
midpoint symmetry on the secant line and the similarity of the projected right triangles.
-/
theorem imo2007_p4_algebraic_core
    (RQ QL RP PK QC PC sin_theta k x y : ℝ)
    (h_sim1 : QL = k * QC)
    (h_sim2 : PK = k * PC)
    (h_RQ : RQ = -x - (-y))
    (h_QC : QC = y - (-x))
    (h_RP : RP = x - (-y))
    (h_PC : PC = y - x) :
    (1 / 2 : ℝ) * RQ * QL * sin_theta = (1 / 2 : ℝ) * RP * PK * sin_theta := by
  -- Step 1: Prove the Power of a Point segment product identity
  have h_pow : RQ * QC = RP * PC := by
    calc
      RQ * QC = (-x - (-y)) * (y - (-x)) := by rw [h_RQ, h_QC]
      _ = (y - x) * (y + x) := by ring
      _ = (x - (-y)) * (y - x) := by ring
      _ = RP * PC := by rw [h_RP, h_PC]
  
  -- Step 2: Scale the area equivalence using the proportionality constant
  calc
    (1 / 2 : ℝ) * RQ * QL * sin_theta = (1 / 2 : ℝ) * RQ * (k * QC) * sin_theta := by rw [h_sim1]
    _ = (1 / 2 : ℝ) * k * (RQ * QC) * sin_theta := by ring
    _ = (1 / 2 : ℝ) * k * (RP * PC) * sin_theta := by rw [h_pow]
    _ = (1 / 2 : ℝ) * RP * (k * PC) * sin_theta := by ring
    _ = (1 / 2 : ℝ) * RP * PK * sin_theta := by rw [← h_sim2]

end Imo2007P4
