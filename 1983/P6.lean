import Mathlib

/-!
# IMO 1984, Problem 6 (Excerpt)

This formalizes the metric space inequalities at the conclusion of the 
solution presented in the reference text. The proof uses the triangle 
inequality to bound the distances between the key points along the paths.
-/

theorem imo1984_b3_bounds
  {α : Type*} [MetricSpace α]
  (X X' Y B B' : α)
  (hXX' : dist X X' ≤ (1:ℝ) / 2)
  (hX'Y : dist X' Y ≤ (1:ℝ) / 2)
  (hBB' : dist B B' ≤ (1:ℝ) / 2)
  (hX'B' : 100 ≤ dist X' B') :
  dist X Y ≤ (1:ℝ) ∧ 
  (99:ℝ) ≤ dist X B ∧ 
  (99:ℝ) ≤ dist Y B ∧ 
  (198:ℝ) ≤ dist X B + dist Y B := by
  
  -- XY ≤ XX' + X'Y ≤ 1
  have hXY : dist X Y ≤ 1 := by
    have t1 := dist_triangle X X' Y
    linarith

  -- XB ≥ X'B' - XX' - BB' ≥ 100 - 1/2 - 1/2 = 99
  have hXB : 99 ≤ dist X B := by
    have t1 := dist_triangle X' B B'
    have t2 := dist_triangle X' X B
    have t3 := dist_comm X X'
    linarith

  -- YB ≥ X'B' - X'Y - BB' ≥ 100 - 1/2 - 1/2 = 99
  have hYB : 99 ≤ dist Y B := by
    have t1 := dist_triangle X' B B'
    have t2 := dist_triangle X' Y B
    linarith

  -- The path from X to Y via B has length at least 198
  exact ⟨hXY, hXB, hYB, by linarith⟩
