import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-!
# Right Triangle with Hypotenuse Median Equal to the Geometric Mean of Legs

Problem:
Construct a right triangle with given hypotenuse `c` such that the median drawn to
the hypotenuse is the geometric mean of the two legs `a` and `b`.

In a right triangle:
- Pythagorean theorem: `a^2 + b^2 = c^2`
- Median to the hypotenuse: `m = c / 2`
- Geometric mean condition: `m = Real.sqrt (a * b)`, or equivalently `m^2 = a * b`.
-/

/-- Characterization: in any right triangle with hypotenuse `c` and legs `a, b`,
    the median to the hypotenuse `m = c / 2` satisfies `m^2 = a * b` if and only if
    `a^2 - 4 * a * b + b^2 = 0`. -/
theorem median_geom_mean_iff_quad_relation (a b c : ℝ) (h_pyth : a^2 + b^2 = c^2) :
    (c / 2)^2 = a * b ↔ a^2 - 4 * a * b + b^2 = 0 := by
  constructor
  · intro h
    have h1 : c^2 = 4 * (a * b) := by
      linarith [show (c / 2)^2 = c^2 / 4 by ring, h]
    linarith [h_pyth, h1]
  · intro h
    have h1 : c^2 = 4 * (a * b) := by
      linarith [h_pyth, h]
    calc
      (c / 2)^2 = c^2 / 4 := by ring
      _ = (4 * (a * b)) / 4 := by rw [h1]
      _ = a * b := by ring

/-- Main Existence Theorem:
    For any given hypotenuse `c > 0`, there exist valid positive catheti `a` and `b`
    such that `a^2 + b^2 = c^2` and the median `c / 2` is the geometric mean of `a` and `b`. -/
theorem exists_right_triangle_median_eq_geom_mean (c : ℝ) (hc : 0 < c) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ a^2 + b^2 = c^2 ∧ (c / 2)^2 = a * b := by
  let a := (c / 4) * (Real.sqrt 6 + Real.sqrt 2)
  let b := (c / 4) * (Real.sqrt 6 - Real.sqrt 2)
  use a, b

  have h6_pos : (0 : ℝ) < 6 := by norm_num
  have h2_pos : (0 : ℝ) < 2 := by norm_num
  have h6_ge : (0 : ℝ) ≤ 6 := by norm_num
  have h2_ge : (0 : ℝ) ≤ 2 := by norm_num

  have h_sqrt6_sq : (Real.sqrt 6)^2 = 6 := Real.sq_sqrt h6_ge
  have h_sqrt2_sq : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt h2_ge

  have h_lt : Real.sqrt 2 < Real.sqrt 6 := Real.sqrt_lt_sqrt h2_ge (by norm_num)

  have ha_pos : 0 < a := by
    have h_sum : 0 < Real.sqrt 6 + Real.sqrt 2 := by positivity
    exact mul_pos (by linarith) h_sum

  have hb_pos : 0 < b := by
    have h_diff : 0 < Real.sqrt 6 - Real.sqrt 2 := sub_pos.mpr h_lt
    exact mul_pos (by linarith) h_diff

  have h_prod : a * b = (c / 2)^2 := by
    calc
      a * b = ((c / 4) * (c / 4)) * ((Real.sqrt 6 + Real.sqrt 2) * (Real.sqrt 6 - Real.sqrt 2)) := by ring
      _ = (c^2 / 16) * ((Real.sqrt 6)^2 - (Real.sqrt 2)^2) := by ring
      _ = (c^2 / 16) * (6 - 2) := by rw [h_sqrt6_sq, h_sqrt2_sq]
      _ = c^2 / 4 := by ring
      _ = (c / 2)^2 := by ring

  have h_pyth : a^2 + b^2 = c^2 := by
    calc
      a^2 + b^2 = (c / 4)^2 * ((Real.sqrt 6 + Real.sqrt 2)^2 + (Real.sqrt 6 - Real.sqrt 2)^2) := by ring
      _ = (c^2 / 16) * (2 * (Real.sqrt 6)^2 + 2 * (Real.sqrt 2)^2) := by ring
      _ = (c^2 / 16) * (2 * 6 + 2 * 2) := by rw [h_sqrt6_sq, h_sqrt2_sq]
      _ = (c^2 / 16) * 16 := by ring
      _ = c^2 := by ring

  refine ⟨ha_pos, hb_pos, h_pyth, h_prod.symm⟩
