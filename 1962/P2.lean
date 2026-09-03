import Mathlib

open scoped Real
open scoped Nat

/-! # IMO 1962 Problem 2

Find all real `x` satisfying `√(3 - x) - √(x + 1) > 1/2`.
The solution set is `[-1, 1 - √31/8)`.
-/

namespace Imo1962P2

/-- The algebraic core: for `-1 ≤ x` and `x ≤ 3`, the inequality
`1/2 < √(3 - x) - √(x + 1)` holds iff `x < 1 - √31 / 8`. -/
theorem key (x : ℝ) (h3 : 0 ≤ 3 - x) (h1 : 0 ≤ x + 1) :
    1 / 2 < √(3 - x) - √(x + 1) ↔ x < 1 - √31 / 8 := by
  have ha0 : 0 ≤ √(3 - x) := Real.sqrt_nonneg _
  have hb0 : 0 ≤ √(x + 1) := Real.sqrt_nonneg _
  have ha : √(3 - x) ^ 2 = 3 - x := Real.sq_sqrt h3
  have hb : √(x + 1) ^ 2 = x + 1 := Real.sq_sqrt h1
  have hs0 : (0:ℝ) ≤ √31 := Real.sqrt_nonneg _
  have hs : (√31) ^ 2 = 31 := Real.sq_sqrt (by norm_num)
  set a := √(3 - x) with hadef
  set b := √(x + 1) with hbdef
  constructor
  · intro h
    -- from `a - b > 1/2` deduce `a * b < 15/8` and `a > b`
    have hab : a * b < 15 / 8 := by nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]
    have habsq : (a * b) ^ 2 = (3 - x) * (x + 1) := by
      rw [mul_pow, ha, hb]
    have hprod : (3 - x) * (x + 1) < 225 / 64 := by
      nlinarith [mul_nonneg ha0 hb0]
    have hxlt1 : x < 1 := by nlinarith
    nlinarith [sq_nonneg (x - 1)]
  · intro h
    have hxlt : x < 7 / 8 := by nlinarith
    have hquad : (7 / 4 - 2 * x) ^ 2 > x + 1 := by nlinarith [sq_nonneg (x - 1)]
    have hb' : b < 7 / 4 - 2 * x := by
      nlinarith [sq_nonneg (b - (7 / 4 - 2 * x))]
    have ha' : (b + 1 / 2) ^ 2 < a ^ 2 := by
      rw [ha]
      nlinarith [hb]
    have := lt_of_pow_lt_pow_left₀ 2 ha0 ha'
    linarith

end Imo1962P2

/-- **IMO 1962, Problem 2.**  The set of real `x` with `3 - x ≥ 0`, `x + 1 ≥ 0` and
`√(3 - x) - √(x + 1) > 1/2` is exactly `[-1, 1 - √31/8)`. -/
theorem imo_1962_p2 :
    {x : ℝ | 0 ≤ 3 - x ∧ 0 ≤ x + 1 ∧ 1 / 2 < √(3 - x) - √(x + 1)} =
      Set.Ico (-1) (1 - √31 / 8) := by
  have hs0 : (0:ℝ) ≤ √31 := Real.sqrt_nonneg _
  have hs : (√31) ^ 2 = 31 := Real.sq_sqrt (by norm_num)
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_Ico]
  constructor
  · rintro ⟨h3, h1, h⟩
    exact ⟨by linarith, (Imo1962P2.key x h3 h1).1 h⟩
  · rintro ⟨hl, hr⟩
    have hsgt : (5:ℝ) < √31 := by nlinarith
    have h3 : (0:ℝ) ≤ 3 - x := by linarith
    have h1 : (0:ℝ) ≤ x + 1 := by linarith
    exact ⟨h3, h1, (Imo1962P2.key x h3 h1).2 hr⟩
