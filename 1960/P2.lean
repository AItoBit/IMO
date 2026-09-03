import Mathlib

open scoped Real
open scoped Nat

/-!
# IMO 1960 Problem 2

For what real values of `x` does the inequality
`4 * x ^ 2 / (1 - √(1 + 2 * x)) ^ 2 < 2 * x + 9` hold?

Answer: exactly for `-1/2 ≤ x < 45/8` with `x ≠ 0`.

The original submission was stated with the competition-problem markers
`@[imo_problem_subject algebra]` and `answer(...)`, which are not available in
this project; the statement below is the same set equality with those wrappers
removed.
-/

/-- Key algebraic simplification: if `0 ≤ 1 + 2 * x` and `(1 - √(1 + 2 * x)) ^ 2 ≠ 0`, then
`4 * x ^ 2 / (1 - √(1 + 2 * x)) ^ 2 = (1 + √(1 + 2 * x)) ^ 2`. -/
theorem imo_1960_p2_div_eq (x : ℝ) (hx : 0 ≤ 1 + 2 * x) (hne : (1 - √(1 + 2 * x)) ^ 2 ≠ 0) :
    4 * x ^ 2 / (1 - √(1 + 2 * x)) ^ 2 = (1 + √(1 + 2 * x)) ^ 2 := by
  have ht : √(1 + 2 * x) ^ 2 = 1 + 2 * x := Real.sq_sqrt hx
  rw [div_eq_iff hne]
  nlinarith [ht]

/-- For what real values of `x` does `4x²/(1-√(1+2x))² < 2x + 9` hold?
The answer is `-1/2 ≤ x < 45/8`, except `x = 0`. -/
theorem imo_1960_p2 :
    {x : ℝ | 0 ≤ 1 + 2 * x ∧ (1 - √(1 + 2 * x)) ^ 2 ≠ 0 ∧
      4 * x ^ 2 / (1 - √(1 + 2 * x)) ^ 2 < 2 * x + 9} =
    Set.Ico (-(1 / 2)) (45 / 8) \ {0} := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_Ico, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hx, hne, hlt⟩
    have ht : √(1 + 2 * x) ^ 2 = 1 + 2 * x := Real.sq_sqrt hx
    have hnn : 0 ≤ √(1 + 2 * x) := Real.sqrt_nonneg _
    rw [imo_1960_p2_div_eq x hx hne] at hlt
    refine ⟨⟨by linarith, by nlinarith⟩, ?_⟩
    rintro rfl
    apply hne
    norm_num
  · rintro ⟨⟨hlo, hhi⟩, hx0⟩
    have hx : 0 ≤ 1 + 2 * x := by linarith
    have ht : √(1 + 2 * x) ^ 2 = 1 + 2 * x := Real.sq_sqrt hx
    have hnn : 0 ≤ √(1 + 2 * x) := Real.sqrt_nonneg _
    have hne : (1 - √(1 + 2 * x)) ^ 2 ≠ 0 := by
      intro h
      have h0 : 1 - √(1 + 2 * x) = 0 := by
        have := sq_eq_zero_iff.mp h
        simpa using this
      have h1 : √(1 + 2 * x) = 1 := by linarith
      rw [h1] at ht
      exact hx0 (by linarith)
    refine ⟨hx, hne, ?_⟩
    rw [imo_1960_p2_div_eq x hx hne]
    have h7 : √(1 + 2 * x) < 7 / 2 := by nlinarith
    nlinarith
