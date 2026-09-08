/-
# IMO 1977, Problem 2

In a finite sequence of real numbers the sum of any seven successive terms is
negative and the sum of any eleven successive terms is positive.  Determine the
maximum number of terms.

The answer is `16`.

## Modelling

A sequence of `n` terms is `x : ℕ → ℝ` used at the indices `0, …, n-1`; a window
of length `L` starting at `i` exists exactly when `i + L ≤ n`.  "Determine the
maximum" is `IsGreatest`.

## Proof

*No sequence of 17 terms works.*  With `s k = x 0 + ⋯ + x (k-1)`, the hypotheses
say `s (i+7) < s i` and `s (i+11) > s i`.  For `n = 17` these give the chain

  `0 = s₀ < s₁₁ < s₄ < s₁₅ < s₈ < s₁ < s₁₂ < s₅ < s₁₆ < s₉ < s₂ < s₁₃ < s₆
       < s₁₇ < s₁₀ < s₃ < s₁₄ < s₇ < s₀ = 0`,

which is absurd.  It uses each of the eleven 7-windows and each of the seven
11-windows exactly once, so `linarith` finds it from the eighteen inequalities
directly, without introducing the partial sums.

Any `n ≥ 17` restricts to `n = 17`, so `n ≤ 16`.

*A sequence of 16 terms exists.*  Taking the ranks in the analogous chain for
`n = 16` as partial sums and differencing gives

  `5, 5, -13, 5, 5, 5, -13, 5, 5, -13, 5, 5, 5, -13, 5, 5`,

for which every 7-window sums to `-1` and every 11-window sums to `1`.
-/

import Mathlib

namespace Imo1977P2

/-- **IMO 1977, Problem 2.** -/
theorem imo1977_p2 :
    IsGreatest {n : ℕ | ∃ x : ℕ → ℝ,
      (∀ i, i + 7 ≤ n → (∑ j ∈ Finset.range 7, x (i + j)) < 0) ∧
      (∀ i, i + 11 ≤ n → 0 < ∑ j ∈ Finset.range 11, x (i + j))} 16 := by
  constructor
  · -- an explicit sequence of 16 terms
    refine ⟨fun k => if k = 2 ∨ k = 6 ∨ k = 9 ∨ k = 13 then (-13 : ℝ) else 5, ?_, ?_⟩
    · intro i hi
      have hi9 : i ≤ 9 := by omega
      interval_cases i <;> norm_num [Finset.sum_range_succ]
    · intro i hi
      have hi5 : i ≤ 5 := by omega
      interval_cases i <;> norm_num [Finset.sum_range_succ]
  · -- no sequence with 17 or more terms
    rintro n ⟨x, h7, h11⟩
    by_contra hcon
    have h17 : 17 ≤ n := by omega
    have A0 := h7 0 (by omega)
    have A1 := h7 1 (by omega)
    have A2 := h7 2 (by omega)
    have A3 := h7 3 (by omega)
    have A4 := h7 4 (by omega)
    have A5 := h7 5 (by omega)
    have A6 := h7 6 (by omega)
    have A7 := h7 7 (by omega)
    have A8 := h7 8 (by omega)
    have A9 := h7 9 (by omega)
    have A10 := h7 10 (by omega)
    have B0 := h11 0 (by omega)
    have B1 := h11 1 (by omega)
    have B2 := h11 2 (by omega)
    have B3 := h11 3 (by omega)
    have B4 := h11 4 (by omega)
    have B5 := h11 5 (by omega)
    have B6 := h11 6 (by omega)
    norm_num [Finset.sum_range_succ] at A0 A1 A2 A3 A4 A5 A6 A7 A8 A9 A10
    norm_num [Finset.sum_range_succ] at B0 B1 B2 B3 B4 B5 B6
    linarith

end Imo1977P2
