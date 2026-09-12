import Mathlib

/-!
# IMO 1992, Problem 1

Find all integers `1 < a < b < c` such that `(a-1)(b-1)(c-1)` divides `abc - 1`.

Answer: `(a,b,c) = (2,4,8)` and `(a,b,c) = (3,5,15)`.

## Proof

Write `abc - 1 = k·(a-1)(b-1)(c-1)`.

* `k ≥ 2`, because `abc - 1 - (a-1)(b-1)(c-1) = ab + ac + bc - a - b - c > 0`.
* `k ≤ 3`, because `abc ≤ 4(a-1)(b-1)(c-1)` when `a ≥ 2`, `b ≥ 3`, `c ≥ 4`.

For `k = 2`: if `a ≥ 4` then `abc ≤ 2(a-1)(b-1)(c-1)`, which is impossible, so `a ∈ {2,3}`.
`a = 2` forces `2b + 2c = 3`, impossible; `a = 3` forces `bc + 5 = 4b + 4c`, giving `(3,5,15)`.

For `k = 3`: if `a ≥ 3` then `abc ≤ 3(a-1)(b-1)(c-1)`, impossible, so `a = 2`, which forces
`bc + 4 = 3b + 3c`, giving `(2,4,8)`.

Each time, `b` is bounded by comparing `bc` with a multiple of `c`, after which `interval_cases`
plus `omega` finishes.
-/

namespace Imo1992P1

theorem imo1992_p1 (a b c : ℤ) (h1 : 1 < a) (hab : a < b) (hbc : b < c) :
    ((a - 1) * (b - 1) * (c - 1) ∣ a * b * c - 1) ↔
      (a = 2 ∧ b = 4 ∧ c = 8) ∨ (a = 3 ∧ b = 5 ∧ c = 15) := by
  have ha : 2 ≤ a := by omega
  have hb : 3 ≤ b := by omega
  have hc : 4 ≤ c := by omega
  constructor
  · rintro ⟨k, hk⟩
    have hP : 0 < (a - 1) * (b - 1) * (c - 1) :=
      mul_pos (mul_pos (by omega) (by omega)) (by omega)
    -- `k ≥ 2`
    have e1 : 2 * b ≤ a * b := by nlinarith
    have e2 : 2 * c ≤ a * c := by nlinarith
    have e3 : 3 * c ≤ b * c := by nlinarith
    have hexp : a * b * c - 1 - (a - 1) * (b - 1) * (c - 1)
        = a * b + a * c + b * c - a - b - c := by ring
    have hgt : (a - 1) * (b - 1) * (c - 1) < a * b * c - 1 := by linarith
    have hk2 : 2 ≤ k := by
      by_contra hcon
      rw [not_le] at hcon
      nlinarith [hP, hgt, hk]
    -- `k ≤ 3`
    have hu : (0 : ℤ) ≤ a - 2 := by omega
    have hv : (0 : ℤ) ≤ b - 3 := by omega
    have hw : (0 : ℤ) ≤ c - 4 := by omega
    have hle4 : a * b * c ≤ 4 * ((a - 1) * (b - 1) * (c - 1)) := by
      nlinarith [mul_nonneg hu hv, mul_nonneg hu hw, mul_nonneg hv hw,
        mul_nonneg (mul_nonneg hu hv) hw]
    have hk3 : k ≤ 3 := by
      by_contra hcon
      rw [not_le] at hcon
      nlinarith [hP, hk, hle4]
    interval_cases k
    · -- `k = 2`
      have ha3 : a ≤ 3 := by
        by_contra hcon
        rw [not_le] at hcon
        have hu' : (0 : ℤ) ≤ a - 4 := by omega
        have hv' : (0 : ℤ) ≤ b - 5 := by omega
        have hw' : (0 : ℤ) ≤ c - 6 := by omega
        nlinarith [hk, mul_nonneg hu' hv', mul_nonneg hu' hw', mul_nonneg hv' hw',
          mul_nonneg (mul_nonneg hu' hv') hw']
      interval_cases a
      · -- `a = 2` : `2b + 2c = 3`, impossible
        exfalso
        have key : 2 * b + 2 * c = 3 := by linear_combination hk
        omega
      · -- `a = 3` : `bc + 5 = 4b + 4c`
        have key : b * c + 5 = 4 * b + 4 * c := by linear_combination -hk
        have hb7 : b ≤ 7 := by
          by_contra hcon
          rw [not_le] at hcon
          nlinarith [key, (by omega : (0 : ℤ) < c)]
        interval_cases b <;> omega
    · -- `k = 3`
      have ha2 : a ≤ 2 := by
        by_contra hcon
        rw [not_le] at hcon
        have hu' : (0 : ℤ) ≤ a - 3 := by omega
        have hv' : (0 : ℤ) ≤ b - 4 := by omega
        have hw' : (0 : ℤ) ≤ c - 5 := by omega
        nlinarith [hk, mul_nonneg hu' hv', mul_nonneg hu' hw', mul_nonneg hv' hw',
          mul_nonneg (mul_nonneg hu' hv') hw']
      have ha2' : a = 2 := by omega
      subst ha2'
      have key : b * c + 4 = 3 * b + 3 * c := by linear_combination -hk
      have hb5 : b ≤ 5 := by
        by_contra hcon
        rw [not_le] at hcon
        nlinarith [key, (by omega : (0 : ℤ) < c)]
      interval_cases b <;> omega
  · rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
    · exact ⟨3, by norm_num⟩
    · exact ⟨2, by norm_num⟩

end Imo1992P1
