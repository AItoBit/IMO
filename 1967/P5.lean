import Mathlib

open Real

/--
Auxiliary lemma: (-x)^(2k+1) = - x^(2k+1)
-/
lemma neg_pow_odd (x : ℝ) (k : ℕ) : (-x)^(2 * k + 1) = -(x^(2 * k + 1)) := by
  induction k with
  | zero => ring
  | succ k ih =>
    have h1 : 2 * (k + 1) + 1 = 2 * k + 1 + 2 := by omega
    rw [h1]
    have h2 : (-x) ^ (2 * k + 1 + 2) = (-x) ^ (2 * k + 1) * (-x) ^ 2 := pow_add (-x) _ _
    have h3 : x ^ (2 * k + 1 + 2) = x ^ (2 * k + 1) * x ^ 2 := pow_add x _ _
    rw [h2, h3, ih]
    ring

/--
Auxiliary lemma: x^(2k) ≥ 0
-/
lemma pow_even_nonneg (x : ℝ) (k : ℕ) : 0 ≤ x^(2 * k) := by
  induction k with
  | zero =>
    change 0 ≤ x^0
    rw [pow_zero]
    exact zero_le_one
  | succ k ih =>
    have h1 : 2 * (k + 1) = 2 * k + 2 := by omega
    rw [h1, pow_add]
    have h2 : 0 ≤ x^2 := sq_nonneg x
    exact mul_nonneg ih h2

/--
Formalization of the algebraic core of the solution to IMO 1967 Problem 5.
-/
theorem imo1967_p5_cancellation
    (a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ : ℝ)
    (h₁ : a₁ = -a₈)
    (h₂ : a₂ = -a₇)
    (h₃ : a₃ = -a₆)
    (h₄ : a₄ = -a₅)
    (k : ℕ) :
    (a₁^(2 * k + 1) + a₂^(2 * k + 1) + a₃^(2 * k + 1) + a₄^(2 * k + 1) +
     a₅^(2 * k + 1) + a₆^(2 * k + 1) + a₇^(2 * k + 1) + a₈^(2 * k + 1) = 0) ∧
    (0 ≤ a₁^(2 * k) + a₂^(2 * k) + a₃^(2 * k) + a₄^(2 * k) +
         a₅^(2 * k) + a₆^(2 * k) + a₇^(2 * k) + a₈^(2 * k)) := by
  constructor
  · -- Odd powers cancel out exactly
    rw [h₁, h₂, h₃, h₄]
    have eq1 := neg_pow_odd a₈ k
    have eq2 := neg_pow_odd a₇ k
    have eq3 := neg_pow_odd a₆ k
    have eq4 := neg_pow_odd a₅ k
    rw [eq1, eq2, eq3, eq4]
    ring
  · -- Even powers are sums of non-negative reals
    have eq1 := pow_even_nonneg a₁ k
    have eq2 := pow_even_nonneg a₂ k
    have eq3 := pow_even_nonneg a₃ k
    have eq4 := pow_even_nonneg a₄ k
    have eq5 := pow_even_nonneg a₅ k
    have eq6 := pow_even_nonneg a₆ k
    have eq7 := pow_even_nonneg a₇ k
    have eq8 := pow_even_nonneg a₈ k
    linarith
