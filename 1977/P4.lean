/-
# IMO 1977, Problem 4

Let `a, b, A, B` be reals and

  `f x = 1 - a cos x - b sin x - A cos 2x - B sin 2x`.

Prove that if `f x ≥ 0` for every real `x`, then `a² + b² ≤ 2` and `A² + B² ≤ 1`.

## Proof



  if `a cos t + b sin t ≤ c` for all `t` and `c ≥ 0`, then `a² + b² ≤ c²`.

It is proved by exhibiting a `t` with `cos t = a/r`, `sin t = b/r`, where
`r = √(a²+b²)`, via `arccos` (and a sign flip when `b < 0`).

* `f x + f (x + π)` kills the first harmonic: `A cos 2x + B sin 2x ≤ 1` for all
  `x`, and `2x` runs over all reals, so `A² + B² ≤ 1`.
* `f x + f (x + π/2)` kills the second harmonic and gives
  `(a+b) cos x + (b-a) sin x ≤ 2` for all `x`, so `(a+b)² + (b-a)² ≤ 4`, that is
  `2(a² + b²) ≤ 4`.  This avoids the `π/4` shift and the `√2` of the write-up.
-/

import Mathlib

namespace Imo1977P4

/-- If `a cos t + b sin t ≤ c` for every `t` (and `c ≥ 0`), then `a² + b² ≤ c²`. -/
private lemma key {a b c : ℝ} (hc : 0 ≤ c)
    (h : ∀ t : ℝ, a * Real.cos t + b * Real.sin t ≤ c) : a ^ 2 + b ^ 2 ≤ c ^ 2 := by
  rcases eq_or_lt_of_le (show (0:ℝ) ≤ a ^ 2 + b ^ 2 by positivity) with h0 | h0
  · nlinarith [sq_nonneg c]
  · set r : ℝ := Real.sqrt (a ^ 2 + b ^ 2) with hrdef
    have hr2 : r ^ 2 = a ^ 2 + b ^ 2 := Real.sq_sqrt (by positivity)
    have hrpos : 0 < r := by
      rw [hrdef]
      exact Real.sqrt_pos.mpr h0
    have hrne : r ≠ 0 := hrpos.ne'
    -- `|a| ≤ r`, hence `a / r ∈ [-1, 1]`
    have habs : |a| ≤ r := by
      rcases abs_cases a with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] <;> nlinarith [sq_nonneg b]
    have hd : |a / r| ≤ 1 := by
      rw [abs_div, abs_of_pos hrpos, div_le_one hrpos]
      exact habs
    obtain ⟨hd2, hd1⟩ := abs_le.mp hd
    -- `sin (arccos (a/r)) = |b| / r`
    have hx2 : 1 - (a / r) ^ 2 = (|b| / r) ^ 2 := by
      rw [div_pow, div_pow, sq_abs]
      field_simp
      linarith [hr2]
    have hsin : Real.sin (Real.arccos (a / r)) = |b| / r := by
      rw [Real.sin_arccos, hx2, Real.sqrt_sq (div_nonneg (abs_nonneg b) hrpos.le)]
    -- a point of the circle with the right coordinates
    obtain ⟨t, hct, hst⟩ : ∃ t : ℝ, Real.cos t = a / r ∧ Real.sin t = b / r := by
      by_cases hb : 0 ≤ b
      · exact ⟨Real.arccos (a / r), Real.cos_arccos hd2 hd1,
          by rw [hsin, abs_of_nonneg hb]⟩
      · refine ⟨-Real.arccos (a / r), ?_, ?_⟩
        · rw [Real.cos_neg]
          exact Real.cos_arccos hd2 hd1
        · rw [Real.sin_neg, hsin, abs_of_neg (not_le.mp hb)]
          ring
    have hle := h t
    rw [hct, hst] at hle
    have hval : a * (a / r) + b * (b / r) = r := by
      field_simp
      nlinarith [hr2]
    rw [hval] at hle
    nlinarith [hle, hrpos, hr2]

/-- **IMO 1977, Problem 4.** -/
theorem imo1977_p4 (a b A B : ℝ)
    (h : ∀ x : ℝ,
      0 ≤ 1 - a * Real.cos x - b * Real.sin x
            - A * Real.cos (2 * x) - B * Real.sin (2 * x)) :
    a ^ 2 + b ^ 2 ≤ 2 ∧ A ^ 2 + B ^ 2 ≤ 1 := by
  constructor
  · -- pair `x` with `x + π/2`: the second harmonic cancels
    have hab : ∀ x : ℝ, (a + b) * Real.cos x + (b - a) * Real.sin x ≤ 2 := by
      intro x
      have h1 := h x
      have h2 := h (x + Real.pi / 2)
      rw [show 2 * (x + Real.pi / 2) = 2 * x + Real.pi from by ring] at h2
      simp only [Real.cos_add, Real.sin_add, Real.cos_pi_div_two, Real.sin_pi_div_two,
        Real.cos_pi, Real.sin_pi] at h2
      linarith
    have := key (by norm_num : (0:ℝ) ≤ 2) hab
    nlinarith [this]
  · -- pair `x` with `x + π`: the first harmonic cancels
    have hAB : ∀ t : ℝ, A * Real.cos t + B * Real.sin t ≤ 1 := by
      intro t
      have h1 := h (t / 2)
      have h2 := h (t / 2 + Real.pi)
      rw [show 2 * (t / 2) = t from by ring] at h1
      rw [show 2 * (t / 2 + Real.pi) = t + 2 * Real.pi from by ring] at h2
      simp only [Real.cos_add, Real.sin_add, Real.cos_pi, Real.sin_pi,
        Real.cos_two_pi, Real.sin_two_pi] at h2
      linarith
    exact key (by norm_num : (0:ℝ) ≤ 1) hAB

end Imo1977P4
