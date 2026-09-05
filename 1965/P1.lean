import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace IMO1965P1

open Real Set

/-- For real `u v`, `||u + v| - |u - v|| = 2 * min |u| |v|`. -/
theorem abs_abs_add_sub_abs_sub (u v : ℝ) :
    |(|u + v| - |u - v|)| = 2 * min |u| |v| := by
  rcases abs_cases (u + v) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
    rcases abs_cases (u - v) with ⟨h2, _⟩ | ⟨h2, _⟩ <;>
    rcases abs_cases u with ⟨h3, _⟩ | ⟨h3, _⟩ <;>
    rcases abs_cases v with ⟨h4, _⟩ | ⟨h4, _⟩ <;>
    rw [h1, h2, h3, h4, min_def] <;> split_ifs <;>
    rw [abs_eq (by linarith)] <;> first | (left; linarith) | (right; linarith)

/-- `√(1 + sin 2x) = |sin x + cos x|`. -/
theorem sqrt_one_add_sin_two_mul (x : ℝ) :
    Real.sqrt (1 + Real.sin (2 * x)) = |Real.sin x + Real.cos x| := by
  rw [show (1 : ℝ) + Real.sin (2 * x) = (Real.sin x + Real.cos x) ^ 2 by
        rw [Real.sin_two_mul]; nlinarith [Real.sin_sq_add_cos_sq x],
    Real.sqrt_sq_eq_abs]

/-- `√(1 - sin 2x) = |sin x - cos x|`. -/
theorem sqrt_one_sub_sin_two_mul (x : ℝ) :
    Real.sqrt (1 - Real.sin (2 * x)) = |Real.sin x - Real.cos x| := by
  rw [show (1 : ℝ) - Real.sin (2 * x) = (Real.sin x - Real.cos x) ^ 2 by
        rw [Real.sin_two_mul]; nlinarith [Real.sin_sq_add_cos_sq x],
    Real.sqrt_sq_eq_abs]

/-- The quantity in the problem equals `2 * min |sin x| |cos x|`. -/
theorem abs_sqrt_sub_sqrt_eq (x : ℝ) :
    |Real.sqrt (1 + Real.sin (2 * x)) - Real.sqrt (1 - Real.sin (2 * x))|
      = 2 * min |Real.sin x| |Real.cos x| := by
  rw [sqrt_one_add_sin_two_mul, sqrt_one_sub_sin_two_mul]
  exact abs_abs_add_sub_abs_sub (Real.sin x) (Real.cos x)

/-- The right-hand inequality always holds. -/
theorem abs_sqrt_sub_sqrt_le_sqrt_two (x : ℝ) :
    |Real.sqrt (1 + Real.sin (2 * x)) - Real.sqrt (1 - Real.sin (2 * x))| ≤ Real.sqrt 2 := by
  rw [abs_sqrt_sub_sqrt_eq]
  have hs := Real.sin_sq_add_cos_sq x
  have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h2n : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  rcases le_total |Real.sin x| |Real.cos x| with h | h
  · rw [min_eq_left h]
    nlinarith [abs_nonneg (Real.sin x), sq_abs (Real.sin x), sq_abs (Real.cos x),
      abs_nonneg (Real.cos x)]
  · rw [min_eq_right h]
    nlinarith [abs_nonneg (Real.sin x), sq_abs (Real.sin x), sq_abs (Real.cos x),
      abs_nonneg (Real.cos x)]

/-- Strictly below `π/4` (and above `0`), `|sin y| < cos y`. -/
theorem abs_sin_lt_cos_of_lt_pi_div_four {y : ℝ} (h0 : 0 ≤ y) (h1 : y < Real.pi / 4) :
    |Real.sin y| < Real.cos y := by
  have hpi := Real.pi_pos
  have hs : Real.sin y < Real.sin (Real.pi / 4) :=
    Real.strictMonoOn_sin ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ h1
  have hc : Real.cos (Real.pi / 4) < Real.cos y :=
    Real.strictAntiOn_cos ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ h1
  rw [Real.sin_pi_div_four] at hs
  rw [Real.cos_pi_div_four] at hc
  have hsn : 0 ≤ Real.sin y := Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith)
  rw [abs_of_nonneg hsn]
  linarith

/-- On `[π/4, π/2]` we have `cos y ≤ |sin y|`. -/
theorem cos_le_abs_sin_of_mem_pi_div_four_pi_div_two {y : ℝ} (h0 : Real.pi / 4 ≤ y)
    (h1 : y ≤ Real.pi / 2) : Real.cos y ≤ |Real.sin y| := by
  have hpi := Real.pi_pos
  have hs : Real.sin (Real.pi / 4) ≤ Real.sin y :=
    Real.strictMonoOn_sin.monotoneOn ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ h0
  have hc : Real.cos y ≤ Real.cos (Real.pi / 4) :=
    Real.strictAntiOn_cos.antitoneOn ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ h0
  rw [Real.sin_pi_div_four] at hs
  rw [Real.cos_pi_div_four] at hc
  calc Real.cos y ≤ Real.sin y := by linarith
    _ ≤ |Real.sin y| := le_abs_self _

theorem cos_two_pi_sub (y : ℝ) : Real.cos (2 * Real.pi - y) = Real.cos y := by
  simp [Real.cos_sub]

theorem abs_sin_two_pi_sub (y : ℝ) : |Real.sin (2 * Real.pi - y)| = |Real.sin y| := by
  simp [Real.sin_sub, abs_neg]

/-- On `[0, 2π]`, `cos x ≤ |sin x|` holds exactly on `[π/4, 7π/4]`. -/
theorem cos_le_abs_sin_iff {x : ℝ} (h0 : 0 ≤ x) (h2 : x ≤ 2 * Real.pi) :
    Real.cos x ≤ |Real.sin x| ↔ Real.pi / 4 ≤ x ∧ x ≤ 7 * Real.pi / 4 := by
  have hpi := Real.pi_pos
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · by_contra hlt
      push_neg at hlt
      exact absurd h (not_le.mpr (abs_sin_lt_cos_of_lt_pi_div_four h0 hlt))
    · by_contra hgt
      push_neg at hgt
      have hkey := abs_sin_lt_cos_of_lt_pi_div_four
        (y := 2 * Real.pi - x) (by linarith) (by linarith)
      rw [cos_two_pi_sub, abs_sin_two_pi_sub] at hkey
      linarith
  · rintro ⟨hx1, hx2⟩
    rcases le_total x (Real.pi / 2) with h | h
    · exact cos_le_abs_sin_of_mem_pi_div_four_pi_div_two hx1 h
    · rcases le_total x (3 * Real.pi / 2) with h' | h'
      · exact le_trans (Real.cos_nonpos_of_pi_div_two_le_of_le h (by linarith)) (abs_nonneg _)
      · have hkey := cos_le_abs_sin_of_mem_pi_div_four_pi_div_two
          (y := 2 * Real.pi - x) (by linarith) (by linarith)
        rwa [cos_two_pi_sub, abs_sin_two_pi_sub] at hkey

/-- **IMO 1965, Problem 1.** For `0 ≤ x ≤ 2π`, the inequality
`2 cos x ≤ |√(1 + sin 2x) − √(1 − sin 2x)| ≤ √2` holds precisely for `x ∈ [π/4, 7π/4]`. -/
theorem imo1965_p1 {x : ℝ} (h0 : 0 ≤ x) (h2 : x ≤ 2 * Real.pi) :
    (2 * Real.cos x ≤ |Real.sqrt (1 + Real.sin (2 * x)) - Real.sqrt (1 - Real.sin (2 * x))| ∧
      |Real.sqrt (1 + Real.sin (2 * x)) - Real.sqrt (1 - Real.sin (2 * x))| ≤ Real.sqrt 2)
      ↔ x ∈ Set.Icc (Real.pi / 4) (7 * Real.pi / 4) := by
  constructor
  · rintro ⟨hl, -⟩
    rw [abs_sqrt_sub_sqrt_eq] at hl
    have hc : Real.cos x ≤ |Real.sin x| :=
      (le_min_iff.mp (by linarith : Real.cos x ≤ min |Real.sin x| |Real.cos x|)).1
    exact (cos_le_abs_sin_iff h0 h2).mp hc
  · rintro ⟨hx1, hx2⟩
    refine ⟨?_, abs_sqrt_sub_sqrt_le_sqrt_two x⟩
    rw [abs_sqrt_sub_sqrt_eq]
    have hc : Real.cos x ≤ |Real.sin x| := (cos_le_abs_sin_iff h0 h2).mpr ⟨hx1, hx2⟩
    have : Real.cos x ≤ min |Real.sin x| |Real.cos x| := le_min hc (le_abs_self _)
    linarith

end IMO1965P1
