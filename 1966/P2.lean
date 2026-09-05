import Mathlib

/--
**Problem.** Let `a, b, c` be the sides of a triangle and `α, β, γ` the opposite angles
(so the angles are positive and sum to `π`, and the law of sines holds).
If `a + b = tan (γ/2) * (a * tan α + b * tan β)` then the triangle is isosceles: `a = b`.
(The hypotheses `cos α ≠ 0`, `cos β ≠ 0` express that the tangents occurring in the
statement are defined.)
-/
theorem triangle_isosceles_of_tan_identity
    (a b c α β γ : ℝ)
    (ha : 0 < a) (_hb : 0 < b) (_hc : 0 < c)
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hsum : α + β + γ = Real.pi)
    -- law of sines : a / sin α = b / sin β = c / sin γ
    (hlaw1 : a * Real.sin β = b * Real.sin α)
    (_hlaw2 : b * Real.sin γ = c * Real.sin β)
    -- the tangents appearing below are defined
    (hca : Real.cos α ≠ 0) (hcb : Real.cos β ≠ 0)
    (heq : a + b = Real.tan (γ / 2) * (a * Real.tan α + b * Real.tan β)) :
    a = b := by
  have hπ := Real.pi_pos
  have hαπ : α < Real.pi := by linarith
  have hβπ : β < Real.pi := by linarith
  have hsa : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα hαπ
  have hsb : 0 < Real.sin β := Real.sin_pos_of_pos_of_lt_pi hβ hβπ

  -- half sum and half difference of the two angles
  obtain ⟨v, u, hα2, hβ2, hvu⟩ :
      ∃ v u : ℝ, α = v + u ∧ β = v - u ∧ γ / 2 = Real.pi / 2 - v :=
    ⟨(α + β) / 2, (α - β) / 2, by ring, by ring, by linarith⟩
  have hv0 : 0 < v := by linarith
  have hvπ : v < Real.pi / 2 := by linarith
  have hu1 : u < Real.pi / 2 := by linarith
  have hu2 : -(Real.pi / 2) < u := by linarith

  have hsv : 0 < Real.sin v := Real.sin_pos_of_pos_of_lt_pi hv0 (by linarith)
  have hcu : 0 < Real.cos u := Real.cos_pos_of_mem_Ioo (Set.mem_Ioo.mpr ⟨hu2, hu1⟩)
  have hsv' : Real.sin v ≠ 0 := ne_of_gt hsv

  -- `tan (γ/2) = cot ((α+β)/2)`
  have htanγ : Real.tan (γ / 2) = Real.cos v / Real.sin v := by
    rw [hvu, Real.tan_eq_sin_div_cos, Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
  rw [htanγ] at heq
  simp only [Real.tan_eq_sin_div_cos] at heq

  -- clear the denominators
  have E0 : (a + b) * (Real.sin v * Real.cos α * Real.cos β)
      = Real.cos v * (a * Real.sin α * Real.cos β + b * Real.sin β * Real.cos α) := by
    rw [heq]
    field_simp
    try ring

  -- use the law of sines to eliminate `a`, `b`
  have E1 : a * ((Real.sin α + Real.sin β) * (Real.sin v * Real.cos α * Real.cos β))
      = a * (Real.cos v * (Real.sin α ^ 2 * Real.cos β + Real.sin β ^ 2 * Real.cos α)) := by
    linear_combination Real.sin α * E0 +
      (Real.sin v * Real.cos α * Real.cos β - Real.cos v * Real.cos α * Real.sin β) * hlaw1
  have E : (Real.sin α + Real.sin β) * (Real.sin v * Real.cos α * Real.cos β)
      = Real.cos v * (Real.sin α ^ 2 * Real.cos β + Real.sin β ^ 2 * Real.cos α) :=
    mul_left_cancel₀ (ne_of_gt ha) E1

  -- expand in terms of `v` and `u`
  rw [hα2, hβ2, Real.sin_add, Real.sin_sub, Real.cos_add, Real.cos_sub] at E
  have hU : (2 * Real.cos u) * (Real.sin u ^ 2 * (Real.sin v ^ 2 + Real.cos v ^ 2) ^ 2) = 0 := by
    linear_combination (-1 : ℝ) * E
  rw [Real.sin_sq_add_cos_sq] at hU
  have hsu : Real.sin u = 0 := by
    rcases mul_eq_zero.mp hU with h | h
    · linarith
    · exact mul_self_eq_zero.mp (by linear_combination h)

  -- hence `sin α = sin β`, and the law of sines gives `a = b`
  have hsab : Real.sin α = Real.sin β := by
    rw [hα2, hβ2, Real.sin_add, Real.sin_sub, hsu]; ring
  rw [← hsab] at hlaw1
  exact mul_right_cancel₀ (ne_of_gt hsa) hlaw1
