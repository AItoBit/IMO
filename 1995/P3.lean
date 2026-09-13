import Mathlib

/-!
# Signed areas in the plane and the "no two equal labels" lemma
-/

namespace EqualAreaLabelling

/-- Twice the signed area of the triangle `P Q R`. -/
def sdet (P Q R : ℝ × ℝ) : ℝ :=
  (Q.1 - P.1) * (R.2 - P.2) - (Q.2 - P.2) * (R.1 - P.1)

/-- The (unsigned) area of the triangle `P Q R`. -/
noncomputable def area (P Q R : ℝ × ℝ) : ℝ := |sdet P Q R| / 2

theorem sdet_swap12 (P Q R : ℝ × ℝ) : sdet Q P R = -sdet P Q R := by
  simp only [sdet]; ring

theorem sdet_swap13 (P Q R : ℝ × ℝ) : sdet R Q P = -sdet P Q R := by
  simp only [sdet]; ring

theorem sdet_swap23 (P Q R : ℝ × ℝ) : sdet P R Q = -sdet P Q R := by
  simp only [sdet]; ring

/-- The alternating sum of the four signed areas determined by four points
vanishes. -/
theorem sdet_alternating (P Q R S : ℝ × ℝ) :
    sdet Q R S - sdet P R S + sdet P Q S - sdet P Q R = 0 := by
  simp only [sdet]; ring

theorem area_nonneg (P Q R : ℝ × ℝ) : 0 ≤ area P Q R := by
  simp only [area]
  positivity

theorem area_pos {P Q R : ℝ × ℝ} (h : sdet P Q R ≠ 0) : 0 < area P Q R := by
  simp only [area]
  have : 0 < |sdet P Q R| := abs_pos.mpr h
  linarith

theorem abs_sdet_eq {P Q R : ℝ × ℝ} : |sdet P Q R| = 2 * area P Q R := by
  simp only [area]; ring

/-- Two vectors both parallel to a nonzero vector are parallel. -/
theorem cross_trans {p₁ p₂ q₁ q₂ w₁ w₂ : ℝ} (hw : ¬(w₁ = 0 ∧ w₂ = 0))
    (h₁ : p₁ * w₂ - p₂ * w₁ = 0) (h₂ : q₁ * w₂ - q₂ * w₁ = 0) :
    p₁ * q₂ - p₂ * q₁ = 0 := by
  have e₁ : (p₁ * q₂ - p₂ * q₁) * w₁ = 0 := by linear_combination q₁ * h₁ - p₁ * h₂
  have e₂ : (p₁ * q₂ - p₂ * q₁) * w₂ = 0 := by linear_combination q₂ * h₁ - p₂ * h₂
  by_cases hw₁ : w₁ = 0
  · have hw₂ : w₂ ≠ 0 := fun h => hw ⟨hw₁, h⟩
    exact (mul_eq_zero.mp e₂).resolve_right hw₂
  · exact (mul_eq_zero.mp e₁).resolve_right hw₁

/-- If `U ≠ V` and both `XY` and `XZ` are parallel to `UV`, then `X`, `Y`, `Z`
are collinear. -/
theorem collinear_of_parallel {X Y Z U V : ℝ × ℝ} (hUV : U ≠ V)
    (h₁ : sdet X Y U - sdet X Y V = 0) (h₂ : sdet X Z U - sdet X Z V = 0) :
    sdet X Y Z = 0 := by
  have hw : ¬(U.1 - V.1 = 0 ∧ U.2 - V.2 = 0) := by
    rintro ⟨a, b⟩
    exact hUV (Prod.ext (by linarith) (by linarith))
  have key := cross_trans (p₁ := Y.1 - X.1) (p₂ := Y.2 - X.2)
    (q₁ := Z.1 - X.1) (q₂ := Z.2 - X.2) (w₁ := U.1 - V.1) (w₂ := U.2 - V.2) hw
    (by simp only [sdet] at h₁ ⊢; linarith [h₁]) (by simp only [sdet] at h₂ ⊢; linarith [h₂])
  simp only [sdet]
  linarith [key]

/-- If the midpoint of `UV` lies on both line `XY` and line `XZ`, then either
`X`, `U`, `V` are collinear (the midpoint is `X`) or `X`, `Y`, `Z` are
collinear. -/
theorem collinear_of_midpoint {X Y Z U V : ℝ × ℝ} (hX : sdet X U V ≠ 0)
    (h₁ : sdet X Y U + sdet X Y V = 0) (h₂ : sdet X Z U + sdet X Z V = 0) :
    sdet X Y Z = 0 := by
  have hw : ¬(U.1 + V.1 - 2 * X.1 = 0 ∧ U.2 + V.2 - 2 * X.2 = 0) := by
    rintro ⟨a, b⟩
    exact hX (by
      simp only [sdet]
      linear_combination (U.1 - X.1) * b - (U.2 - X.2) * a)
  have key := cross_trans (p₁ := Y.1 - X.1) (p₂ := Y.2 - X.2)
    (q₁ := Z.1 - X.1) (q₂ := Z.2 - X.2)
    (w₁ := U.1 + V.1 - 2 * X.1) (w₂ := U.2 + V.2 - 2 * X.2) hw
    (by simp only [sdet] at h₁ ⊢; linarith [h₁]) (by simp only [sdet] at h₂ ⊢; linarith [h₂])
  simp only [sdet]
  linarith [key]


/-- **No two labels can be equal.**  Suppose `U` and `V` carry the same label,
so that for each of the three pairs taken from `X`, `Y`, `Z` the triangles on
that pair with apex `U` and with apex `V` have equal areas.  If `X`, `Y`, `Z`
are not collinear and none of `X`, `Y`, `Z` is collinear with `U` and `V`, this
is impossible. -/
theorem labels_not_equal {X Y Z U V : ℝ × ℝ}
    (hXYZ : sdet X Y Z ≠ 0) (hXUV : sdet X U V ≠ 0) (hYUV : sdet Y U V ≠ 0)
    (hZUV : sdet Z U V ≠ 0)
    (h₁ : area X Y U = area X Y V) (h₂ : area X Z U = area X Z V)
    (h₃ : area Y Z U = area Y Z V) : False := by
  have hUV : U ≠ V := by
    rintro rfl
    exact hXUV (by simp only [sdet]; ring)
  have habs : ∀ {P Q : ℝ × ℝ}, area P Q U = area P Q V →
      sdet P Q U = sdet P Q V ∨ sdet P Q U = -sdet P Q V := by
    intro P Q h
    exact abs_eq_abs.mp (by rw [abs_sdet_eq, abs_sdet_eq, h])
  have d₁ := habs h₁
  have d₂ := habs h₂
  have d₃ := habs h₃
  rcases d₁ with e₁ | e₁ <;> rcases d₂ with e₂ | e₂ <;> rcases d₃ with e₃ | e₃
  · -- all three pairs parallel to `UV`: use the pairs `XY`, `XZ`
    exact hXYZ (collinear_of_parallel hUV (by linarith) (by linarith))
  · exact hXYZ (collinear_of_parallel hUV (by linarith) (by linarith))
  · -- `XY` and `YZ` parallel to `UV`
    have key : sdet Y X Z = 0 :=
      collinear_of_parallel hUV
        (by simp only [sdet] at e₁ ⊢; linarith) (by linarith)
    exact hXYZ (by simp only [sdet] at key ⊢; linarith)
  · -- the midpoint of `UV` lies on `XZ` and on `YZ`
    have key : sdet Z X Y = 0 :=
      collinear_of_midpoint hZUV
        (by simp only [sdet] at e₂ ⊢; linarith) (by simp only [sdet] at e₃ ⊢; linarith)
    exact hXYZ (by simp only [sdet] at key ⊢; linarith)
  · -- `XZ` and `YZ` parallel to `UV`
    have key : sdet Z X Y = 0 :=
      collinear_of_parallel hUV
        (by simp only [sdet] at e₂ ⊢; linarith) (by simp only [sdet] at e₃ ⊢; linarith)
    exact hXYZ (by simp only [sdet] at key ⊢; linarith)
  · -- the midpoint of `UV` lies on `XY` and on `YZ`
    have key : sdet Y X Z = 0 :=
      collinear_of_midpoint hYUV
        (by simp only [sdet] at e₁ ⊢; linarith) (by linarith)
    exact hXYZ (by simp only [sdet] at key ⊢; linarith)
  · -- the midpoint of `UV` lies on `XY` and on `XZ`
    exact hXYZ (collinear_of_midpoint hXUV (by linarith) (by linarith))
  · exact hXYZ (collinear_of_midpoint hXUV (by linarith) (by linarith))

end EqualAreaLabelling
