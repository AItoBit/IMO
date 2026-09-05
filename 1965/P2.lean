import Mathlib

/-- IMO 1965, Problem 2. -/
theorem imo1965_p2
    (a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ x₁ x₂ x₃ : ℝ)
    -- (a) diagonal entries are positive
    (hp₁ : 0 < a₁₁) (hp₂ : 0 < a₂₂) (hp₃ : 0 < a₃₃)
    -- (b) off-diagonal entries are negative
    (hn₁₂ : a₁₂ < 0) (hn₁₃ : a₁₃ < 0)
    (hn₂₁ : a₂₁ < 0) (hn₂₃ : a₂₃ < 0)
    (hn₃₁ : a₃₁ < 0) (hn₃₂ : a₃₂ < 0)
    -- (c) each row sum is positive
    (hs₁ : 0 < a₁₁ + a₁₂ + a₁₃)
    (hs₂ : 0 < a₂₁ + a₂₂ + a₂₃)
    (hs₃ : 0 < a₃₁ + a₃₂ + a₃₃)
    (e₁ : a₁₁ * x₁ + a₁₂ * x₂ + a₁₃ * x₃ = 0)
    (e₂ : a₂₁ * x₁ + a₂₂ * x₂ + a₂₃ * x₃ = 0)
    (e₃ : a₃₁ * x₁ + a₃₂ * x₂ + a₃₃ * x₃ = 0) :
    x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0 := by
  -- Key step: if `y₁` is the largest coordinate, its own equation forces `y₁ ≤ 0`.
  -- Indeed `bⱼ < 0` and `yⱼ ≤ y₁` give `bⱼ * yⱼ ≥ bⱼ * y₁`, hence
  -- `0 = b₁y₁ + b₂y₂ + b₃y₃ ≥ (b₁ + b₂ + b₃) * y₁ > 0` if `y₁ > 0`.
  have key : ∀ b₁ b₂ b₃ y₁ y₂ y₃ : ℝ, 0 < b₁ → b₂ < 0 → b₃ < 0 →
      0 < b₁ + b₂ + b₃ → b₁ * y₁ + b₂ * y₂ + b₃ * y₃ = 0 →
      y₂ ≤ y₁ → y₃ ≤ y₁ → y₁ ≤ 0 := by
    intro b₁ b₂ b₃ y₁ y₂ y₃ hb₁ hb₂ hb₃ hs he h₂ h₃
    by_contra hy
    push_neg at hy
    nlinarith [mul_nonneg (neg_nonneg.mpr hb₂.le) (sub_nonneg.mpr h₂),
               mul_nonneg (neg_nonneg.mpr hb₃.le) (sub_nonneg.mpr h₃),
               mul_pos hs hy]
  -- "the maximum is ≤ 0", instantiated at each row
  have k₁ : x₂ ≤ x₁ → x₃ ≤ x₁ → x₁ ≤ 0 := fun h₂ h₃ =>
    key a₁₁ a₁₂ a₁₃ x₁ x₂ x₃ hp₁ hn₁₂ hn₁₃ hs₁ e₁ h₂ h₃
  have k₂ : x₁ ≤ x₂ → x₃ ≤ x₂ → x₂ ≤ 0 := fun h₁ h₃ =>
    key a₂₂ a₂₁ a₂₃ x₂ x₁ x₃ hp₂ hn₂₁ hn₂₃ (by linarith) (by linear_combination e₂) h₁ h₃
  have k₃ : x₁ ≤ x₃ → x₂ ≤ x₃ → x₃ ≤ 0 := fun h₁ h₂ =>
    key a₃₃ a₃₁ a₃₂ x₃ x₁ x₂ hp₃ hn₃₁ hn₃₂ (by linarith) (by linear_combination e₃) h₁ h₂
  -- "the minimum is ≥ 0", obtained by applying the same lemma to `-x`
  have m₁ : x₁ ≤ x₂ → x₁ ≤ x₃ → 0 ≤ x₁ := fun h₂ h₃ => by
    have := key a₁₁ a₁₂ a₁₃ (-x₁) (-x₂) (-x₃) hp₁ hn₁₂ hn₁₃ hs₁
      (by linear_combination -e₁) (by linarith) (by linarith)
    linarith
  have m₂ : x₂ ≤ x₁ → x₂ ≤ x₃ → 0 ≤ x₂ := fun h₁ h₃ => by
    have := key a₂₂ a₂₁ a₂₃ (-x₂) (-x₁) (-x₃) hp₂ hn₂₁ hn₂₃ (by linarith)
      (by linear_combination -e₂) (by linarith) (by linarith)
    linarith
  have m₃ : x₃ ≤ x₁ → x₃ ≤ x₂ → 0 ≤ x₃ := fun h₁ h₂ => by
    have := key a₃₃ a₃₁ a₃₂ (-x₃) (-x₁) (-x₂) hp₃ hn₃₁ hn₃₂ (by linarith)
      (by linear_combination -e₃) (by linarith) (by linarith)
    linarith
  -- Case split on which coordinate is largest / smallest.
  have hle : x₁ ≤ 0 ∧ x₂ ≤ 0 ∧ x₃ ≤ 0 := by
    rcases le_total x₁ x₂ with h | h
    · rcases le_total x₂ x₃ with h' | h'
      · have h₃ := k₃ (by linarith) h'
        exact ⟨by linarith, by linarith, h₃⟩
      · have h₂ := k₂ h h'
        exact ⟨by linarith, h₂, by linarith⟩
    · rcases le_total x₁ x₃ with h' | h'
      · have h₃ := k₃ h' (by linarith)
        exact ⟨by linarith, by linarith, h₃⟩
      · have h₁ := k₁ h h'
        exact ⟨h₁, by linarith, by linarith⟩
  have hge : 0 ≤ x₁ ∧ 0 ≤ x₂ ∧ 0 ≤ x₃ := by
    rcases le_total x₁ x₂ with h | h
    · rcases le_total x₁ x₃ with h' | h'
      · have h₁ := m₁ h h'
        exact ⟨h₁, by linarith, by linarith⟩
      · have h₃ := m₃ h' (by linarith)
        exact ⟨by linarith, by linarith, h₃⟩
    · rcases le_total x₂ x₃ with h' | h'
      · have h₂ := m₂ h h'
        exact ⟨by linarith, h₂, by linarith⟩
      · have h₃ := m₃ (by linarith) h'
        exact ⟨by linarith, by linarith, h₃⟩
  exact ⟨le_antisymm hle.1 hge.1, le_antisymm hle.2.1 hge.2.1,
         le_antisymm hle.2.2 hge.2.2⟩
