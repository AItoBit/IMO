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

/-- The quadratic `y^2 + y - 1 = 0` holds exactly for the two values `(-1 ± √5)/2`. -/
theorem imo_1963_p4_quadratic_iff (y : ℝ) :
    y ^ 2 + y - 1 = 0 ↔ y = (-1 + √5) / 2 ∨ y = (-1 - √5) / 2 := by
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  constructor
  · intro h
    have hfac : (y - (-1 + √5) / 2) * (y - (-1 - √5) / 2) = 0 := by
      have hexp : (y - (-1 + √5) / 2) * (y - (-1 - √5) / 2)
          = y ^ 2 + y - 1 + (5 - √5 ^ 2) / 4 := by ring
      rw [hexp, h, h5]; ring
    rcases mul_eq_zero.mp hfac with h' | h'
    · left; linarith
    · right; linarith
  · rintro (rfl | rfl) <;> nlinarith [h5]

/--
IMO 1963 Problem 4: find all `(x₁, …, x₅)` for which there is a real `y` with
`xᵢ + xᵢ₊₂ = y * xᵢ₊₁` for all `i` (indices reduced mod 5).

The solutions are exactly the constant tuples `(a, a, a, a, a)` (which come from `y = 2`,
and include the zero tuple, the only solution for all other values of `y`)
together with the two-parameter families `(a, b, -a + y*b, -y*a - y*b, y*a - b)`
for `y = (-1 ± √5)/2`.
-/
theorem imo_1963_p4 :
    {(x₁, x₂, x₃, x₄, x₅) |
      (x₁ : ℝ) (x₂ : ℝ) (x₃ : ℝ) (x₄ : ℝ) (x₅ : ℝ) (y : ℝ)
      (_h₀ : x₅ + x₂ = y*x₁)
      (_h₁ : x₁ + x₃ = y*x₂)
      (_h₂ : x₂ + x₄ = y*x₃)
      (_h₃ : x₃ + x₅ = y*x₄)
      (_h₄ : x₄ + x₁ = y*x₅)} =
      ({(a, a, a, a, a) | (a : ℝ)} ∪
      {(a, b, -a + y*b, -y*a - y*b, y*a - b) |
        (a : ℝ) (b : ℝ) (y : ℝ)
        (_h₀ : y = (-1 + √5) / 2 ∨ y = (-1 - √5) / 2)}) := by
  ext ⟨p₁, p₂, p₃, p₄, p₅⟩
  simp only [Set.mem_ofPred_eq, Set.mem_union, Prod.mk.injEq]
  constructor
  · rintro ⟨x₁, x₂, x₃, x₄, x₅, y, h₀, h₁, h₂, h₃, h₄, e₁, e₂, e₃, e₄, e₅⟩
    subst e₁; subst e₂; subst e₃; subst e₄; subst e₅
    -- `x₃, x₄, x₅` are determined by `x₁, x₂` and `y` via the recurrence
    have hx₃ : x₃ = y * x₂ - x₁ := by linarith
    subst hx₃
    have hx₄ : x₄ = y * (y * x₂ - x₁) - x₂ := by linear_combination h₂
    subst hx₄
    have hx₅ : x₅ = y * (y * (y * x₂ - x₁) - x₂) - (y * x₂ - x₁) := by
      linear_combination h₃
    subst hx₅
    by_cases hq : y ^ 2 + y - 1 = 0
    · -- golden ratio case: the tuple has exactly the stated shape
      right
      exact ⟨x₁, x₂, y, (imo_1963_p4_quadratic_iff y).mp hq, rfl, rfl, by ring,
        by linear_combination (-x₂) * hq,
        by linear_combination (x₁ - x₂ * (y - 1)) * hq⟩
    · -- otherwise the tuple is constant: either all zero, or `y = 2`
      left
      -- the two remaining (wrap-around) equations, factored
      have E2 : (y ^ 2 + y - 1) * (x₂ * (y - 1) - x₁) = 0 := by linear_combination h₀
      have E1 : (y ^ 2 + y - 1) * (x₂ * (y ^ 2 - y - 1) - x₁ * (y - 1)) = 0 := by
        linear_combination -h₄
      have hb2 : x₂ * (y - 1) - x₁ = 0 := by
        rcases mul_eq_zero.mp E2 with h | h
        · exact absurd h hq
        · exact h
      have hb1 : x₂ * (y ^ 2 - y - 1) - x₁ * (y - 1) = 0 := by
        rcases mul_eq_zero.mp E1 with h | h
        · exact absurd h hq
        · exact h
      have hx₁ : x₁ = x₂ * (y - 1) := by linarith
      have hy2 : x₂ * (y - 2) = 0 := by linear_combination hb1 + (y - 1) * hx₁
      rcases mul_eq_zero.mp hy2 with hb | hy
      · -- `x₂ = 0`, hence every coordinate vanishes
        have h1 : x₁ = 0 := by rw [hx₁, hb]; ring
        subst h1; subst hb
        exact ⟨0, rfl, rfl, by ring, by ring, by ring⟩
      · -- `y = 2`, hence the tuple is constant
        have hy' : y = 2 := by linarith
        subst hy'
        have h1 : x₁ = x₂ := by rw [hx₁]; ring
        refine ⟨x₁, rfl, ?_, ?_, ?_, ?_⟩ <;> linarith
  · rintro (⟨a, e₁, e₂, e₃, e₄, e₅⟩ | ⟨a, b, y, hy, e₁, e₂, e₃, e₄, e₅⟩)
    · subst e₁; subst e₂; subst e₃; subst e₄; subst e₅
      exact ⟨a, a, a, a, a, 2, by ring, by ring, by ring, by ring, by ring,
        rfl, rfl, rfl, rfl, rfl⟩
    · subst e₁; subst e₂; subst e₃; subst e₄; subst e₅
      have hq : y ^ 2 + y - 1 = 0 := (imo_1963_p4_quadratic_iff y).mpr hy
      exact ⟨a, b, -a + y * b, -y * a - y * b, y * a - b, y,
        by ring, by ring, by linear_combination (-b) * hq,
        by linear_combination (a + b) * hq, by linear_combination (-a) * hq,
        rfl, rfl, rfl, rfl, rfl⟩
