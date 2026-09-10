/-
# IMO 1982, Problem 2

A non-isosceles triangle `A₁A₂A₃` has sides `a₁, a₂, a₃`, with `aᵢ` opposite
`Aᵢ`.  `Mᵢ` is the midpoint of `aᵢ`, `Tᵢ` is the point where the incircle
touches `aᵢ`, and `Sᵢ` is the reflection of `Tᵢ` in the interior bisector of the
angle at `Aᵢ`.  Prove that `M₁S₁`, `M₂S₂`, `M₃S₃` are concurrent.

## Modelling

Normalise (a similarity) so that the incircle is the **unit circle centred at
`0`**.  The touch points are then unit complex numbers `u₁, u₂, u₃`, and:

* the tangent at a unit point `u` is `{z : z + u² z̄ = 2u}`, so the vertex `A₁`
  (meet of the tangents at `T₂`, `T₃`) is `A₁ = 2u₂u₃/(u₂+u₃)`;
* the bisector at `A₁` is the line `0A₁` and reflection in it is
  `z ↦ (A₁/Ā₁) z̄ = u₂u₃ z̄`, so `S₁ = u₂u₃/u₁`;
* `M₁ = (A₂+A₃)/2`.

The first two are *proved* below (`vertex_on_tangents`, `reflection`).

`P` lies on line `MᵢSᵢ` exactly when `P = Mᵢ + λ (Sᵢ - Mᵢ)` with `λ` real, i.e.
`λ̄ = λ`.  The theorem produces one `P` and one real `λ` working for all three
`i`, which is concurrency.

## Proof

With `e₁ = u₁+u₂+u₃`, `e₂ = u₁u₂+u₂u₃+u₃u₁`, `e₃ = u₁u₂u₃`, one has
`Sᵢ = e₃/uᵢ²`, `Mᵢ = uᵢ(uᵢe₂+e₃)/(uᵢ²e₁+e₃)`, and

  `P = e₂/e₁`,   `λ = e₃/(e₁e₂)`

satisfy `P - Mᵢ = λ (Sᵢ - Mᵢ)`, the identity reducing to
`uᵢe₂ = uᵢ²e₁ + e₃ - uᵢ³`.  Reality of `λ` comes from `ū = 1/u`, i.e.
`ē₁e₃ = e₂`, `ē₂e₃ = e₁`, `ē₃e₃ = 1`.

This is the homothety of Solution 2 made explicit; `e₁ ≠ 0` (the triangle is not
equilateral) is exactly the condition that it is not a translation.

## A note on the tactic style

Everything is arranged so that no `field_simp` ever has to divide by `e₂`: the
goals are first cleared with `eq_div_iff`/`div_eq_div_iff`, leaving only the
denominators `u₁, u₂, u₃, u₁+u₂, u₂+u₃, u₃+u₁, e₁`, which match the hypotheses
syntactically.  The conjugation facts are stated multiplicatively for the same
reason.
-/

import Mathlib

namespace Imo1982P2

/-- The meeting point of the tangents to the unit circle at the unit points `v`
and `w` is `2vw/(v+w)`: it lies on both tangents `z + v² z̄ = 2v` and
`z + w² z̄ = 2w`. -/
theorem vertex_on_tangents (v w : ℂ) (hv : v * (starRingEnd ℂ) v = 1)
    (hw : w * (starRingEnd ℂ) w = 1) (hvw : v + w ≠ 0) :
    (2 * v * w / (v + w)) + v ^ 2 * (starRingEnd ℂ) (2 * v * w / (v + w)) = 2 * v ∧
    (2 * v * w / (v + w)) + w ^ 2 * (starRingEnd ℂ) (2 * v * w / (v + w)) = 2 * w := by
  have hv0 : v ≠ 0 := by intro h; rw [h] at hv; simp at hv
  have hw0 : w ≠ 0 := by intro h; rw [h] at hw; simp at hw
  have cv : (starRingEnd ℂ) v = 1 / v := by field_simp; linear_combination hv
  have cw : (starRingEnd ℂ) w = 1 / w := by field_simp; linear_combination hw
  have hc : (starRingEnd ℂ) (2 * v * w / (v + w)) = 2 / (v + w) := by
    simp only [map_div₀, map_mul, map_add, map_ofNat, cv, cw]
    field_simp
    rw [← add_mul, mul_inv_cancel₀ hvw]
  rw [hc]
  constructor
  · field_simp
    ring
  · field_simp
    ring

/-- With the incircle the unit circle at `0`, reflection in the bisector `0A₁`
sends the touch point `u₁` to `u₂u₃/u₁`, which again lies on the incircle. -/
theorem reflection (u₁ u₂ u₃ : ℂ)
    (hu₁ : u₁ * (starRingEnd ℂ) u₁ = 1) (hu₂ : u₂ * (starRingEnd ℂ) u₂ = 1)
    (hu₃ : u₃ * (starRingEnd ℂ) u₃ = 1) (h23 : u₂ + u₃ ≠ 0) :
    (u₂ * u₃ / u₁) * (starRingEnd ℂ) (2 * u₂ * u₃ / (u₂ + u₃))
        = (2 * u₂ * u₃ / (u₂ + u₃)) * (starRingEnd ℂ) u₁ ∧
      (u₂ * u₃ / u₁) * (starRingEnd ℂ) (u₂ * u₃ / u₁) = 1 := by
  have hu10 : u₁ ≠ 0 := by intro h; rw [h] at hu₁; simp at hu₁
  have hu20 : u₂ ≠ 0 := by intro h; rw [h] at hu₂; simp at hu₂
  have hu30 : u₃ ≠ 0 := by intro h; rw [h] at hu₃; simp at hu₃
  have c1 : (starRingEnd ℂ) u₁ = 1 / u₁ := by field_simp; linear_combination hu₁
  have c2 : (starRingEnd ℂ) u₂ = 1 / u₂ := by field_simp; linear_combination hu₂
  have c3 : (starRingEnd ℂ) u₃ = 1 / u₃ := by field_simp; linear_combination hu₃
  have hc : (starRingEnd ℂ) (2 * u₂ * u₃ / (u₂ + u₃)) = 2 / (u₂ + u₃) := by
    simp only [map_div₀, map_mul, map_add, map_ofNat, c2, c3]
    field_simp
    rw [← add_mul, mul_inv_cancel₀ h23]
  constructor
  · rw [hc, c1]
    field_simp
    ring
  · simp only [map_div₀, map_mul, c1, c2, c3]
    field_simp

/-- **IMO 1982, Problem 2.**  The three lines `MᵢSᵢ` pass through the common
point `P = e₂/e₁`: for the *real* number `λ = e₃/(e₁e₂)` one has
`P = Mᵢ + λ (Sᵢ - Mᵢ)` for `i = 1, 2, 3`. -/
theorem imo1982_p2 (u₁ u₂ u₃ A₁ A₂ A₃ S₁ S₂ S₃ M₁ M₂ M₃ : ℂ)
    (hu₁ : u₁ * (starRingEnd ℂ) u₁ = 1) (hu₂ : u₂ * (starRingEnd ℂ) u₂ = 1)
    (hu₃ : u₃ * (starRingEnd ℂ) u₃ = 1)
    (h12 : u₁ + u₂ ≠ 0) (h23 : u₂ + u₃ ≠ 0) (h31 : u₃ + u₁ ≠ 0)
    (he1 : u₁ + u₂ + u₃ ≠ 0) (he2 : u₁ * u₂ + u₂ * u₃ + u₃ * u₁ ≠ 0)
    (hA₁ : A₁ = 2 * u₂ * u₃ / (u₂ + u₃)) (hA₂ : A₂ = 2 * u₃ * u₁ / (u₃ + u₁))
    (hA₃ : A₃ = 2 * u₁ * u₂ / (u₁ + u₂))
    (hS₁ : S₁ = u₂ * u₃ / u₁) (hS₂ : S₂ = u₃ * u₁ / u₂) (hS₃ : S₃ = u₁ * u₂ / u₃)
    (hM₁ : M₁ = (A₂ + A₃) / 2) (hM₂ : M₂ = (A₃ + A₁) / 2) (hM₃ : M₃ = (A₁ + A₂) / 2) :
    ∃ P lam : ℂ, (starRingEnd ℂ) lam = lam ∧
      P = M₁ + lam * (S₁ - M₁) ∧
      P = M₂ + lam * (S₂ - M₂) ∧
      P = M₃ + lam * (S₃ - M₃) := by
  have hu10 : u₁ ≠ 0 := by intro h; rw [h] at hu₁; simp at hu₁
  have hu20 : u₂ ≠ 0 := by intro h; rw [h] at hu₂; simp at hu₂
  have hu30 : u₃ ≠ 0 := by intro h; rw [h] at hu₃; simp at hu₃
  have c1 : (starRingEnd ℂ) u₁ = 1 / u₁ := by field_simp; linear_combination hu₁
  have c2 : (starRingEnd ℂ) u₂ = 1 / u₂ := by field_simp; linear_combination hu₂
  have c3 : (starRingEnd ℂ) u₃ = 1 / u₃ := by field_simp; linear_combination hu₃
  have hne12 : (u₁ + u₂ + u₃) * (u₁ * u₂ + u₂ * u₃ + u₃ * u₁) ≠ 0 := mul_ne_zero he1 he2
  -- conjugation of the elementary symmetric functions, stated multiplicatively
  have ce1 : (starRingEnd ℂ) (u₁ + u₂ + u₃) * (u₁ * u₂ * u₃)
      = u₁ * u₂ + u₂ * u₃ + u₃ * u₁ := by
    rw [map_add, map_add, c1, c2, c3]
    field_simp
    ring
  have ce2 : (starRingEnd ℂ) (u₁ * u₂ + u₂ * u₃ + u₃ * u₁) * (u₁ * u₂ * u₃)
      = u₁ + u₂ + u₃ := by
    rw [map_add, map_add, map_mul, map_mul, map_mul, c1, c2, c3]
    field_simp
    ring
  have ce3 : (starRingEnd ℂ) (u₁ * u₂ * u₃) * (u₁ * u₂ * u₃) = 1 := by
    rw [map_mul, map_mul, c1, c2, c3]
    field_simp
  have hcE1 : (starRingEnd ℂ) (u₁ + u₂ + u₃) ≠ 0 := by
    intro h
    rw [h, zero_mul] at ce1
    exact he2 ce1.symm
  have hcE2 : (starRingEnd ℂ) (u₁ * u₂ + u₂ * u₃ + u₃ * u₁) ≠ 0 := by
    intro h
    rw [h, zero_mul] at ce2
    exact he1 ce2.symm
  subst hA₁; subst hA₂; subst hA₃; subst hS₁; subst hS₂; subst hS₃
  subst hM₁; subst hM₂; subst hM₃
  refine ⟨(u₁ * u₂ + u₂ * u₃ + u₃ * u₁) / (u₁ + u₂ + u₃),
    u₁ * u₂ * u₃ / ((u₁ + u₂ + u₃) * (u₁ * u₂ + u₂ * u₃ + u₃ * u₁)), ?_, ?_, ?_, ?_⟩
  · -- `λ` is real
    rw [map_div₀, map_mul, div_eq_div_iff (mul_ne_zero hcE1 hcE2) hne12]
    linear_combination
      ((starRingEnd ℂ) (u₁ + u₂ + u₃) * (starRingEnd ℂ) (u₁ * u₂ + u₂ * u₃ + u₃ * u₁) *
          (u₁ * u₂ * u₃)) * ce3
      - ((starRingEnd ℂ) (u₁ + u₂ + u₃) * (starRingEnd ℂ) (u₁ * u₂ * u₃) *
          (u₁ * u₂ * u₃)) * ce2
      - ((starRingEnd ℂ) (u₁ * u₂ * u₃) * (u₁ + u₂ + u₃)) * ce1
  · have h1 : (u₁ * u₂ + u₂ * u₃ + u₃ * u₁) / (u₁ + u₂ + u₃)
        - (2 * u₃ * u₁ / (u₃ + u₁) + 2 * u₁ * u₂ / (u₁ + u₂)) / 2
        = (u₁ * u₂ * u₃ * (u₂ * u₃ / u₁
            - (2 * u₃ * u₁ / (u₃ + u₁) + 2 * u₁ * u₂ / (u₁ + u₂)) / 2))
          / ((u₁ + u₂ + u₃) * (u₁ * u₂ + u₂ * u₃ + u₃ * u₁)) := by
      rw [eq_div_iff hne12]
      field_simp
      ring
    rw [div_mul_eq_mul_div]
    linear_combination h1
  · have h1 : (u₁ * u₂ + u₂ * u₃ + u₃ * u₁) / (u₁ + u₂ + u₃)
        - (2 * u₁ * u₂ / (u₁ + u₂) + 2 * u₂ * u₃ / (u₂ + u₃)) / 2
        = (u₁ * u₂ * u₃ * (u₃ * u₁ / u₂
            - (2 * u₁ * u₂ / (u₁ + u₂) + 2 * u₂ * u₃ / (u₂ + u₃)) / 2))
          / ((u₁ + u₂ + u₃) * (u₁ * u₂ + u₂ * u₃ + u₃ * u₁)) := by
      rw [eq_div_iff hne12]
      field_simp
      ring
    rw [div_mul_eq_mul_div]
    linear_combination h1
  · have h1 : (u₁ * u₂ + u₂ * u₃ + u₃ * u₁) / (u₁ + u₂ + u₃)
        - (2 * u₂ * u₃ / (u₂ + u₃) + 2 * u₃ * u₁ / (u₃ + u₁)) / 2
        = (u₁ * u₂ * u₃ * (u₁ * u₂ / u₃
            - (2 * u₂ * u₃ / (u₂ + u₃) + 2 * u₃ * u₁ / (u₃ + u₁)) / 2))
          / ((u₁ + u₂ + u₃) * (u₁ * u₂ + u₂ * u₃ + u₃ * u₁)) := by
      rw [eq_div_iff hne12]
      field_simp
      ring
    rw [div_mul_eq_mul_div]
    linear_combination h1

end Imo1982P2
