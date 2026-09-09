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

/-!
# IMO 1979, Problem 3

*Two circles in a plane intersect. `A` is one of the points of intersection. Starting
simultaneously from `A` two points move with constant speed, each travelling along its own circle
in the same sense. The two points return to `A` simultaneously after one revolution. Prove that
there is a fixed point `P` in the plane such that the two points are always equidistant from `P`.*

The plane is modelled as `ℂ`. A circle through `A` with centre `O` is the circle of radius
`‖A - O‖` about `O`; a point that starts at `A` at time `t = 0`, travels with constant speed in
the positive sense and completes one revolution in one unit of time is then

`imo1979P3Motion O A t = O + (A - O) * exp (2 * π * t * I)`.

Two *distinct* circles that meet at a common point `A` necessarily have distinct centres, which is
the hypothesis `O₁ ≠ O₂`.

The required fixed point is `imo1979P3Point O₁ O₂ A`.
-/

namespace Imo1979P3

open Complex

/-- The position at time `t` of a point that starts at `A`, moves along the circle with centre `O`
through `A` in the positive sense with constant speed, and makes exactly one revolution per unit of
time. -/
noncomputable def imo1979P3Motion (O A : ℂ) (t : ℝ) : ℂ :=
  O + (A - O) * Complex.exp ((2 * Real.pi * t : ℝ) * Complex.I)

/-- The fixed point equidistant from the two moving points, for the two circles with centres
`O₁ ≠ O₂` meeting at `A`. -/
noncomputable def imo1979P3Point (O₁ O₂ A : ℂ) : ℂ :=
  A + ((Complex.normSq (A - O₂) - Complex.normSq (A - O₁) : ℝ) : ℂ) /
      (starRingEnd ℂ) (O₂ - O₁)

/-- Both moving points start at `A`. -/
theorem imo1979P3Motion_zero (O A : ℂ) : imo1979P3Motion O A 0 = A := by
  simp [imo1979P3Motion]

/-- Both moving points are back at `A` after one revolution. -/
theorem imo1979P3Motion_one (O A : ℂ) : imo1979P3Motion O A 1 = A := by
  simp [imo1979P3Motion, Complex.exp_two_pi_mul_I]

/-- A moving point indeed travels on the circle centred at `O` through `A`. -/
theorem dist_imo1979P3Motion_center (O A : ℂ) (t : ℝ) :
    dist (imo1979P3Motion O A t) O = dist A O := by
  rw [Complex.dist_eq, Complex.dist_eq, imo1979P3Motion]
  have h0 : O + (A - O) * Complex.exp ((2 * Real.pi * t : ℝ) * Complex.I) - O
      = (A - O) * Complex.exp ((2 * Real.pi * t : ℝ) * Complex.I) := by ring
  rw [h0, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

/-- The purely algebraic identity underlying the solution. -/
private theorem key_identity (r₁ s₁ r₂ s₂ x y u v N : ℂ) (hu : u * v = 1)
    (hx : x * (s₁ - s₂) = N) (hy : y * (r₁ - r₂) = N) (hN : N = r₂ * s₂ - r₁ * s₁) :
    (r₁ * (u - 1) - x) * (s₁ * (v - 1) - y) = (r₂ * (u - 1) - x) * (s₂ * (v - 1) - y) := by
  linear_combination (r₁ * s₁ - r₂ * s₂) * hu + (1 - v) * hx + (1 - u) * hy +
    (2 - u - v) * hN

/-- **IMO 1979, Problem 3.** There is a fixed point `P` in the plane from which the two moving
points are always equidistant. -/
theorem imo1979_p3 (O₁ O₂ A : ℂ) (h : O₁ ≠ O₂) :
    ∃ P : ℂ, ∀ t : ℝ,
      dist (imo1979P3Motion O₁ A t) P = dist (imo1979P3Motion O₂ A t) P := by
  refine ⟨imo1979P3Point O₁ O₂ A, fun t => ?_⟩
  set P : ℂ := imo1979P3Point O₁ O₂ A with hPdef
  set d : ℂ := O₂ - O₁ with hddef
  have hd : d ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  have hdc : (starRingEnd ℂ) d ≠ 0 := by
    simpa using hd
  set N : ℂ := ((Complex.normSq (A - O₂) - Complex.normSq (A - O₁) : ℝ) : ℂ) with hNdef
  -- the two defining properties of `P`
  have hx : (P - A) * (starRingEnd ℂ) d = N := by
    have : P - A = N / (starRingEnd ℂ) d := by
      rw [hPdef, imo1979P3Point, hNdef, hddef]; ring
    rw [this, div_mul_cancel₀ _ hdc]
  have hNconj : (starRingEnd ℂ) N = N := by
    rw [hNdef]; exact Complex.conj_ofReal _
  have hy : (starRingEnd ℂ) (P - A) * d = N := by
    have := congrArg (starRingEnd ℂ) hx
    simpa [map_mul, hNconj, mul_comm] using this
  have hN : N = (A - O₂) * (starRingEnd ℂ) (A - O₂) - (A - O₁) * (starRingEnd ℂ) (A - O₁) := by
    rw [Complex.mul_conj, Complex.mul_conj, hNdef]; push_cast; ring
  -- reduce to an identity between squared distances
  set u : ℂ := Complex.exp ((2 * Real.pi * t : ℝ) * Complex.I) with hudef
  have hu : u * (starRingEnd ℂ) u = 1 := by
    rw [Complex.mul_conj]
    have : ‖u‖ = 1 := by rw [hudef]; exact Complex.norm_exp_ofReal_mul_I _
    have h2 : ‖u‖ ^ 2 = Complex.normSq u := Complex.sq_norm u
    rw [this] at h2
    simp [← h2]
  have hB : imo1979P3Motion O₁ A t - P = (A - O₁) * (u - 1) - (P - A) := by
    rw [imo1979P3Motion, ← hudef]; ring
  have hC : imo1979P3Motion O₂ A t - P = (A - O₂) * (u - 1) - (P - A) := by
    rw [imo1979P3Motion, ← hudef]; ring
  have main : (imo1979P3Motion O₁ A t - P) * (starRingEnd ℂ) (imo1979P3Motion O₁ A t - P)
      = (imo1979P3Motion O₂ A t - P) * (starRingEnd ℂ) (imo1979P3Motion O₂ A t - P) := by
    rw [hB, hC]
    have e1 : (starRingEnd ℂ) ((A - O₁) * (u - 1) - (P - A))
        = (starRingEnd ℂ) (A - O₁) * ((starRingEnd ℂ) u - 1) - (starRingEnd ℂ) (P - A) := by
      simp [map_sub, map_mul]
    have e2 : (starRingEnd ℂ) ((A - O₂) * (u - 1) - (P - A))
        = (starRingEnd ℂ) (A - O₂) * ((starRingEnd ℂ) u - 1) - (starRingEnd ℂ) (P - A) := by
      simp [map_sub, map_mul]
    rw [e1, e2]
    refine key_identity (A - O₁) ((starRingEnd ℂ) (A - O₁)) (A - O₂) ((starRingEnd ℂ) (A - O₂))
      (P - A) ((starRingEnd ℂ) (P - A)) u ((starRingEnd ℂ) u) N hu ?_ ?_ hN
    · have : (starRingEnd ℂ) (A - O₁) - (starRingEnd ℂ) (A - O₂) = (starRingEnd ℂ) d := by
        rw [hddef, ← map_sub]; ring_nf
      rw [this]; exact hx
    · have : (A - O₁) - (A - O₂) = d := by rw [hddef]; ring
      rw [this]; exact hy
  rw [Complex.mul_conj, Complex.mul_conj] at main
  have hsq : Complex.normSq (imo1979P3Motion O₁ A t - P)
      = Complex.normSq (imo1979P3Motion O₂ A t - P) := by exact_mod_cast main
  rw [Complex.dist_eq, Complex.dist_eq, ← Real.sqrt_sq (norm_nonneg _),
    ← Real.sqrt_sq (norm_nonneg (imo1979P3Motion O₂ A t - P)), Complex.sq_norm, Complex.sq_norm,
    hsq]

end Imo1979P3
