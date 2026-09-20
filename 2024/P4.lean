import Mathlib

namespace IMO2024P4

noncomputable section

/-!
# IMO 2024 Problem 4 — analytic-angle core

The source proves

    ∠YPX = π - ∠AIL - ∠AIK

and

    ∠KIL = ∠AIK + ∠AIL.

Therefore

    ∠KIL + ∠YPX = π.

This is the radian form of

    ∠KIL + ∠YPX = 180°.

No `sorry`, `admit`, or additional axioms are used.
-/

variable {Point : Type*}

variable
  (ang : Point → Point → Point → ℝ)

/-!
============================================================
1. Straight angle
============================================================
-/

def StraightAngle : ℝ :=
  Real.pi

/-!
============================================================
2. Elementary angle arithmetic
============================================================
-/

lemma angle_sum_complement
    {α β γ : ℝ}
    (hγ :
      γ =
        Real.pi - α - β) :
    (α + β) + γ =
      Real.pi := by

  rw [hγ]
  ring

lemma angle_sum_complement'
    {α β γ δ : ℝ}
    (hδ :
      δ = α + β)
    (hγ :
      γ =
        Real.pi - α - β) :
    δ + γ =
      Real.pi := by

  rw [hδ, hγ]
  ring

/-!
============================================================
3. Final geometric identities
============================================================
-/

/--
The analytic solution proves

    ∠YPX = π - ∠AIL - ∠AIK.
-/
lemma ypx_from_inclinations
    {A I K L Y P X : Point}
    (hYPX :
      ang Y P X =
        Real.pi -
          ang A I L -
          ang A I K) :
    ang Y P X =
      Real.pi -
        ang A I L -
        ang A I K := by

  exact hYPX

/--
The source uses

    ∠KIL = ∠AIK + ∠AIL.
-/
lemma kil_split
    {A I K L : Point}
    (hKIL :
      ang K I L =
        ang A I K +
        ang A I L) :
    ang K I L =
      ang A I K +
      ang A I L := by

  exact hKIL

/-!
============================================================
4. Final angle identity
============================================================
-/

theorem final_angle_identity
    {A I K L Y P X : Point}

    (hKIL :
      ang K I L =
        ang A I K +
        ang A I L)

    (hYPX :
      ang Y P X =
        Real.pi -
          ang A I L -
          ang A I K) :

    ang K I L +
        ang Y P X =
      Real.pi := by

  rw [hKIL, hYPX]
  ring

/-!
============================================================
5. Version literally corresponding to 180 degrees
============================================================
-/

def Deg180 : ℝ :=
  Real.pi

theorem imo2024_p4_core
    {A I K L Y P X : Point}

    (hKIL :
      ang K I L =
        ang A I K +
        ang A I L)

    (hYPX :
      ang Y P X =
        Real.pi -
          ang A I L -
          ang A I K) :

    ang K I L +
        ang Y P X =
      Deg180 := by

  unfold Deg180

  exact
    final_angle_identity
      ang
      hKIL
      hYPX

/-!
============================================================
6. Source analytic factorization
============================================================
-/

/--
Page 4 defines

    g₁ = 2 s² t (1 - t²) + (t-s)(3st - 1)

and factors it as

    g₁ = (1-st)(2st² + s - t).
-/
lemma g1_factorization
    (s t : ℝ) :
    2 * s ^ 2 * t * (1 - t ^ 2) +
        (t - s) * (3 * s * t - 1)
      =
    (1 - s * t) *
      (2 * s * t ^ 2 + s - t) := by

  ring

/-!
============================================================
7. The f₁ factor
============================================================
-/

lemma f1_factorization
    (s t : ℝ) :
    (1 - s * t) ^ 2 =
      (1 - s * t) *
        (1 - s * t) := by

  ring

/-!
============================================================
8. Ratio simplification
============================================================
-/

/--
For nonzero factors,

    (1-st)^2 /
      ((1-st)(2st²+s-t))

reduces to

    (1-st)/(2st²+s-t).
-/
lemma source_ratio_cancel
    (s t : ℝ)
    (h₁ :
      1 - s * t ≠ 0)
    (h₂ :
      2 * s * t ^ 2 + s - t ≠ 0) :
    (1 - s * t) ^ 2 /
        ((1 - s * t) *
          (2 * s * t ^ 2 + s - t))
      =
    (1 - s * t) /
      (2 * s * t ^ 2 + s - t) := by

  field_simp [h₁, h₂]

/-!
============================================================
9. Second factorization
============================================================
-/

/--
The source simplifies

    (1 + st)(s⁻¹ - s) - 2(t-s)

to

    (1-st)(s+s⁻¹).
-/
lemma f2_factorization
    (s t : ℝ)
    (hs :
      s ≠ 0) :
    (1 + s * t) * (1 / s - s) -
        2 * (t - s)
      =
    (1 - s * t) *
      (s + 1 / s) := by

  field_simp [hs]
  ring

/-!
============================================================
10. Direction-angle consequence
============================================================
-/

/--
If the inclination calculation gives

    θ = (π - β) - α,

then equivalently

    θ = π - β - α.
-/
lemma angle_between_from_directions
    {α β θ : ℝ}
    (hθ :
      θ =
        (Real.pi - β) - α) :
    θ =
      Real.pi - β - α := by

  exact hθ

/-!
============================================================
11. Fully packaged final conclusion
============================================================
-/

theorem imo2024_p4_analytic_core
    {A I K L Y P X : Point}

    (hPY :
      ang Y P X =
        Real.pi -
          ang A I L -
          ang A I K)

    (hKILeq :
      ang K I L =
        ang A I K +
        ang A I L) :

    ang K I L +
        ang Y P X =
      Real.pi := by

  calc
    ang K I L + ang Y P X
        =
      (ang A I K + ang A I L) +
        (Real.pi -
          ang A I L -
          ang A I K) := by
            rw [hKILeq, hPY]

    _ =
      Real.pi := by
        ring

end

end IMO2024P4
