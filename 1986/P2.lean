import Mathlib

/-!
# IMO 1986, Problem 2 (Algebraic Core)

This formalizes the algebraic core of the complex plane solution
presented in "image_a168ad.png".

Let `ω` be the 120-degree rotation multiplier, satisfying `ω^2 + ω + 1 = 0`.
The net translation after 3 rotations is `Δ = -ω^2 + ω - a*ω + a`.
Since 1986/3 = 662, applying this translation 662 times gives `662 * Δ = 0`.
We prove this algebraically forces `a = -ω`, which corresponds to the
coordinates of an equilateral triangle.
-/

namespace IMO1986P2

theorem imo1986_p2_algebraic_core
    (ω a : ℂ)
    (hω_root : ω^2 + ω + 1 = 0)
    (h_cycle : 662 * (-ω^2 + ω - a * ω + a) = 0) :
    a = -ω := by

  -- Step 1: Cancel the integer multiplier from the cycle
  have h_delta : -ω^2 + ω - a * ω + a = 0 := by
    have h662 : (662 : ℂ) ≠ 0 := by norm_num
    have h_mul : (662 : ℂ) * (-ω^2 + ω - a * ω + a) = (662 : ℂ) * 0 := by
      calc (662 : ℂ) * (-ω^2 + ω - a * ω + a) = 0 := h_cycle
        _ = (662 : ℂ) * 0 := by ring
    exact mul_left_cancel₀ h662 h_mul

  -- Step 2: Factor the translation expression
  have h_factor : (a + ω) * (1 - ω) = 0 := by
    calc (a + ω) * (1 - ω) = a - a * ω + ω - ω^2 := by ring
      _ = -ω^2 + ω - a * ω + a := by ring
      _ = 0 := h_delta

  -- Step 3: Prove that 1 - ω ≠ 0 using the minimal polynomial
  have h_omega_neq_one : 1 - ω ≠ 0 := by
    intro h
    have h1 : ω = 1 := by
      calc ω = 1 - (1 - ω) := by ring
        _ = 1 - 0 := by rw [h]
        _ = 1 := by ring
    have h2 : (3 : ℂ) = 0 := by
      calc (3 : ℂ) = (1)^2 + (1) + 1 := by ring
        _ = ω^2 + ω + 1 := by rw [← h1]
        _ = 0 := hω_root
    norm_num at h2

  -- Step 4: Conclude the final coordinate value
  have h_a_omega : a + ω = 0 := by
    cases mul_eq_zero.mp h_factor with
    | inl h => exact h
    | inr h => exact False.elim (h_omega_neq_one h)

  calc a = (a + ω) - ω := by ring
    _ = 0 - ω := by rw [h_a_omega]
    _ = -ω := by ring

end IMO1986P2
