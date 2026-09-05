import Mathlib

open Real
open scoped BigOperators

/-- Auxiliary lemma showing the cotangent double-angle identity:
    cot θ - cot 2θ = 1 / sin 2θ. -/
lemma cot_sub_cot_double (θ : ℝ) (h1 : sin θ ≠ 0) (h2 : sin (2 * θ) ≠ 0) :
    cos θ / sin θ - cos (2 * θ) / sin (2 * θ) = 1 / sin (2 * θ) := by
  have h_sub : sin (2 * θ) * cos θ - cos (2 * θ) * sin θ = sin θ := by
    have h_trig := sin_sub (2 * θ) θ
    have h_eq : 2 * θ - θ = θ := by ring
    rw [h_eq] at h_trig
    exact h_trig.symm
  have h_cancel : sin θ * sin (2 * θ) ≠ 0 := mul_ne_zero h1 h2
  have h_frac : cos θ / sin θ - cos (2 * θ) / sin (2 * θ) =
      (sin (2 * θ) * cos θ - cos (2 * θ) * sin θ) / (sin θ * sin (2 * θ)) := by
    field_simp
  rw [h_frac, h_sub]
  field_simp

/-- **1966 IMO Problem 4**
    For any natural number `n` and real `x` such that all intermediate sines are non-zero:
    ∑_{i=1}^n 1 / sin (2^i * x) = cot x - cot (2^n * x). -/
theorem imo1966_p4 (n : ℕ) (x : ℝ) (h : ∀ t ≤ n, sin (2^t * x) ≠ 0) :
    ∑ i ∈ Finset.range n, (1 / sin (2^(i + 1) * x)) = cos x / sin x - cos (2^n * x) / sin (2^n * x) := by
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, pow_zero, one_mul, sub_self]
  | succ n ih =>
    have h_n : ∀ t ≤ n, sin (2^t * x) ≠ 0 := by
      intro t ht
      exact h t (by omega)
    have ih_spec := ih h_n
    rw [Finset.sum_range_succ, ih_spec]
    have h_pow : 2^(n + 1) * x = 2 * (2^n * x) := by
      rw [pow_add]
      simp only [pow_one]
      ring
    have h_theta1 : sin (2^n * x) ≠ 0 := h_n n (by omega)
    have h_theta2 : sin (2 * (2^n * x)) ≠ 0 := by
      rw [← h_pow]
      exact h (n + 1) (by omega)
    have h_id := cot_sub_cot_double (2^n * x) h_theta1 h_theta2
    rw [← h_pow] at h_id
    linarith
