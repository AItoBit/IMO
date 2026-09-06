import Mathlib

open Finset
open scoped BigOperators
open Real

/--
Formalization of the algebraic core of IMO 1968 Problem 3.
Adding the equations yields a characteristic sum.
-/
lemma imo1968_p3_sum_reduction {ι : Type*} (s : Finset ι)
    (a b c : ℝ) (x y : ι → ℝ)
    (h_sys : ∀ i ∈ s, a * x i^2 + b * x i + c = y i)
    (h_sum_y : ∑ i ∈ s, y i = ∑ i ∈ s, x i) :
    ∑ i ∈ s, (a * x i^2 + (b - 1) * x i + c) = 0 := by
  calc
    ∑ i ∈ s, (a * x i^2 + (b - 1) * x i + c)
      = ∑ i ∈ s, (a * x i^2 + b * x i + c - x i) := by
        apply sum_congr rfl
        intro i _
        ring
    _ = ∑ i ∈ s, (a * x i^2 + b * x i + c) - ∑ i ∈ s, x i := by rw [sum_sub_distrib]
    _ = ∑ i ∈ s, y i - ∑ i ∈ s, x i := by
        congr 1
        apply sum_congr rfl
        intro i hi
        exact h_sys i hi
    _ = 0 := by rw [h_sum_y, sub_self]

/--
The central algebraic identity completing the square over the sum.
-/
lemma imo1968_p3_algebra {ι : Type*} (s : Finset ι)
    (a b c Δ : ℝ) (x : ι → ℝ)
    (hΔ : Δ = (b - 1)^2 - 4 * a * c)
    (h_sum : ∑ i ∈ s, (a * x i^2 + (b - 1) * x i + c) = 0) :
    ∑ i ∈ s, (2 * a * x i + b - 1)^2 = (s.card : ℝ) * Δ := by
  have h1 : ∀ i, (2 * a * x i + b - 1)^2 = 4 * a * (a * x i^2 + (b - 1) * x i + c) + Δ := by
    intro i
    rw [hΔ]
    ring
  calc
    ∑ i ∈ s, (2 * a * x i + b - 1)^2
      = ∑ i ∈ s, (4 * a * (a * x i^2 + (b - 1) * x i + c) + Δ) := sum_congr rfl (fun i _ => h1 i)
    _ = (∑ i ∈ s, 4 * a * (a * x i^2 + (b - 1) * x i + c)) + ∑ i ∈ s, Δ := by rw [sum_add_distrib]
    _ = 4 * a * (∑ i ∈ s, (a * x i^2 + (b - 1) * x i + c)) + ∑ i ∈ s, Δ := by rw [← mul_sum]
    _ = 4 * a * 0 + ∑ i ∈ s, Δ := by rw [h_sum]
    _ = ∑ i ∈ s, Δ := by ring
    _ = s.card • Δ := by rw [sum_const]
    _ = (s.card : ℝ) * Δ := by rw [nsmul_eq_mul]

/--
Part (a): If Δ < 0, there are no solutions.
-/
theorem imo1968_p3_part_a {ι : Type*} (s : Finset ι)
    (h_nonempty : s.Nonempty)
    (a b c Δ : ℝ) (x : ι → ℝ)
    (hΔ : Δ = (b - 1)^2 - 4 * a * c)
    (h_sum : ∑ i ∈ s, (a * x i^2 + (b - 1) * x i + c) = 0)
    (h_neg : Δ < 0) :
    False := by
  have h_eq := imo1968_p3_algebra s a b c Δ x hΔ h_sum
  have h_lhs : 0 ≤ ∑ i ∈ s, (2 * a * x i + b - 1)^2 := sum_nonneg (fun i _ ↦ sq_nonneg _)
  have h_rhs : (s.card : ℝ) * Δ < 0 := by
    have h_card : 0 < (s.card : ℝ) := Nat.cast_pos.mpr (Finset.Nonempty.card_pos h_nonempty)
    nlinarith
  linarith

/--
Part (b): If Δ = 0, there is exactly one (constant) solution possible.
-/
theorem imo1968_p3_part_b {ι : Type*} (s : Finset ι)
    (a b c : ℝ) (ha : a ≠ 0) (x : ι → ℝ)
    (hΔ : (b - 1)^2 - 4 * a * c = 0)
    (h_sum : ∑ i ∈ s, (a * x i^2 + (b - 1) * x i + c) = 0) :
    ∀ i ∈ s, x i = (1 - b) / (2 * a) := by
  have h_alg := imo1968_p3_algebra s a b c 0 x hΔ.symm h_sum
  rw [mul_zero] at h_alg
  
  have h_sq_nonneg : ∀ i ∈ s, (0 : ℝ) ≤ (2 * a * x i + b - 1)^2 := fun i _ ↦ sq_nonneg _
  have h_zero : ∀ i ∈ s, (2 * a * x i + b - 1)^2 = 0 := by
    intro i hi
    exact (sum_eq_zero_iff_of_nonneg h_sq_nonneg).mp h_alg i hi
  
  intro i hi
  have hi_zero := h_zero i hi
  have hi_linear : 2 * a * x i + b - 1 = 0 := sq_eq_zero_iff.mp hi_zero
  have h2a : 2 * a ≠ 0 := mul_ne_zero (by norm_num) ha
  
  calc x i = (2 * a * x i) / (2 * a) := (mul_div_cancel_left₀ (x i) h2a).symm
     _ = (1 - b) / (2 * a) := by
        congr 1
        linarith
