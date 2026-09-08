
import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Imo1976P6

/-- The sequence `u₀ = 2`, `u₁ = 5/2`, `u_{n+1} = u_n (u_{n-1}² - 2) - u₁`. -/
noncomputable def u : ℕ → ℝ
  | 0 => 2
  | 1 => 5 / 2
  | (n + 2) => u (n + 1) * ((u n) ^ 2 - 2) - 5 / 2

/-- The exponent sequence `eₙ = (2ⁿ - (-1)ⁿ)/3`, defined by the recursion
`e₀ = 0`, `e₁ = 1`, `e_{n+2} = e_{n+1} + 2 eₙ`. -/
def expo : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | (n + 2) => expo (n + 1) + 2 * expo n

@[simp] lemma expo_zero : expo 0 = 0 := rfl
@[simp] lemma expo_one : expo 1 = 1 := rfl
lemma expo_succ_succ (n : ℕ) : expo (n + 2) = expo (n + 1) + 2 * expo n := rfl

@[simp] lemma u_zero : u 0 = 2 := rfl
@[simp] lemma u_one : u 1 = 5 / 2 := rfl
lemma u_succ_succ (n : ℕ) : u (n + 2) = u (n + 1) * ((u n) ^ 2 - 2) - 5 / 2 := rfl

/-- The exponent sequence has the closed form `(2ⁿ - (-1)ⁿ)/3`. -/
lemma expo_closed (n : ℕ) : 3 * expo n = 2 ^ n - (-1) ^ n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => norm_num
  | more n ih1 ih2 =>
      rw [expo_succ_succ]
      have h1 : (2 : ℤ) ^ (n + 2) = 4 * 2 ^ n := by ring
      have h2 : (-1 : ℤ) ^ (n + 2) = (-1) ^ n := by ring
      rw [h1, h2]
      have hn1 : 3 * expo (n + 1) = 2 ^ (n + 1) - (-1) ^ (n + 1) := ih2
      have hn : 3 * expo n = 2 ^ n - (-1) ^ n := ih1
      have h3 : (2 : ℤ) ^ (n + 1) = 2 * 2 ^ n := by ring
      have h4 : (-1 : ℤ) ^ (n + 1) = -((-1) ^ n) := by ring
      rw [h3, h4] at hn1
      linarith

/-- The difference `e_{n+1} - 2 eₙ` alternates between `1` and `-1`. -/
lemma expo_diff (n : ℕ) : expo (n + 1) - 2 * expo n = (-1) ^ n := by
  have h1 : 3 * expo (n + 1) = 2 ^ (n + 1) - (-1) ^ (n + 1) := expo_closed (n + 1)
  have h2 : 3 * expo n = 2 ^ n - (-1) ^ n := expo_closed n
  have h3 : (2 : ℤ) ^ (n + 1) = 2 * 2 ^ n := by ring
  have h4 : (-1 : ℤ) ^ (n + 1) = -((-1) ^ n) := by ring
  rw [h3, h4] at h1
  linarith

lemma expo_nonneg (n : ℕ) : 0 ≤ expo n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => norm_num
  | more n ih1 ih2 => rw [expo_succ_succ]; omega

lemma expo_pos (n : ℕ) (hn : 1 ≤ n) : 1 ≤ expo n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  clear hn
  induction k with
  | zero => simp
  | succ j ih =>
      rw [expo_succ_succ]
      have := expo_nonneg j
      omega

/-- Key closed form: `uₙ = 2^{eₙ} + 2^{-eₙ}`. -/
lemma u_eq (n : ℕ) : u n = (2 : ℝ) ^ (expo n) + (2 : ℝ) ^ (-(expo n)) := by
  have h2ne : (2 : ℝ) ≠ 0 := by norm_num
  induction n using Nat.twoStepInduction with
  | zero => norm_num
  | one => norm_num
  | more n ih1 ih2 =>
      have hx : (0 : ℝ) < 2 ^ (expo n) := zpow_pos (by norm_num) _
      have hy : (0 : ℝ) < 2 ^ (expo (n + 1)) := zpow_pos (by norm_num) _
      set x : ℝ := (2 : ℝ) ^ (expo n) with hxdef
      set y : ℝ := (2 : ℝ) ^ (expo (n + 1)) with hydef
      have hxinv : (2 : ℝ) ^ (-(expo n)) = x⁻¹ := by rw [hxdef, ← zpow_neg]
      have hyinv : (2 : ℝ) ^ (-(expo (n + 1))) = y⁻¹ := by rw [hydef, ← zpow_neg]
      have hxne : x ≠ 0 := ne_of_gt hx
      have hyne : y ≠ 0 := ne_of_gt hy
      have hsq2 : (2 : ℝ) ^ (2 * expo n) = x ^ 2 := by
        rw [two_mul, zpow_add₀ h2ne, hxdef, sq]
      have hprod : (2 : ℝ) ^ (expo (n + 2)) = y * x ^ 2 := by
        rw [expo_succ_succ, zpow_add₀ h2ne, hsq2, hydef]
      have hprodinv : (2 : ℝ) ^ (-(expo (n + 2))) = (y * x ^ 2)⁻¹ := by
        rw [← hprod, ← zpow_neg]
      have hratio : y * (x ^ 2)⁻¹ + y⁻¹ * x ^ 2 = 5 / 2 := by
        have hxy : y * (x ^ 2)⁻¹ = (2 : ℝ) ^ ((-1 : ℤ) ^ n) := by
          rw [← expo_diff n, zpow_sub₀ h2ne, hsq2, div_eq_mul_inv, hydef]
        have hxy2 : y⁻¹ * x ^ 2 = ((2 : ℝ) ^ ((-1 : ℤ) ^ n))⁻¹ := by
          rw [← hxy]; field_simp
        rw [hxy, hxy2]
        rcases neg_one_pow_eq_or ℤ n with h | h <;> rw [h] <;> norm_num
      rw [u_succ_succ, ih1, ih2, hxinv, hyinv, hprod, hprodinv]
      have hsq : (x + x⁻¹) ^ 2 - 2 = x ^ 2 + (x ^ 2)⁻¹ := by
        field_simp; ring
      rw [hsq]
      have hexp : (y + y⁻¹) * (x ^ 2 + (x ^ 2)⁻¹)
          = (y * x ^ 2 + (y * x ^ 2)⁻¹) + (y * (x ^ 2)⁻¹ + y⁻¹ * x ^ 2) := by
        field_simp; ring
      rw [hexp, hratio]
      ring

/-- **IMO 1976, Problem 6.** For `n ≥ 1`, `⌊uₙ⌋ = 2^{(2ⁿ - (-1)ⁿ)/3}`, where the exponent
`m` is characterized by `3 m = 2ⁿ - (-1)ⁿ`. -/
theorem imo1976_p6 (n : ℕ) (hn : 1 ≤ n) (m : ℕ) (hm : 3 * (m : ℤ) = 2 ^ n - (-1) ^ n) :
    ⌊u n⌋ = 2 ^ m := by
  have hme : (m : ℤ) = expo n := by
    have := expo_closed n
    omega
  have hpos : 1 ≤ expo n := expo_pos n hn
  have hval : u n = (2 : ℝ) ^ (expo n) + (2 : ℝ) ^ (-(expo n)) := u_eq n
  have hint : (2 : ℝ) ^ (expo n) = ((2 ^ m : ℤ) : ℝ) := by
    rw [← hme]
    push_cast
    rw [← zpow_natCast (2 : ℝ) m]
  have hsmall1 : (0 : ℝ) < (2 : ℝ) ^ (-(expo n)) := zpow_pos (by norm_num) _
  have hsmall2 : (2 : ℝ) ^ (-(expo n)) < 1 := by
    apply zpow_lt_one_of_neg₀ (by norm_num) (by omega)
  rw [hval, hint, Int.floor_eq_iff]
  refine ⟨by push_cast; linarith, by push_cast; linarith⟩

end Imo1976P6
