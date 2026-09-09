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
# IMO 1979 Problem 5

Determine all real numbers `a` for which there exist non-negative reals
`x₁, …, x₅` satisfying

`∑ k x_k = a`,  `∑ k³ x_k = a²`,  `∑ k⁵ x_k = a³`.

The answer is `a ∈ {0, 1, 4, 9, 16, 25}`.
-/

namespace Imo1979P5

/-- The three defining relations for a candidate value `a`, with the non-negative
reals `x₁, …, x₅` given as the values at `1, …, 5` of a function `x : ℕ → ℝ`. -/
def Sols (a : ℝ) : Prop :=
  ∃ x : ℕ → ℝ, (∀ k ∈ Finset.Icc 1 5, 0 ≤ x k) ∧
    (∑ k ∈ Finset.Icc (1 : ℕ) 5, (k : ℝ) * x k = a) ∧
    (∑ k ∈ Finset.Icc (1 : ℕ) 5, (k : ℝ) ^ 3 * x k = a ^ 2) ∧
    (∑ k ∈ Finset.Icc (1 : ℕ) 5, (k : ℝ) ^ 5 * x k = a ^ 3)

/-- Expansion of a sum over `{1, …, 5}`. -/
lemma sum_Icc_one_five (f : ℕ → ℝ) :
    ∑ k ∈ Finset.Icc (1 : ℕ) 5, f k = f 1 + f 2 + f 3 + f 4 + f 5 := by
  simp [Finset.sum_Icc_succ_top]

/-- If `a > 0` and `a * (a - p) * (a - q) ≥ 0`, then `a ≤ p` or `q ≤ a`. -/
lemma le_or_ge_of_mul_nonneg {a p q : ℝ} (ha : 0 < a)
    (h : 0 ≤ a * (a - p) * (a - q)) : a ≤ p ∨ q ≤ a := by
  rcases le_or_gt a p with hp | hp
  · exact Or.inl hp
  · right
    by_contra hq
    push_neg at hq
    exact absurd h (not_le.mpr (mul_neg_of_pos_of_neg (mul_pos ha (sub_pos.mpr hp))
      (by linarith)))

end Imo1979P5

open Imo1979P5 in
/-- **IMO 1979, Problem 5.**  The real numbers `a` for which there exist non-negative
reals `x₁, …, x₅` with `∑ k x_k = a`, `∑ k³ x_k = a²` and `∑ k⁵ x_k = a³` are exactly
`0, 1, 4, 9, 16, 25`. -/
theorem imo1979_p5 (a : ℝ) :
    Sols a ↔ a = 0 ∨ a = 1 ∨ a = 4 ∨ a = 9 ∨ a = 16 ∨ a = 25 := by
  constructor
  · rintro ⟨x, hx, h1, h2, h3⟩
    have hx1 : 0 ≤ x 1 := hx 1 (by decide)
    have hx2 : 0 ≤ x 2 := hx 2 (by decide)
    have hx3 : 0 ≤ x 3 := hx 3 (by decide)
    have hx4 : 0 ≤ x 4 := hx 4 (by decide)
    have hx5 : 0 ≤ x 5 := hx 5 (by decide)
    rw [sum_Icc_one_five] at h1 h2 h3
    norm_num at h1 h2 h3
    -- `a` is non-negative
    have ha0 : 0 ≤ a := by linarith
    -- `Σ(n, n+1) ≥ 0` for `n = 0, 1, 2, 3, 4`
    have k0 : 0 ≤ a * (a - 0) * (a - 1) := by nlinarith
    have k1 : 0 ≤ a * (a - 1) * (a - 4) := by nlinarith
    have k2 : 0 ≤ a * (a - 4) * (a - 9) := by nlinarith
    have k3 : 0 ≤ a * (a - 9) * (a - 16) := by nlinarith
    have k4 : 0 ≤ a * (a - 16) * (a - 25) := by nlinarith
    -- `Σ(0,5) ≤ 0`
    have hu : a ^ 3 - 25 * a ^ 2 ≤ 0 := by nlinarith
    rcases eq_or_lt_of_le ha0 with hpos | hpos
    · exact Or.inl hpos.symm
    -- now `a > 0`
    have hle : a ≤ 25 := by nlinarith
    have c0 := le_or_ge_of_mul_nonneg hpos k0
    have c1 := le_or_ge_of_mul_nonneg hpos k1
    have c2 := le_or_ge_of_mul_nonneg hpos k2
    have c3 := le_or_ge_of_mul_nonneg hpos k3
    have c4 := le_or_ge_of_mul_nonneg hpos k4
    rcases c0 with h | h
    · linarith
    rcases c1 with h' | h'
    · exact Or.inr (Or.inl (le_antisymm h' h))
    rcases c2 with h'' | h''
    · exact Or.inr (Or.inr (Or.inl (le_antisymm h'' h')))
    rcases c3 with h₃ | h₃
    · exact Or.inr (Or.inr (Or.inr (Or.inl (le_antisymm h₃ h''))))
    rcases c4 with h₄ | h₄
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (le_antisymm h₄ h₃)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (le_antisymm hle h₄)))))
  · intro h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨fun _ => 0, by norm_num, by rw [sum_Icc_one_five]; norm_num,
        by rw [sum_Icc_one_five]; norm_num, by rw [sum_Icc_one_five]; norm_num⟩
    · exact ⟨fun k => if k = 1 then 1 else 0, by intro k _; dsimp only; split <;> norm_num,
        by rw [sum_Icc_one_five]; norm_num, by rw [sum_Icc_one_five]; norm_num,
        by rw [sum_Icc_one_five]; norm_num⟩
    · exact ⟨fun k => if k = 2 then 2 else 0, by intro k _; dsimp only; split <;> norm_num,
        by rw [sum_Icc_one_five]; norm_num, by rw [sum_Icc_one_five]; norm_num,
        by rw [sum_Icc_one_five]; norm_num⟩
    · exact ⟨fun k => if k = 3 then 3 else 0, by intro k _; dsimp only; split <;> norm_num,
        by rw [sum_Icc_one_five]; norm_num, by rw [sum_Icc_one_five]; norm_num,
        by rw [sum_Icc_one_five]; norm_num⟩
    · exact ⟨fun k => if k = 4 then 4 else 0, by intro k _; dsimp only; split <;> norm_num,
        by rw [sum_Icc_one_five]; norm_num, by rw [sum_Icc_one_five]; norm_num,
        by rw [sum_Icc_one_five]; norm_num⟩
    · exact ⟨fun k => if k = 5 then 5 else 0, by intro k _; dsimp only; split <;> norm_num,
        by rw [sum_Icc_one_five]; norm_num, by rw [sum_Icc_one_five]; norm_num,
        by rw [sum_Icc_one_five]; norm_num⟩
