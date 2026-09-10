import Mathlib

namespace Imo1982P3

/-- `a ≤ b / c` from `a * c ≤ b`, avoiding the `le_div_iff` name churn. -/
private lemma le_div_of_mul_le {a b c : ℝ} (hc : 0 < c) (h : a * c ≤ b) : a ≤ b / c := by
  have h1 : 0 ≤ (b - a * c) / c := div_nonneg (by linarith) (le_of_lt hc)
  have h2 : (b - a * c) / c = b / c - a := by field_simp
  rw [h2] at h1
  linarith

/-- **IMO 1982, Problem 3 (a).** -/
theorem imo1982_p3a (x : ℕ → ℝ) (hpos : ∀ i, 0 < x i) (hx0 : x 0 = 1)
    (hmono : ∀ i, x (i + 1) ≤ x i) :
    ∃ n : ℕ, 1 ≤ n ∧ (3.999 : ℝ) ≤ ∑ i ∈ Finset.range n, (x i) ^ 2 / x (i + 1) := by
  have hanti : ∀ i j, i ≤ j → x j ≤ x i := by
    intro i j hij
    induction j, hij using Nat.le_induction with
    | base => exact le_refl _
    | succ m _ ih => exact le_trans (hmono m) ih
  refine ⟨16000, by norm_num, ?_⟩
  -- (1) the telescoping bound
  have hb1 : 4 - 4 * x 16000 ≤ ∑ i ∈ Finset.range 16000, (x i) ^ 2 / x (i + 1) := by
    have h1 : ∀ i ∈ Finset.range 16000,
        4 * x i - 4 * x (i + 1) ≤ (x i) ^ 2 / x (i + 1) := by
      intro i _
      refine le_div_of_mul_le (hpos (i + 1)) ?_
      nlinarith [sq_nonneg (x i - 2 * x (i + 1))]
    have h2 := Finset.sum_le_sum h1
    have h3 : ∑ i ∈ Finset.range 16000, (4 * x i - 4 * x (i + 1))
        = 4 * x 0 - 4 * x 16000 := Finset.sum_range_sub' (fun i => 4 * x i) 16000
    rw [h3, hx0] at h2
    linarith
  -- (2) the crude bound
  have hb2 : (16000 : ℝ) * x 16000 ≤ ∑ i ∈ Finset.range 16000, (x i) ^ 2 / x (i + 1) := by
    have h1 : ∀ i ∈ Finset.range 16000, x 16000 ≤ (x i) ^ 2 / x (i + 1) := by
      intro i hi
      rw [Finset.mem_range] at hi
      refine le_div_of_mul_le (hpos (i + 1)) ?_
      have hxi : x 16000 ≤ x i := hanti i 16000 (le_of_lt hi)
      nlinarith [hmono i, hpos (i + 1), hpos i]
    have h2 := Finset.sum_le_sum h1
    have h4 : ∑ _i ∈ Finset.range 16000, x 16000 = (16000 : ℝ) * x 16000 := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      norm_num
    rw [h4] at h2
    exact h2
  -- combine
  have hnum : (3.999 : ℝ) = 3999 / 1000 := by norm_num
  rw [hnum]
  by_cases h : x 16000 ≤ 1 / 4000
  · linarith
  · have h' : 1 / 4000 < x 16000 := not_le.mp h
    linarith

/-- **IMO 1982, Problem 3 (b).**  The geometric sequence `(1/2)ⁱ` works. -/
theorem imo1982_p3b :
    ∃ x : ℕ → ℝ, (∀ i, 0 < x i) ∧ x 0 = 1 ∧ (∀ i, x (i + 1) ≤ x i) ∧
      ∀ n : ℕ, ∑ i ∈ Finset.range n, (x i) ^ 2 / x (i + 1) < 4 := by
  refine ⟨fun i => (1 / 2 : ℝ) ^ i, ?_, ?_, ?_, ?_⟩
  · intro i; positivity
  · norm_num
  · intro i
    dsimp only
    have hp : (0 : ℝ) < (1 / 2 : ℝ) ^ i := by positivity
    rw [pow_succ]
    nlinarith
  · intro n
    dsimp only
    have hterm : ∀ i ∈ Finset.range n,
        ((1 / 2 : ℝ) ^ i) ^ 2 / (1 / 2 : ℝ) ^ (i + 1) = 2 * (1 / 2 : ℝ) ^ i := by
      intro i _
      have hp1 : ((1 / 2 : ℝ) ^ (i + 1)) ≠ 0 := by positivity
      rw [div_eq_iff hp1, sq, pow_succ]
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum,
      geom_sum_eq (by norm_num : (1 / 2 : ℝ) ≠ 1) n]
    have hval : 2 * (((1 / 2 : ℝ) ^ n - 1) / ((1 / 2 : ℝ) - 1))
        = 4 - 4 * (1 / 2 : ℝ) ^ n := by
      rw [show ((1 : ℝ) / 2 - 1) = -(1 / 2) from by norm_num]
      field_simp
      ring
    rw [hval]
    have hp : (0 : ℝ) < (1 / 2 : ℝ) ^ n := by positivity
    linarith

end Imo1982P3
