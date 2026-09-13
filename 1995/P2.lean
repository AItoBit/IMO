import Mathlib.Analysis.MeanInequalities
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open scoped BigOperators

private lemma three_le_pairwise_sum (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    3 ≤ a * b + b * c + c * a := by
  have hab : 0 ≤ a * b := (mul_pos ha hb).le
  have hbc : 0 ≤ b * c := (mul_pos hb hc).le
  have hca : 0 ≤ c * a := (mul_pos hc ha).le
  have h := Real.geom_mean_le_arith_mean3_weighted
    (w₁ := (1 : ℝ) / 3) (w₂ := (1 : ℝ) / 3) (w₃ := (1 : ℝ) / 3)
    (p₁ := a * b) (p₂ := b * c) (p₃ := c * a)
    (by norm_num) (by norm_num) (by norm_num) hab hbc hca (by norm_num)
  rw [← Real.mul_rpow hab hbc,
    ← Real.mul_rpow (mul_nonneg hab hbc) hca] at h
  have hprod : (a * b) * (b * c) * (c * a) = 1 := by
    calc
      (a * b) * (b * c) * (c * a) = (a * b * c) ^ 2 := by ring
      _ = 1 := by rw [habc]; norm_num
  rw [hprod, Real.one_rpow] at h
  nlinarith

private lemma three_term_cauchy (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ((1 / a + 1 / b + 1 / c) ^ 2) /
        (a * (b + c) + b * (c + a) + c * (a + b)) ≤
      1 / (a ^ 3 * (b + c)) + 1 / (b ^ 3 * (c + a)) +
        1 / (c ^ 3 * (a + b)) := by
  let f : Fin 3 → ℝ := ![1 / a, 1 / b, 1 / c]
  let g : Fin 3 → ℝ := ![a * (b + c), b * (c + a), c * (a + b)]
  have hg : ∀ i ∈ (Finset.univ : Finset (Fin 3)), 0 < g i := by
    intro i _
    fin_cases i <;> simp [g] <;> positivity
  have h := Finset.sq_sum_div_le_sum_sq_div
    (Finset.univ : Finset (Fin 3)) f hg
  norm_num [f, g, Fin.sum_univ_succ] at h
  convert h using 1 <;>
    field_simp [ne_of_gt ha, ne_of_gt hb, ne_of_gt hc,
      ne_of_gt (add_pos hb hc), ne_of_gt (add_pos hc ha),
      ne_of_gt (add_pos ha hb)] <;> ring

theorem imo_1995_p2 (a b c : ℝ)
    (h₀ : 0 < a ∧ 0 < b ∧ 0 < c) (h₁ : a * b * c = 1) :
    (1 : ℝ) / (a ^ 3 * (b + c)) + (1 : ℝ) / (b ^ 3 * (c + a)) +
        (1 : ℝ) / (c ^ 3 * (a + b)) ≥ (3 : ℝ) / 2 := by
  rcases h₀ with ⟨ha, hb, hc⟩
  have hcauchy := three_term_cauchy a b c ha hb hc
  have hamgm := three_le_pairwise_sum a b c ha hb hc h₁
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hb0 : b ≠ 0 := ne_of_gt hb
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hinva : 1 / a = b * c := by
    apply (div_eq_iff ha0).2
    nlinarith [h₁]
  have hinvb : 1 / b = c * a := by
    apply (div_eq_iff hb0).2
    nlinarith [h₁]
  have hinvc : 1 / c = a * b := by
    apply (div_eq_iff hc0).2
    nlinarith [h₁]
  have hsum : 0 < a * b + b * c + c * a := by positivity
  have hquotient :
      ((1 / a + 1 / b + 1 / c) ^ 2) /
          (a * (b + c) + b * (c + a) + c * (a + b)) =
        (a * b + b * c + c * a) / 2 := by
    rw [hinva, hinvb, hinvc]
    field_simp [ne_of_gt hsum]
    ring
  rw [hquotient] at hcauchy
  linarith
