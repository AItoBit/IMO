import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# IMO 2003, Problem 5: general inequality and equality characterization

This file uses the corrected unordered-pair coefficient (n^2 - 1) / 3.
Each pair i < j occurs once; diagonal terms are zero. For sums over all
ordered pairs, the equivalent coefficient is 2 * (n^2 - 1) / 3.


 
-/

namespace IMO2003P5
open Finset

/-- Each unordered pair occurs once; diagonal terms would be zero. -/
def spread (n : ℕ) (x : ℕ → ℝ) : ℝ :=
  ∑ j ∈ range n, ∑ i ∈ range j, |x j - x i|

def energy (n : ℕ) (x : ℕ → ℝ) : ℝ :=
  ∑ j ∈ range n, ∑ i ∈ range j, (x j - x i) ^ 2

def weight (n i : ℕ) : ℝ := 2 * (i : ℝ) + 1 - n

def IsArithmetic (n : ℕ) (x : ℕ → ℝ) : Prop :=
  ∃ a d : ℝ, ∀ i < n, x i = a + (i : ℝ) * d

lemma linear_sum (n : ℕ) (x : ℕ → ℝ) :
    (∑ j ∈ range n, ∑ i ∈ range j, (x j - x i)) =
      (∑ i ∈ range n, (2 * (i : ℝ) + 1) * x i) -
        (n : ℝ) * ∑ i ∈ range n, x i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih, sum_sub_distrib]
    simp only [sum_const, card_range, nsmul_eq_mul]
    rw [sum_range_succ, sum_range_succ]
    push_cast
    ring

lemma energy_formula (n : ℕ) (x : ℕ → ℝ) :
    energy n x = (n : ℝ) * (∑ i ∈ range n, x i ^ 2) - (∑ i ∈ range n, x i) ^ 2 := by
  induction n with
  | zero => simp [energy]
  | succ n ih =>
    change (∑ j ∈ range (n + 1), ∑ i ∈ range j, (x j - x i) ^ 2) = _
    rw [sum_range_succ]
    change energy n x + _ = _
    rw [ih]
    have he : (∑ i ∈ range n, (x n - x i) ^ 2) =
        (n : ℝ) * x n ^ 2 - 2 * x n * (∑ i ∈ range n, x i) +
          ∑ i ∈ range n, x i ^ 2 := by
      simp_rw [sub_sq, sum_add_distrib, sum_sub_distrib, ← mul_sum]
      simp
    rw [he, sum_range_succ, sum_range_succ]
    push_cast
    ring

lemma weight_succ (n i : ℕ) : weight (n + 1) i = weight n i - 1 := by
  simp [weight]; ring

lemma weight_last (n : ℕ) : weight (n + 1) n = n := by
  simp [weight]; ring

lemma weight_moments (n : ℕ) :
    (∑ i ∈ range n, weight n i) = 0 ∧
    (∑ i ∈ range n, weight n i ^ 2) = (n : ℝ) * ((n : ℝ) ^ 2 - 1) / 3 := by
  induction n with
  | zero => simp
  | succ n ih =>
    constructor
    · rw [sum_range_succ, weight_last]
      simp_rw [weight_succ, sum_sub_distrib]
      simp [ih.1]
    · rw [sum_range_succ, weight_last]
      simp_rw [weight_succ, sub_sq, sum_add_distrib, sum_sub_distrib]
      simp only [mul_one, one_pow, ← mul_sum, sum_const, card_range, nsmul_eq_mul]
      rw [ih.1, ih.2]
      push_cast
      ring

lemma spread_formula (n : ℕ) (x : ℕ → ℝ)
    (hx : ∀ i j, i ≤ j → j < n → x i ≤ x j) :
    spread n x = ∑ i ∈ range n, weight n i * x i := by
  have he : spread n x = ∑ j ∈ range n, ∑ i ∈ range j, (x j - x i) := by
    apply sum_congr rfl
    intro j hj
    apply sum_congr rfl
    intro i hi
    exact abs_of_nonneg (sub_nonneg.mpr (hx i j (mem_range.mp hi).le (mem_range.mp hj)))
  rw [he, linear_sum]
  simp_rw [weight, sub_mul, sum_sub_distrib, ← mul_sum]

lemma residual_expansion (n : ℕ) (u v : ℕ → ℝ) (d : ℝ) :
    (∑ i ∈ range n, (v i - d * u i) ^ 2) =
      (∑ i ∈ range n, v i ^ 2) - 2 * d * (∑ i ∈ range n, u i * v i) +
        d ^ 2 * (∑ i ∈ range n, u i ^ 2) := by
  calc
    _ = ∑ i ∈ range n, (v i ^ 2 - 2 * d * (u i * v i) + d ^ 2 * u i ^ 2) := by
      apply sum_congr rfl; intro i hi; ring
    _ = _ := by simp_rw [sum_add_distrib, sum_sub_distrib, ← mul_sum]

/-- Cauchy--Schwarz with its equality condition, proved by a sum of squares. -/
lemma cauchy_equality (n : ℕ) (u v : ℕ → ℝ)
    (hu : 0 < ∑ i ∈ range n, u i ^ 2) :
    (∑ i ∈ range n, u i * v i) ^ 2 ≤
        (∑ i ∈ range n, u i ^ 2) * (∑ i ∈ range n, v i ^ 2) ∧
    ((∑ i ∈ range n, u i * v i) ^ 2 =
        (∑ i ∈ range n, u i ^ 2) * (∑ i ∈ range n, v i ^ 2) ↔
      ∃ d : ℝ, ∀ i < n, v i = d * u i) := by
  let U := ∑ i ∈ range n, u i ^ 2
  let L := ∑ i ∈ range n, u i * v i
  let V := ∑ i ∈ range n, v i ^ 2
  let d := L / U
  have hU : U ≠ 0 := ne_of_gt hu
  have hid : U * (∑ i ∈ range n, (v i - d * u i) ^ 2) = U * V - L ^ 2 := by
    rw [residual_expansion]
    change U * (V - 2 * (L / U) * L + (L / U) ^ 2 * U) = U * V - L ^ 2
    field_simp
    ring
  have hs : 0 ≤ ∑ i ∈ range n, (v i - d * u i) ^ 2 :=
    sum_nonneg (fun i hi => sq_nonneg _)
  constructor
  · change L ^ 2 ≤ U * V
    nlinarith [mul_nonneg hu.le hs]
  · constructor
    · intro heq
      have hz : U * (∑ i ∈ range n, (v i - d * u i) ^ 2) = 0 := by
        rw [hid]; exact sub_eq_zero.mpr heq.symm
      have hsum := (mul_eq_zero.mp hz).resolve_left hU
      refine ⟨d, ?_⟩
      intro i hi
      have := (sum_sq_eq_zero_iff (range n) (fun i => v i - d * u i)).mp hsum i (mem_range.mpr hi)
      linarith
    · rintro ⟨c, hc⟩
      have hL : L = c * U := by
        dsimp [L, U]
        rw [mul_sum]
        apply sum_congr rfl
        intro i hi
        rw [hc i (mem_range.mp hi)]
        ring
      have hV : V = c ^ 2 * U := by
        dsimp [V, U]
        rw [mul_sum]
        apply sum_congr rfl
        intro i hi
        rw [hc i (mem_range.mp hi)]
        ring
      change L ^ 2 = U * V
      rw [hL, hV]
      ring

/-- The inequality and its sharp equality condition when n is at least two. -/
lemma main_of_two_le (n : ℕ) (hn : 2 ≤ n) (x : ℕ → ℝ)
    (hx : ∀ i j, i ≤ j → j < n → x i ≤ x j) :
    spread n x ^ 2 ≤ (((n : ℝ) ^ 2 - 1) / 3) * energy n x ∧
    (spread n x ^ 2 = (((n : ℝ) ^ 2 - 1) / 3) * energy n x ↔ IsArithmetic n x) := by
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  let μ : ℝ := (∑ i ∈ range n, x i) / n
  let v : ℕ → ℝ := fun i => x i - μ
  have hw0 := (weight_moments n).1
  have hw2 := (weight_moments n).2
  have hu : 0 < ∑ i ∈ range n, weight n i ^ 2 := by
    rw [hw2]
    have : 0 < (n : ℝ) ^ 2 - 1 := by nlinarith
    positivity
  have hsumv : (∑ i ∈ range n, v i) = 0 := by
    simp only [v, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
    dsimp [μ]
    field_simp
    ring
  have hexpand := residual_expansion n (fun _ => 1) x μ
  simp only [one_mul, one_pow, sum_const, card_range, nsmul_eq_mul, mul_one] at hexpand
  have hvar : energy n x = (n : ℝ) * (∑ i ∈ range n, v i ^ 2) := by
    rw [energy_formula]
    change _ = (n : ℝ) * (∑ i ∈ range n, (x i - μ) ^ 2)
    rw [hexpand]
    dsimp [μ]
    field_simp
    ring
  have hL : (∑ i ∈ range n, weight n i * v i) = spread n x := by
    rw [spread_formula n x hx]
    simp only [v, mul_sub, sum_sub_distrib, ← sum_mul, hw0, zero_mul, sub_zero]
  have hUV : (∑ i ∈ range n, weight n i ^ 2) * (∑ i ∈ range n, v i ^ 2) =
      (((n : ℝ) ^ 2 - 1) / 3) * energy n x := by
    rw [hw2, hvar]
    ring
  have hc := cauchy_equality n (weight n) v hu
  rw [hL, hUV] at hc
  have hshape : (∃ c : ℝ, ∀ i < n, v i = c * weight n i) ↔ IsArithmetic n x := by
    constructor
    · rintro ⟨c, hcv⟩
      refine ⟨μ + c * (1 - (n : ℝ)), 2 * c, ?_⟩
      intro i hi
      have h := hcv i hi
      dsimp [v, weight] at h
      nlinarith
    · rintro ⟨a, d, hd⟩
      let b : ℝ := a - μ + d * ((n : ℝ) - 1) / 2
      have hv : ∀ i < n, v i = (d / 2) * weight n i + b := by
        intro i hi
        dsimp [v, b, weight]
        rw [hd i hi]
        ring
      have hs : (∑ i ∈ range n, v i) =
          (d / 2) * (∑ i ∈ range n, weight n i) + (n : ℝ) * b := by
        calc
          _ = ∑ i ∈ range n, ((d / 2) * weight n i + b) := by
            apply sum_congr rfl
            intro i hi
            exact hv i (mem_range.mp hi)
          _ = _ := by simp only [sum_add_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul]
      rw [hsumv, hw0, mul_zero, zero_add] at hs
      have hb : b = 0 := (mul_eq_zero.mp hs.symm).resolve_left hn0
      refine ⟨d / 2, ?_⟩
      intro i hi
      simpa only [hb, add_zero] using hv i hi
  exact ⟨hc.1, hc.2.trans hshape⟩

/-- IMO 2003, Problem 5, with the corrected coefficient for unordered pairs.
The indices are 0-based. The sums include each pair i < j once; adding the
zero diagonal terms gives the equivalent convention i ≤ j.
The second conjunct proves equality if and only if the sequence is arithmetic. -/
theorem imo2003_p5 (n : ℕ) (hn : 0 < n) (x : ℕ → ℝ)
    (hx : ∀ i j, i ≤ j → j < n → x i ≤ x j) :
    spread n x ^ 2 ≤ (((n : ℝ) ^ 2 - 1) / 3) * energy n x ∧
    (spread n x ^ 2 = (((n : ℝ) ^ 2 - 1) / 3) * energy n x ↔ IsArithmetic n x) := by
  by_cases h1 : n = 1
  · subst n
    constructor
    · norm_num [spread, energy]
    · constructor
      · intro _
        refine ⟨x 0, 0, ?_⟩
        intro i hi
        have hi0 : i = 0 := by omega
        subst i
        simp
      · intro _
        norm_num [spread, energy]
  · exact main_of_two_le n (by omega) x hx

end IMO2003P5
