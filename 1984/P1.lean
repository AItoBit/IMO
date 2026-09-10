import Mathlib

/-!
# IMO 1984, Problem 1 (Solution A1)

Formalization of the algebraic identity and inequality presented in Solution A1 
(from the referenced file "image_091ccd.png"):
$$(1 - 2x)(1 - 2y)(1 - 2z) = 4(yz + zx + xy) - 8xyz - 1$$
when $x + y + z = 1$, leading to:
$$yz + zx + xy - 2xyz = \frac{1}{4}(1 - 2x)(1 - 2y)(1 - 2z) + \frac{1}{4} \le \frac{7}{27}.$$
-/

namespace IMO1984A1

variable (x y z : ℝ)

/-- The target symmetric expression. -/
def target : ℝ := y * z + z * x + x * y - 2 * x * y * z

/-- Identity 1: Expansion of `(1 - 2x)(1 - 2y)(1 - 2z)` in terms of `x + y + z`
and `yz + zx + xy - 2xyz`. -/
lemma prod_expansion :
    (1 - 2 * x) * (1 - 2 * y) * (1 - 2 * z) =
      1 - 2 * (x + y + z) + 4 * (y * z + z * x + x * y) - 8 * x * y * z := by
  ring

/-- Identity 2: When `x + y + z = 1`, `(1 - 2x)(1 - 2y)(1 - 2z) = 4(yz + zx + xy) - 8xyz - 1`. -/
lemma prod_eq_four_mul_sub_one (hsum : x + y + z = 1) :
    (1 - 2 * x) * (1 - 2 * y) * (1 - 2 * z) =
      4 * (y * z + z * x + x * y) - 8 * x * y * z - 1 := by
  rw [prod_expansion, hsum]
  ring

/-- Identity 3: `yz + zx + xy - 2xyz = 1/4 (1 - 2x)(1 - 2y)(1 - 2z) + 1/4`. -/
lemma target_eq_quarter_mul_add_quarter (hsum : x + y + z = 1) :
    target x y z = (1 / 4) * ((1 - 2 * x) * (1 - 2 * y) * (1 - 2 * z)) + 1 / 4 := by
  have h := prod_eq_four_mul_sub_one x y z hsum
  dsimp [target]
  linarith

/-- The AM-GM upper bound step: $(a b c) \le ((a + b + c) / 3)^3$ for non-negative reals,
and when at least one factor is negative, the product is non-positive $\le 1/27$. -/
lemma prod_le_one_twenty_seventh (_hx : 0 ≤ x) (_hy : 0 ≤ y) (_hz : 0 ≤ z)
    (hsum : x + y + z = 1) :
    (1 - 2 * x) * (1 - 2 * y) * (1 - 2 * z) ≤ 1 / 27 := by
  -- At most one of x, y, z can be > 1/2 because x + y + z = 1
  by_cases hx_gt : 1 / 2 < x
  · have hy_le : y ≤ 1 / 2 := by linarith
    have hz_le : z ≤ 1 / 2 := by linarith
    have h1_le : 1 - 2 * x ≤ 0 := by linarith
    have h2 : 0 ≤ 1 - 2 * y := by linarith
    have h3 : 0 ≤ 1 - 2 * z := by linarith
    have hprod_neg : (1 - 2 * x) * (1 - 2 * y) * (1 - 2 * z) ≤ 0 := by
      have : (1 - 2 * x) * (1 - 2 * y) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h1_le h2
      exact mul_nonpos_of_nonpos_of_nonneg this h3
    linarith
  by_cases hy_gt : 1 / 2 < y
  · have hx_le : x ≤ 1 / 2 := by linarith
    have hz_le : z ≤ 1 / 2 := by linarith
    have h1 : 0 ≤ 1 - 2 * x := by linarith
    have h2_le : 1 - 2 * y ≤ 0 := by linarith
    have h3 : 0 ≤ 1 - 2 * z := by linarith
    have hprod_neg : (1 - 2 * x) * (1 - 2 * y) * (1 - 2 * z) ≤ 0 := by
      have : (1 - 2 * x) * (1 - 2 * y) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h1 h2_le
      exact mul_nonpos_of_nonpos_of_nonneg this h3
    linarith
  by_cases hz_gt : 1 / 2 < z
  · have hx_le : x ≤ 1 / 2 := by linarith
    have hy_le : y ≤ 1 / 2 := by linarith
    have h1 : 0 ≤ 1 - 2 * x := by linarith
    have h2 : 0 ≤ 1 - 2 * y := by linarith
    have h3_le : 1 - 2 * z ≤ 0 := by linarith
    have hprod_neg : (1 - 2 * x) * (1 - 2 * y) * (1 - 2 * z) ≤ 0 := by
      have : 0 ≤ (1 - 2 * x) * (1 - 2 * y) := mul_nonneg h1 h2
      exact mul_nonpos_of_nonneg_of_nonpos this h3_le
    linarith
  · -- All three factors are non-negative
    push Not at hx_gt hy_gt hz_gt
    set a := 1 - 2 * x
    set b := 1 - 2 * y
    set c := 1 - 2 * z
    have ha : 0 ≤ a := by linarith
    have hb : 0 ≤ b := by linarith
    have hc : 0 ≤ c := by linarith
    have habc_sum : a + b + c = 1 := by
      dsimp [a, b, c]
      linarith

    -- Direct verification: (a + b + c)^3 / 27 - abc expressed as an exact sum of squares
    have h_sos_identity : (a + b + c)^3 / 27 - a * b * c =
        (1 / 54 : ℝ) * (
          (a + b + 7 * c) * (a - b)^2 +
          (b + c + 7 * a) * (b - c)^2 +
          (c + a + 7 * b) * (c - a)^2
        ) := by ring

    have h_sos_nonneg : 0 ≤
        (1 / 54 : ℝ) * (
          (a + b + 7 * c) * (a - b)^2 +
          (b + c + 7 * a) * (b - c)^2 +
          (c + a + 7 * b) * (c - a)^2
        ) := by
      refine mul_nonneg (by norm_num) ?_
      have t1 : 0 ≤ (a + b + 7 * c) * (a - b)^2 := mul_nonneg (by linarith) (sq_nonneg _)
      have t2 : 0 ≤ (b + c + 7 * a) * (b - c)^2 := mul_nonneg (by linarith) (sq_nonneg _)
      have t3 : 0 ≤ (c + a + 7 * b) * (c - a)^2 := mul_nonneg (by linarith) (sq_nonneg _)
      linarith

    have h_diff_nonneg : 0 ≤ (a + b + c)^3 / 27 - a * b * c := by
      rwa [h_sos_identity]
    rw [habc_sum] at h_diff_nonneg
    norm_num at h_diff_nonneg
    linarith

/-- **IMO 1984, Problem 1 (Upper Bound via Solution A1)**:
$$yz + zx + xy - 2xyz \le \frac{1}{4} \cdot \frac{28}{27} = \frac{7}{27}.$$ -/
theorem imo1984_a1 (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hsum : x + y + z = 1) :
    target x y z ≤ 7 / 27 := by
  rw [target_eq_quarter_mul_add_quarter x y z hsum]
  have h_amgm := prod_le_one_twenty_seventh x y z hx hy hz hsum
  have h_bound : (1 / 4 : ℝ) * ((1 - 2 * x) * (1 - 2 * y) * (1 - 2 * z)) + 1 / 4 ≤
      (1 / 4) * (1 / 27) + 1 / 4 := by
    linarith
  have h_calc : (1 / 4 : ℝ) * (1 / 27) + 1 / 4 = 7 / 27 := by norm_num
  rwa [h_calc] at h_bound

end IMO1984A1
