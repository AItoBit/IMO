import Mathlib

namespace IMO1991P1

/-- Three-variable AM–GM, first with `u` a smallest variable. -/
private theorem product_bound_of_min
    (u v w : ℝ)
    (hu : 0 ≤ u)
    (huv : u ≤ v)
    (huw : u ≤ w) :
    27 * (u * v * w) ≤ (u + v + w) ^ 3 := by
  have hd : 0 ≤ v - u := sub_nonneg.mpr huv
  have he : 0 ≤ w - u := sub_nonneg.mpr huw
  have hs : 0 ≤ v + w - 2 * u := by
    linarith
  have h :
      0 ≤
        9 * u * ((v - w) ^ 2 + (v - u) * (w - u))
          + (v + w - 2 * u) ^ 3 := by
    positivity
  nlinarith [h]

/-- Polynomial form of three-variable AM–GM. -/
theorem product_bound
    (u v w : ℝ)
    (hu : 0 ≤ u)
    (hv : 0 ≤ v)
    (hw : 0 ≤ w) :
    27 * (u * v * w) ≤ (u + v + w) ^ 3 := by
  by_cases huv : u ≤ v
  · by_cases huw : u ≤ w
    · exact product_bound_of_min u v w hu huv huw
    · have hwu : w ≤ u := by
        linarith
      have hwv : w ≤ v := by
        linarith
      have h := product_bound_of_min w u v hw hwu hwv
      nlinarith [h]
  · have hvu : v ≤ u := by
      linarith
    by_cases hvw : v ≤ w
    · have h := product_bound_of_min v u w hv hvu hvw
      nlinarith [h]
    · have hwu : w ≤ u := by
        linarith
      have hwv : w ≤ v := by
        linarith
      have h := product_bound_of_min w u v hw hwu hwv
      nlinarith [h]

/--
The algebraic inequality for the side lengths of a
nondegenerate triangle.
-/
theorem side_length_inequality
    (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (hA : a < b + c)
    (hB : b < c + a)
    (hC : c < a + b) :
    (1 : ℝ) / 4 <
        ((a + b) * (b + c) * (c + a)) /
          (a + b + c) ^ 3 ∧
      ((a + b) * (b + c) * (c + a)) /
          (a + b + c) ^ 3 ≤
        (8 : ℝ) / 27 := by
  have hs : 0 < a + b + c := by
    positivity
  have hs3 : 0 < (a + b + c) ^ 3 := by
    positivity

  have hx : 0 < b + c - a := by
    linarith
  have hy : 0 < c + a - b := by
    linarith
  have hz : 0 < a + b - c := by
    linarith

  have htriangle :
      0 < (b + c - a) * (c + a - b) * (a + b - c) :=
    mul_pos (mul_pos hx hy) hz

  have habc : 0 < a * b * c :=
    mul_pos (mul_pos ha hb) hc

  have hid :
      4 * ((a + b) * (b + c) * (c + a))
          - (a + b + c) ^ 3 =
        (b + c - a) * (c + a - b) * (a + b - c)
          + 4 * (a * b * c) := by
    ring

  have hlower :
      (a + b + c) ^ 3 <
        4 * ((a + b) * (b + c) * (c + a)) := by
    nlinarith [htriangle, habc, hid]

  have hupper :
      27 * ((a + b) * (b + c) * (c + a)) ≤
        8 * (a + b + c) ^ 3 := by
    have h :=
      product_bound (a + b) (b + c) (c + a)
        (by positivity)
        (by positivity)
        (by positivity)
    nlinarith [h]

  constructor
  · apply (lt_div_iff₀ hs3).2
    nlinarith [hlower]
  · apply (div_le_iff₀ hs3).2
    nlinarith [hupper]

/--
The product of the three ratios appearing after the
angle-bisector reduction.
-/
theorem ratio_product_inequality
    (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (hA : a < b + c)
    (hB : b < c + a)
    (hC : c < a + b) :
    (1 : ℝ) / 4 <
        ((b + c) / (a + b + c)) *
        ((c + a) / (a + b + c)) *
        ((a + b) / (a + b + c)) ∧
      ((b + c) / (a + b + c)) *
        ((c + a) / (a + b + c)) *
        ((a + b) / (a + b + c)) ≤
          (8 : ℝ) / 27 := by
  have hs : a + b + c ≠ 0 := by
    positivity

  have hid :
      ((b + c) / (a + b + c)) *
        ((c + a) / (a + b + c)) *
        ((a + b) / (a + b + c)) =
      ((a + b) * (b + c) * (c + a)) /
        (a + b + c) ^ 3 := by
    field_simp [hs] <;> ring

  rw [hid]
  exact side_length_inequality a b c ha hb hc hA hB hC

end IMO1991P1
