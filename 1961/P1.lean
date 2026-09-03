import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# IMO 1961 Problem 1

Solve the following equations for `x, y, z`:
`x + y + z = a`, `x^2 + y^2 + z^2 = b^2`, `x * y = z^2`.
What conditions must `a` and `b` satisfy for `x, y, z` to be distinct positive numbers?

The answer is `a > 0` together with `b^2 < a^2 < 3 * b^2`.

The originally proposed formalization omitted the condition `a > 0`; that version of the
statement is false (see `imo_1961_p1_without_pos_false` below), so the corrected statement
`imo_1961_p1` includes `0 < a` in the answer.
-/

/-- Auxiliary: with `x, y, z > 0`, `x + y + z = a`, `x^2 + y^2 + z^2 = b^2` and `x * y = z^2`,
we have `a^2 - b^2 = 2 * z * a`. -/
theorem imo_1961_p1_key (a b x y z : ℝ) (h1 : x + y + z = a) (h2 : x ^ 2 + y ^ 2 + z ^ 2 = b ^ 2)
    (h3 : x * y = z ^ 2) : a ^ 2 - b ^ 2 = 2 * z * a := by
  rw [← h1, ← h2]; linear_combination 2 * h3

/-- Forward direction of IMO 1961 Problem 1. -/
theorem imo_1961_p1_forward (a b : ℝ)
    (h : ∃ x > (0 : ℝ), ∃ y > (0 : ℝ), ∃ z > (0 : ℝ),
      x + y + z = a ∧ x ^ 2 + y ^ 2 + z ^ 2 = b ^ 2 ∧ x * y = z ^ 2 ∧ [x, y, z].Nodup) :
    0 < a ∧ b ^ 2 < a ^ 2 ∧ a ^ 2 < 3 * b ^ 2 := by
  obtain ⟨x, hx, y, hy, z, hz, h1, h2, h3, hnd⟩ := h
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
    List.nodup_nil, not_or] at hnd
  have hxy : x ≠ y := by
    intro hh; exact hnd.1.1 hh
  have ha : 0 < a := by rw [← h1]; linarith
  have key := imo_1961_p1_key a b x y z h1 h2 h3
  have hza : 0 < 2 * z * a := by positivity
  refine ⟨ha, by linarith, ?_⟩
  have hxy2 : 0 < (x - y) ^ 2 := by
    have : x - y ≠ 0 := sub_ne_zero.mpr hxy
    positivity
  -- `3 * b ^ 2 - a ^ 2 = 2 * (x ^ 2 + y ^ 2 - z * (x + y))`
  have hz2 : 2 * z < x + y := by nlinarith [sq_nonneg (x + y - 2 * z)]
  nlinarith [sq_nonneg (x - y), mul_pos hx hy]

/-- Reverse direction of IMO 1961 Problem 1. -/
theorem imo_1961_p1_reverse (a b : ℝ) (ha : 0 < a) (hb : b ^ 2 < a ^ 2) (hb3 : a ^ 2 < 3 * b ^ 2) :
    ∃ x > (0 : ℝ), ∃ y > (0 : ℝ), ∃ z > (0 : ℝ),
      x + y + z = a ∧ x ^ 2 + y ^ 2 + z ^ 2 = b ^ 2 ∧ x * y = z ^ 2 ∧ [x, y, z].Nodup := by
  have ha' : a ≠ 0 := ne_of_gt ha
  set z : ℝ := (a ^ 2 - b ^ 2) / (2 * a) with hzdef
  set s : ℝ := (a ^ 2 + b ^ 2) / (2 * a) with hsdef
  have hb2 : 0 < b ^ 2 := by nlinarith
  have hz : 0 < z := by
    apply div_pos (by linarith) (by linarith)
  have hs : 0 < s := by
    apply div_pos (by nlinarith) (by linarith)
  have hA : 0 < (3 * b ^ 2 - a ^ 2) * (3 * a ^ 2 - b ^ 2) := by nlinarith
  set t : ℝ := Real.sqrt ((3 * b ^ 2 - a ^ 2) * (3 * a ^ 2 - b ^ 2)) / (2 * a) with htdef
  have ht0 : 0 < t := by
    apply div_pos (Real.sqrt_pos.mpr hA) (by linarith)
  have htsq : t ^ 2 = ((3 * b ^ 2 - a ^ 2) * (3 * a ^ 2 - b ^ 2)) / (4 * a ^ 2) := by
    rw [htdef, div_pow, Real.sq_sqrt hA.le]
    ring
  have hst : s ^ 2 - t ^ 2 = 4 * z ^ 2 := by
    rw [htsq, hsdef, hzdef, div_pow, div_pow]
    field_simp
    ring
  have hts : t < s := by
    nlinarith
  refine ⟨(s + t) / 2, by positivity, (s - t) / 2, by linarith, z, hz, ?_, ?_, ?_, ?_⟩
  · rw [hsdef, hzdef]; field_simp; ring
  · have : ((s + t) / 2) ^ 2 + ((s - t) / 2) ^ 2 + z ^ 2 = (s ^ 2 + t ^ 2) / 2 + z ^ 2 := by ring
    rw [this]
    have h4 : t ^ 2 = s ^ 2 - 4 * z ^ 2 := by linarith
    rw [h4, hsdef, hzdef]
    field_simp
    ring
  · have : ((s + t) / 2) * ((s - t) / 2) = (s ^ 2 - t ^ 2) / 4 := by ring
    rw [this, hst]; ring
  · have hne1 : (s + t) / 2 ≠ (s - t) / 2 := by intro hh; nlinarith
    have hnz : (s + t) / 2 ≠ z := by
      intro hh
      have h1 : ((s + t) / 2) * ((s - t) / 2) = z ^ 2 := by
        have : ((s + t) / 2) * ((s - t) / 2) = (s ^ 2 - t ^ 2) / 4 := by ring
        rw [this, hst]; ring
      rw [hh] at h1
      have : (s - t) / 2 = z := by
        field_simp at h1
        nlinarith
      exact hne1 (by rw [hh, this])
    have hnz2 : (s - t) / 2 ≠ z := by
      intro hh
      have h1 : ((s + t) / 2) * ((s - t) / 2) = z ^ 2 := by
        have : ((s + t) / 2) * ((s - t) / 2) = (s ^ 2 - t ^ 2) / 4 := by ring
        rw [this, hst]; ring
      rw [hh] at h1
      have : (s + t) / 2 = z := by
        field_simp at h1
        nlinarith
      exact hne1 (by rw [hh, this])
    refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_, List.nodup_singleton z⟩⟩
    · simp [hne1, hnz]
    · simp [hnz2]

/-- **IMO 1961 Problem 1.** The system `x + y + z = a`, `x^2 + y^2 + z^2 = b^2`, `x * y = z^2`
has a solution in distinct positive reals `x, y, z` if and only if `0 < a` and
`b^2 < a^2 < 3 * b^2`.

(The condition `0 < a` was missing from the originally proposed statement; see
`imo_1961_p1_without_pos_false`.) -/
theorem imo_1961_p1 (a b : ℝ) :
    (∃ x > (0 : ℝ), ∃ y > (0 : ℝ), ∃ z > (0 : ℝ),
      x + y + z = a ∧
      x ^ 2 + y ^ 2 + z ^ 2 = b ^ 2 ∧
      x * y = z ^ 2 ∧
      [x, y, z].Nodup) ↔
    (0 < a ∧ b ^ 2 < a ^ 2 ∧ a ^ 2 < 3 * b ^ 2) := by
  constructor
  · exact imo_1961_p1_forward a b
  · rintro ⟨ha, hb, hb3⟩
    exact imo_1961_p1_reverse a b ha hb hb3

/-- The originally proposed version of the statement, which omits the condition `0 < a`,
is false: for `a = -2`, `b = Real.sqrt 2` the right-hand side holds while there are of course
no positive `x, y, z` summing to a negative number. -/
theorem imo_1961_p1_without_pos_false :
    ¬ ∀ a b : ℝ,
      (∃ x > (0 : ℝ), ∃ y > (0 : ℝ), ∃ z > (0 : ℝ),
        x + y + z = a ∧
        x ^ 2 + y ^ 2 + z ^ 2 = b ^ 2 ∧
        x * y = z ^ 2 ∧
        [x, y, z].Nodup) ↔
      (b ^ 2 < a ^ 2 ∧ a ^ 2 < 3 * b ^ 2) := by
  intro h
  have hsq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h2 := (h (-2) (Real.sqrt 2)).mpr (by rw [hsq]; norm_num)
  obtain ⟨x, hx, y, hy, z, hz, h1, -⟩ := h2
  linarith
