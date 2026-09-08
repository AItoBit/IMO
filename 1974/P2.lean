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
# IMO 1974, Problem 2

In the triangle `ABC`, prove that there is a point `D` on side `AB` such that `CD` is the
geometric mean of `AD` and `DB` if and only if `sin A * sin B ≤ sin (C / 2) ^ 2`.
-/

namespace IMO1974P2

open EuclideanGeometry Real
open scoped RealInnerProductSpace

/-- The plane in which the triangle lives. -/
abbrev Plane : Type := EuclideanSpace ℝ (Fin 2)

/-- Comparison with `√2 * c` in squared form. -/
lemma le_sqrt_two_mul_iff {x c : ℝ} (hx : 0 ≤ x) (hc : 0 ≤ c) :
    x ≤ Real.sqrt 2 * c ↔ x ^ 2 ≤ 2 * c ^ 2 := by
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  constructor
  · intro h
    nlinarith [mul_nonneg hs0 hc]
  · intro h
    nlinarith [mul_nonneg hs0 hc]

/-- The algebraic heart of the "existence of `D`" side: with `a, b, c` the side lengths of the
triangle and `k = ⟪C - A, B - A⟫`, the quadratic equation coming from `CD ^ 2 = AD * DB` has a
root in `[0, 1]` iff `a + b ≤ √2 * c`. -/
lemma exists_root_iff {a b c k : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 < c)
    (hk : 2 * k = b ^ 2 + c ^ 2 - a ^ 2) (h1 : a ≤ b + c) (h2 : b ≤ a + c) :
    (∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ 2 * c ^ 2 * t ^ 2 - (2 * k + c ^ 2) * t + b ^ 2 = 0) ↔
      a + b ≤ Real.sqrt 2 * c := by
  set s : ℝ := Real.sqrt 2 * c with hsdef
  have hs0 : 0 ≤ s := by
    have : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    exact mul_nonneg this hc.le
  have hs2 : s ^ 2 = 2 * c ^ 2 := by
    rw [hsdef, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  have hsc : c < s := by nlinarith
  have hspos : 0 < s := lt_trans hc hsc
  set X : ℝ := b ^ 2 + s ^ 2 - a ^ 2 with hXdef
  have hXe : 2 * k + c ^ 2 = X := by rw [hXdef, hs2]; linarith
  have hq : ∀ t : ℝ, 2 * c ^ 2 * t ^ 2 - (2 * k + c ^ 2) * t + b ^ 2
      = s ^ 2 * t ^ 2 - X * t + b ^ 2 := by
    intro t; rw [hXe, hs2]
  have hfact : X ^ 2 - 4 * b ^ 2 * s ^ 2
      = (((b - s) - a) * ((b - s) + a)) * (((b + s) - a) * ((b + s) + a)) := by
    rw [hXdef]; ring
  have hf1 : (b - s) - a < 0 := by linarith
  have hf3 : 0 < (b + s) - a := by linarith
  have hf4 : 0 < (b + s) + a := by linarith
  constructor
  · rintro ⟨t, ht0, ht1, hroot⟩
    rw [hq] at hroot
    have hsq : (2 * s ^ 2 * t - X) ^ 2 = X ^ 2 - 4 * b ^ 2 * s ^ 2 := by
      linear_combination (4 * s ^ 2) * hroot
    have hdisc : 0 ≤ X ^ 2 - 4 * b ^ 2 * s ^ 2 := hsq ▸ sq_nonneg _
    by_contra hcon
    push_neg at hcon
    have hf2 : 0 < (b - s) + a := by linarith
    have hneg : (((b - s) - a) * ((b - s) + a)) * (((b + s) - a) * ((b + s) + a)) < 0 :=
      mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hf1 hf2) (mul_pos hf3 hf4)
    rw [hfact] at hdisc
    linarith
  · intro hle
    have hf2 : (b - s) + a ≤ 0 := by linarith
    have hdisc : 0 ≤ X ^ 2 - 4 * b ^ 2 * s ^ 2 := by
      rw [hfact]
      exact mul_nonneg (by nlinarith) (mul_pos hf3 hf4).le
    set r : ℝ := Real.sqrt (X ^ 2 - 4 * b ^ 2 * s ^ 2) with hrdef
    have hr0 : 0 ≤ r := Real.sqrt_nonneg _
    have hr2 : r ^ 2 = X ^ 2 - 4 * b ^ 2 * s ^ 2 := Real.sq_sqrt hdisc
    have hXpos : 0 ≤ X := by
      have ha' : a ≤ s := by linarith
      have : a ^ 2 ≤ s ^ 2 := by nlinarith
      rw [hXdef]; nlinarith [sq_nonneg b]
    have hrX : r ≤ X := by nlinarith
    have hX2 : X ≤ 2 * s ^ 2 := by
      have hb' : b ≤ s - a := by linarith
      rw [hXdef]; nlinarith
    refine ⟨(X - r) / (2 * s ^ 2), ?_, ?_, ?_⟩
    · apply div_nonneg (by linarith)
      positivity
    · rw [div_le_one (by positivity)]
      linarith
    · rw [hq]
      field_simp
      nlinarith [hr2]

/-- The algebraic heart of the trigonometric side. -/
lemma trig_core {a b c cA cB cC : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hA : 2 * b * c * cA = b ^ 2 + c ^ 2 - a ^ 2)
    (hB : 2 * a * c * cB = a ^ 2 + c ^ 2 - b ^ 2)
    (hC : 2 * a * b * cC = a ^ 2 + b ^ 2 - c ^ 2)
    (hsin : 0 < 1 - cA ^ 2)
    (h1 : a ≤ b + c) (h2 : b ≤ a + c) (h3 : c ≤ a + b) :
    ((1 - cA ^ 2) * (1 - cB ^ 2) ≤ ((1 - cC) / 2) ^ 2) ↔ a + b ≤ Real.sqrt 2 * c := by
  set P : ℝ := (a + b) ^ 2 - c ^ 2 with hPdef
  set Q : ℝ := c ^ 2 - (a - b) ^ 2 with hQdef
  have hP : 0 ≤ P := by rw [hPdef]; nlinarith
  have hQ : 0 ≤ Q := by rw [hQdef]; nlinarith
  have e1 : (1 - cA ^ 2) * (4 * b ^ 2 * c ^ 2) = P * Q := by
    rw [hPdef, hQdef]; linear_combination (-(2 * b * c * cA + (b ^ 2 + c ^ 2 - a ^ 2))) * hA
  have e2 : (1 - cB ^ 2) * (4 * a ^ 2 * c ^ 2) = P * Q := by
    rw [hPdef, hQdef]; linear_combination (-(2 * a * c * cB + (a ^ 2 + c ^ 2 - b ^ 2))) * hB
  have e3 : ((1 - cC) / 2) * (4 * a * b) = Q := by
    rw [hQdef]; linear_combination -hC
  have hPQ : 0 < P * Q := by
    rw [← e1]; exact mul_pos hsin (by positivity)
  have hQpos : 0 < Q := by
    rcases hQ.lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h] at hPQ; simp at hPQ
  have hPpos : 0 < P := by
    rcases hP.lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h] at hPQ; simp at hPQ
  have f1 : 1 - cA ^ 2 = P * Q / (4 * b ^ 2 * c ^ 2) := by
    field_simp
    linarith [e1]
  have f2 : 1 - cB ^ 2 = P * Q / (4 * a ^ 2 * c ^ 2) := by
    field_simp
    linarith [e2]
  have f3 : (1 - cC) / 2 = Q / (4 * a * b) := by
    field_simp
    linarith [e3]
  have key : ((1 - cA ^ 2) * (1 - cB ^ 2) ≤ ((1 - cC) / 2) ^ 2) ↔ P ^ 2 ≤ (c ^ 2) ^ 2 := by
    rw [f1, f2, f3, div_mul_div_comm, div_pow,
      div_le_div_iff₀ (by positivity) (by positivity)]
    have hpos : 0 < 16 * a ^ 2 * b ^ 2 * Q ^ 2 := by positivity
    constructor <;> intro h <;> nlinarith [hpos]
  rw [key, le_sqrt_two_mul_iff (by positivity) hc.le]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- Existence of a point `D` on the side `AB` with `CD ^ 2 = AD * DB` is equivalent to
`BC + AC ≤ √2 * AB`. -/
lemma exists_point_iff {A B C : Plane} (hAB : A ≠ B) :
    (∃ D ∈ segment ℝ A B, dist C D ^ 2 = dist A D * dist D B) ↔
      dist B C + dist A C ≤ Real.sqrt 2 * dist A B := by
  have hc : 0 < dist A B := dist_pos.2 hAB
  set a : ℝ := dist B C with hadef
  set b : ℝ := dist A C with hbdef
  set c : ℝ := dist A B with hcdef
  set k : ℝ := ⟪C - A, B - A⟫ with hkdef
  have hbn : b = ‖C - A‖ := by rw [hbdef, dist_eq_norm, norm_sub_rev]
  have hcn : c = ‖B - A‖ := by rw [hcdef, dist_eq_norm, norm_sub_rev]
  have han : a = ‖(C - A) - (B - A)‖ := by
    rw [hadef, dist_comm, dist_eq_norm]
    congr 1
    abel
  have hk : 2 * k = b ^ 2 + c ^ 2 - a ^ 2 := by
    have hsq : a ^ 2 = b ^ 2 - 2 * k + c ^ 2 := by
      rw [han, hbn, hcn, hkdef]
      exact norm_sub_sq_real (C - A) (B - A)
    linarith
  have htri1 : a ≤ b + c := by
    have h := dist_triangle B A C
    rw [dist_comm B A] at h
    rw [hadef, hbdef, hcdef]
    linarith
  have htri2 : b ≤ a + c := by
    have h := dist_triangle A B C
    rw [hadef, hbdef, hcdef]
    linarith
  have hval : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ((dist C (A + t • (B - A)) ^ 2 = dist A (A + t • (B - A)) * dist (A + t • (B - A)) B) ↔
        2 * c ^ 2 * t ^ 2 - (2 * k + c ^ 2) * t + b ^ 2 = 0) := by
    intro t ht0 ht1
    have h1 : C - (A + t • (B - A)) = (C - A) - t • (B - A) := by abel
    have h2 : A - (A + t • (B - A)) = -(t • (B - A)) := by abel
    have h3 : (A + t • (B - A)) - B = -((1 - t) • (B - A)) := by
      rw [sub_smul, one_smul]; abel
    have e1 : dist C (A + t • (B - A)) ^ 2 = b ^ 2 - 2 * t * k + t ^ 2 * c ^ 2 := by
      rw [dist_eq_norm, h1, norm_sub_sq_real, real_inner_smul_right, norm_smul,
        ← hbn, ← hcn, ← hkdef, Real.norm_eq_abs, abs_of_nonneg ht0]
      ring
    have e2 : dist A (A + t • (B - A)) = t * c := by
      rw [dist_eq_norm, h2, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0, ← hcn]
    have e3 : dist (A + t • (B - A)) B = (1 - t) * c := by
      rw [dist_eq_norm, h3, norm_neg, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - t), ← hcn]
    rw [e1, e2, e3]
    constructor <;> intro h <;> nlinarith [h]
  rw [← exists_root_iff dist_nonneg dist_nonneg hc hk htri1 htri2]
  constructor
  · rintro ⟨D, hD, hEq⟩
    rw [segment_eq_image'] at hD
    obtain ⟨t, ht, rfl⟩ := hD
    exact ⟨t, ht.1, ht.2, (hval t ht.1 ht.2).1 hEq⟩
  · rintro ⟨t, ht0, ht1, ht⟩
    refine ⟨A + t • (B - A), ?_, (hval t ht0 ht1).2 ht⟩
    rw [segment_eq_image']
    exact ⟨t, ⟨ht0, ht1⟩, rfl⟩

/-- The trigonometric condition is equivalent to `BC + AC ≤ √2 * AB`. -/
lemma angle_condition_iff {A B C : Plane} (h : ¬ Collinear ℝ ({A, B, C} : Set Plane)) :
    (Real.sin (∠ B A C) * Real.sin (∠ A B C) ≤ Real.sin (∠ A C B / 2) ^ 2) ↔
      dist B C + dist A C ≤ Real.sqrt 2 * dist A B := by
  have hAB : A ≠ B := ne₁₂_of_not_collinear h
  have hAC : A ≠ C := ne₁₃_of_not_collinear h
  have hBC : B ≠ C := ne₂₃_of_not_collinear h
  have hncA : ¬ Collinear ℝ ({B, A, C} : Set Plane) := by rwa [Set.insert_comm]
  set a : ℝ := dist B C with hadef
  set b : ℝ := dist A C with hbdef
  set c : ℝ := dist A B with hcdef
  have ha : 0 < a := dist_pos.2 hBC
  have hb : 0 < b := dist_pos.2 hAC
  have hc : 0 < c := dist_pos.2 hAB
  set cA : ℝ := Real.cos (∠ B A C) with hcAdef
  set cB : ℝ := Real.cos (∠ A B C) with hcBdef
  set cC : ℝ := Real.cos (∠ A C B) with hcCdef
  have hA : 2 * b * c * cA = b ^ 2 + c ^ 2 - a ^ 2 := by
    have hl := EuclideanGeometry.law_cos B A C
    rw [dist_comm B A, dist_comm C A] at hl
    rw [hadef, hbdef, hcdef, hcAdef]
    linear_combination hl
  have hB : 2 * a * c * cB = a ^ 2 + c ^ 2 - b ^ 2 := by
    have hl := EuclideanGeometry.law_cos A B C
    rw [dist_comm C B] at hl
    rw [hadef, hbdef, hcdef, hcBdef]
    linear_combination hl
  have hC : 2 * a * b * cC = a ^ 2 + b ^ 2 - c ^ 2 := by
    have hl := EuclideanGeometry.law_cos A C B
    rw [hadef, hbdef, hcdef, hcCdef]
    linear_combination hl
  have hsA : Real.sin (∠ B A C) ^ 2 = 1 - cA ^ 2 := by
    have := Real.sin_sq_add_cos_sq (∠ B A C)
    rw [hcAdef]; linarith
  have hsB : Real.sin (∠ A B C) ^ 2 = 1 - cB ^ 2 := by
    have := Real.sin_sq_add_cos_sq (∠ A B C)
    rw [hcBdef]; linarith
  have hhalf : Real.sin (∠ A C B / 2) ^ 2 = (1 - cC) / 2 := by
    have h2 : (2 : ℝ) * (∠ A C B / 2) = ∠ A C B := by ring
    rw [Real.sin_sq_eq_half_sub, h2, hcCdef]; ring
  have hsinA : 0 < Real.sin (∠ B A C) := EuclideanGeometry.sin_pos_of_not_collinear hncA
  have hsinB : 0 < Real.sin (∠ A B C) := EuclideanGeometry.sin_pos_of_not_collinear h
  have hsin : 0 < 1 - cA ^ 2 := by
    rw [← hsA]; positivity
  have hCle : cC ≤ 1 := by rw [hcCdef]; exact Real.cos_le_one _
  have htri1 : a ≤ b + c := by
    have hd := dist_triangle B A C
    rw [dist_comm B A] at hd
    rw [hadef, hbdef, hcdef]; linarith
  have htri2 : b ≤ a + c := by
    have hd := dist_triangle A B C
    rw [hadef, hbdef, hcdef]; linarith
  have htri3 : c ≤ a + b := by
    have hd := dist_triangle A C B
    rw [dist_comm C B] at hd
    rw [hadef, hbdef, hcdef]; linarith
  have hkey : (Real.sin (∠ B A C) * Real.sin (∠ A B C) ≤ Real.sin (∠ A C B / 2) ^ 2) ↔
      ((1 - cA ^ 2) * (1 - cB ^ 2) ≤ ((1 - cC) / 2) ^ 2) := by
    rw [hhalf]
    rw [← pow_le_pow_iff_left₀ (by positivity) (by linarith) (two_ne_zero)]
    rw [mul_pow, hsA, hsB]
  rw [hkey]
  exact trig_core ha hb hc hA hB hC hsin htri1 htri2 htri3

/-- **IMO 1974, Problem 2.**  In a (nondegenerate) triangle `ABC` there is a point `D` on the
side `AB` such that `CD` is the geometric mean of `AD` and `DB` if and only if
`sin A * sin B ≤ sin (C / 2) ^ 2`. -/
theorem imo1974_p2 {A B C : Plane} (h : ¬ Collinear ℝ ({A, B, C} : Set Plane)) :
    (∃ D ∈ segment ℝ A B, dist C D ^ 2 = dist A D * dist D B) ↔
      Real.sin (∠ B A C) * Real.sin (∠ A B C) ≤ Real.sin (∠ A C B / 2) ^ 2 := by
  rw [exists_point_iff (ne₁₂_of_not_collinear h), angle_condition_iff h]

end IMO1974P2
