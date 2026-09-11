import Mathlib
import RequestProject.IncenterFormula

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

set_option grind.warning false

/-!
# IMO 1988, Problem 5

In a right-angled triangle `ABC` (with the right angle at `A`) let `AD` be the altitude drawn to
the hypotenuse `BC`, and let the straight line joining the incentres of the triangles `ABD`, `ACD`
intersect the sides `AB`, `AC` at the points `K`, `L` respectively.  If `E` and `E₁` denote the
areas of the triangles `ABC` and `AKL` respectively, then `E / E₁ ≥ 2`.

The proof shows that `AK = AL = AD`, which gives `E / E₁ = BC ^ 2 / (AB * AC) ≥ 2`.
-/

open EuclideanGeometry
open scoped RealInnerProductSpace

namespace Imo1988P5

/-- The plane. -/
abbrev Pt := EuclideanSpace ℝ (Fin 2)

/-- The area of the triangle with vertices `X`, `Y`, `Z`, computed as half the product of the
two sides at `X` with the sine of the angle at `X`. -/
noncomputable def area (X Y Z : Pt) : ℝ :=
  1 / 2 * dist X Y * dist X Z * Real.sin (∠ Y X Z)

/-- The area of a triangle with a right angle at `X` is half the product of the legs. -/
lemma area_of_right_angle {X Y Z : Pt} (h : ⟪Y - X, Z - X⟫ = 0) :
    area X Y Z = 1 / 2 * dist X Y * dist X Z := by
  have hang : ∠ Y X Z = Real.pi / 2 := by
    rw [EuclideanGeometry.angle, ← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two]
    simpa using h
  rw [area, hang, Real.sin_pi_div_two, mul_one]

/-- Two nonzero orthogonal vectors are linearly independent. -/
theorem coeff_eq_zero_of_orthogonal {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {u v : E} (huv : ⟪u, v⟫ = 0) (hu : u ≠ 0) (hv : v ≠ 0)
    {x y : ℝ} (h : x • u + y • v = 0) : x = 0 ∧ y = 0 := by
  have huv' : ⟪v, u⟫ = 0 := by rw [real_inner_comm]; exact huv
  constructor
  · have h1 := congrArg (fun w => ⟪u, w⟫) h
    simp [inner_add_right, real_inner_smul_right, huv] at h1
    rcases h1 with h1 | h1
    · exact h1
    · exact absurd h1 (by simpa using hu)
  · have h1 := congrArg (fun w => ⟪v, w⟫) h
    simp [inner_add_right, real_inner_smul_right, huv'] at h1
    rcases h1 with h1 | h1
    · exact h1
    · exact absurd h1 (by simpa using hv)

/-- The squared norm of a combination of two orthogonal vectors. -/
lemma norm_sq_smul_add_smul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {u v : E} (huv : ⟪u, v⟫ = 0) (x y : ℝ) :
    ‖x • u + y • v‖ ^ 2 = x ^ 2 * ‖u‖ ^ 2 + y ^ 2 * ‖v‖ ^ 2 := by
  rw [show ‖x • u + y • v‖ ^ 2 = ⟪x • u + y • v, x • u + y • v⟫ from
    (real_inner_self_eq_norm_sq _).symm]
  have huv' : ⟪v, u⟫ = 0 := by rw [real_inner_comm]; exact huv
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    huv, huv']
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  ring

/-- Three collinear points, written in coordinates with respect to two orthogonal vectors
`u`, `v` and a base point `A`, satisfy the vanishing of the usual `2 × 2` determinant. -/
theorem collinear_det {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {u v : E} (huv : ⟪u, v⟫ = 0) (hu : u ≠ 0) (hv : v ≠ 0)
    {A p1 p2 p3 : E} {x1 y1 x2 y2 x3 y3 : ℝ}
    (h1 : p1 - A = x1 • u + y1 • v) (h2 : p2 - A = x2 • u + y2 • v)
    (h3 : p3 - A = x3 • u + y3 • v) (hcol : Collinear ℝ ({p1, p2, p3} : Set E)) :
    (x2 - x1) * (y3 - y1) = (x3 - x1) * (y2 - y1) := by
  obtain ⟨d, hd⟩ := (collinear_iff_of_mem (Set.mem_insert p1 {p2, p3})).1 hcol
  obtain ⟨r2, hr2⟩ := hd p2 (by simp)
  obtain ⟨r3, hr3⟩ := hd p3 (by simp)
  have e2 : (x2 - x1) • u + (y2 - y1) • v = r2 • d := by
    have hp : p2 - p1 = r2 • d := by rw [hr2]; simp
    rw [← hp, show p2 - p1 = (p2 - A) - (p1 - A) by abel, h1, h2]
    module
  have e3 : (x3 - x1) • u + (y3 - y1) • v = r3 • d := by
    have hp : p3 - p1 = r3 • d := by rw [hr3]; simp
    rw [← hp, show p3 - p1 = (p3 - A) - (p1 - A) by abel, h1, h3]
    module
  have key : (r3 * (x2 - x1) - r2 * (x3 - x1)) • u + (r3 * (y2 - y1) - r2 * (y3 - y1)) • v = 0 := by
    have hz : r3 • ((x2 - x1) • u + (y2 - y1) • v) - r2 • ((x3 - x1) • u + (y3 - y1) • v) = 0 := by
      rw [e2, e3, smul_smul, smul_smul, mul_comm]
      abel
    rw [← hz]; module
  obtain ⟨k1, k2⟩ := coeff_eq_zero_of_orthogonal huv hu hv key
  rcases eq_or_ne r3 0 with hr | hr
  · subst hr
    have e3' : (x3 - x1) • u + (y3 - y1) • v = 0 := by rw [e3]; simp
    obtain ⟨m1, m2⟩ := coeff_eq_zero_of_orthogonal huv hu hv e3'
    have hx : x3 = x1 := by linarith
    have hy : y3 = y1 := by linarith
    rw [hx, hy]; ring
  · have hx : r3 * (x2 - x1) = r2 * (x3 - x1) := by linarith
    have hy : r3 * (y2 - y1) = r2 * (y3 - y1) := by linarith
    refine mul_left_cancel₀ hr ?_
    calc r3 * ((x2 - x1) * (y3 - y1)) = (r3 * (x2 - x1)) * (y3 - y1) := by ring
      _ = (r2 * (x3 - x1)) * (y3 - y1) := by rw [hx]
      _ = (x3 - x1) * (r2 * (y3 - y1)) := by ring
      _ = (x3 - x1) * (r3 * (y2 - y1)) := by rw [hy]
      _ = r3 * ((x3 - x1) * (y2 - y1)) := by ring

/-- **IMO 1988, Problem 5** (main computation).
`ABC` is a triangle with a right angle at `A`; `D` is the foot of the altitude from `A` to the
hypotenuse `BC`; `T₁` and `T₂` are the triangles `ABD` and `ACD`, and the line through their
incentres meets the side `AB` at `K` and the side `AC` at `L`.  Then `AK = AL = AD` and the
area of `ABC` is at least twice the area of `AKL`. -/
theorem imo1988_p5_aux (A B C D K L : Pt) (T₁ T₂ : Affine.Triangle ℝ Pt)
    (hT₁ : T₁.points = ![A, B, D]) (hT₂ : T₂.points = ![A, C, D])
    (hAB : A ≠ B) (hAC : A ≠ C) (hright : ⟪B - A, C - A⟫ = 0)
    (hD : D ∈ line[ℝ, B, C]) (hDperp : ⟪A - D, C - B⟫ = 0)
    (hK : K ∈ line[ℝ, A, B]) (hL : L ∈ line[ℝ, A, C])
    (hKcol : Collinear ℝ ({T₁.incenter, T₂.incenter, K} : Set Pt))
    (hLcol : Collinear ℝ ({T₁.incenter, T₂.incenter, L} : Set Pt)) :
    dist A K = dist A D ∧ dist A L = dist A D ∧ 2 ≤ area A B C / area A K L := by
  -- Set up coordinates: `u = B - A` and `v = C - A` are orthogonal, of lengths `c` and `b`.
  obtain ⟨u, hu_def⟩ : ∃ w : Pt, B - A = w := ⟨_, rfl⟩
  obtain ⟨v, hv_def⟩ : ∃ w : Pt, C - A = w := ⟨_, rfl⟩
  have huv : ⟪u, v⟫ = 0 := by rw [← hu_def, ← hv_def]; exact hright
  have huv' : ⟪v, u⟫ = 0 := by rw [real_inner_comm]; exact huv
  have hu : u ≠ 0 := by rw [← hu_def]; exact sub_ne_zero.2 (Ne.symm hAB)
  have hv : v ≠ 0 := by rw [← hv_def]; exact sub_ne_zero.2 (Ne.symm hAC)
  obtain ⟨c, hc_def⟩ : ∃ r : ℝ, ‖u‖ = r := ⟨_, rfl⟩
  obtain ⟨b, hb_def⟩ : ∃ r : ℝ, ‖v‖ = r := ⟨_, rfl⟩
  obtain ⟨a, ha_def⟩ : ∃ r : ℝ, ‖v - u‖ = r := ⟨_, rfl⟩
  have hcpos : 0 < c := by rw [← hc_def]; exact norm_pos_iff.2 hu
  have hbpos : 0 < b := by rw [← hb_def]; exact norm_pos_iff.2 hv
  have hanneg : 0 ≤ a := by rw [← ha_def]; exact norm_nonneg _
  have hvu : C - B = v - u := by rw [← hu_def, ← hv_def]; abel
  have ha2 : a ^ 2 = b ^ 2 + c ^ 2 := by
    have h := norm_sub_sq_real v u
    rw [ha_def, hb_def, hc_def, huv'] at h
    linarith
  have hapos : 0 < a := by nlinarith
  have ha' : a ≠ 0 := ne_of_gt hapos
  have hb' : b ≠ 0 := ne_of_gt hbpos
  have hc' : c ≠ 0 := ne_of_gt hcpos
  have hs' : a + b + c ≠ 0 := by positivity
  have hsq : ∀ (P Q : Pt) (r : ℝ), 0 ≤ r → dist P Q ^ 2 = r ^ 2 → dist P Q = r := by
    intro P Q r hr h
    rw [← Real.sqrt_sq dist_nonneg, h, Real.sqrt_sq hr]
  have hnorm : ∀ x y : ℝ, ‖x • u + y • v‖ ^ 2 = x ^ 2 * c ^ 2 + y ^ 2 * b ^ 2 := by
    intro x y
    rw [norm_sq_smul_add_smul huv, hc_def, hb_def]
  -- The foot of the altitude.
  obtain ⟨t, ht⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.1 hD
  have hDA : D - A = u + t • (v - u) := by
    rw [← ht, AffineMap.lineMap_apply]
    simp only [vsub_eq_sub, vadd_eq_add, hvu]
    rw [show t • (v - u) + B - A = t • (v - u) + (B - A) by abel, hu_def]
    abel
  have h0 : ⟪D - A, v - u⟫ = 0 := by
    rw [← hvu, show D - A = -(A - D) by abel, inner_neg_left, hDperp, neg_zero]
  have e1 : ⟪u, v - u⟫ = -c ^ 2 := by
    rw [inner_sub_right, huv, real_inner_self_eq_norm_sq, hc_def]; ring
  have e2 : ⟪v - u, v - u⟫ = a ^ 2 := by rw [real_inner_self_eq_norm_sq, ha_def]
  rw [hDA, inner_add_left, real_inner_smul_left, e1, e2] at h0
  have ht' : t = c ^ 2 / a ^ 2 := by field_simp; linarith
  have hDA' : D - A = (b ^ 2 / a ^ 2) • u + (c ^ 2 / a ^ 2) • v := by
    rw [hDA, ht']
    have hcoef : (1 : ℝ) - c ^ 2 / a ^ 2 = b ^ 2 / a ^ 2 := by field_simp; linarith
    rw [show u + (c ^ 2 / a ^ 2) • (v - u)
        = (1 - c ^ 2 / a ^ 2) • u + (c ^ 2 / a ^ 2) • v by module, hcoef]
  -- The side lengths of the two small triangles.
  have hdAB : dist A B = c := by
    rw [dist_eq_norm, show A - B = -(B - A) by abel, norm_neg, hu_def, hc_def]
  have hdAC : dist A C = b := by
    rw [dist_eq_norm, show A - C = -(C - A) by abel, norm_neg, hv_def, hb_def]
  have hdAD : dist A D = b * c / a := by
    refine hsq _ _ _ (by positivity) ?_
    rw [dist_eq_norm, show A - D = -(D - A) by abel, norm_neg, hDA', hnorm]
    field_simp
    nlinarith [ha2]
  have hdBD : dist B D = c ^ 2 / a := by
    refine hsq _ _ _ (by positivity) ?_
    rw [dist_eq_norm, show B - D = -((D - A) - (B - A)) by abel, norm_neg, hDA', hu_def,
      show (b ^ 2 / a ^ 2) • u + (c ^ 2 / a ^ 2) • v - u
        = (b ^ 2 / a ^ 2 - 1) • u + (c ^ 2 / a ^ 2) • v by module, hnorm]
    have hco : b ^ 2 / a ^ 2 - 1 = -(c ^ 2 / a ^ 2) := by field_simp; linarith
    rw [hco]
    field_simp
    nlinarith [ha2]
  have hdCD : dist C D = b ^ 2 / a := by
    refine hsq _ _ _ (by positivity) ?_
    rw [dist_eq_norm, show C - D = -((D - A) - (C - A)) by abel, norm_neg, hDA', hv_def,
      show (b ^ 2 / a ^ 2) • u + (c ^ 2 / a ^ 2) • v - v
        = (b ^ 2 / a ^ 2) • u + (c ^ 2 / a ^ 2 - 1) • v by module, hnorm]
    have hco : c ^ 2 / a ^ 2 - 1 = -(b ^ 2 / a ^ 2) := by field_simp; linarith
    rw [hco]
    field_simp
    nlinarith [ha2]
  -- The two incentres, in coordinates.
  have hI1 : T₁.incenter - A = ((a * b + b ^ 2) / (a * (a + b + c))) • u
      + (c ^ 2 / (a * (a + b + c))) • v := by
    have h := IncenterFormula.incenter_vsub_of_points_eq T₁ hT₁
    simp only [vsub_eq_sub] at h
    rw [hdAB, hdAD, hdBD, hDA', hu_def] at h
    rw [show c ^ 2 / a + b * c / a + c = c * (a + b + c) / a by field_simp; ring] at h
    rw [h]
    match_scalars <;> field_simp
  have hI2 : T₂.incenter - A = (b ^ 2 / (a * (a + b + c))) • u
      + ((a * c + c ^ 2) / (a * (a + b + c))) • v := by
    have h := IncenterFormula.incenter_vsub_of_points_eq T₂ hT₂
    simp only [vsub_eq_sub] at h
    rw [hdAC, hdAD, hdCD, hDA', hv_def] at h
    rw [show b ^ 2 / a + b * c / a + b = b * (a + b + c) / a by field_simp; ring] at h
    rw [h]
    match_scalars <;> field_simp
  -- The point `K` on the side `AB`.
  obtain ⟨k, hk⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.1 hK
  have hKA : K - A = k • u + (0 : ℝ) • v := by
    rw [← hk, AffineMap.lineMap_apply]
    simp only [vsub_eq_sub, vadd_eq_add, hu_def, zero_smul, add_zero]
    abel
  have hkval : k = b / a := by
    have hdet := collinear_det huv hu hv hI1 hI2 hKA hKcol
    field_simp at hdet
    rw [eq_div_iff ha']
    have key : (a * c * (a + b + c)) * (k * a) = (a * c * (a + b + c)) * b := by
      linear_combination -hdet
    exact mul_left_cancel₀ (by positivity) key
  -- The point `L` on the side `AC`.
  obtain ⟨l, hl⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.1 hL
  have hLA : L - A = (0 : ℝ) • u + l • v := by
    rw [← hl, AffineMap.lineMap_apply]
    simp only [vsub_eq_sub, vadd_eq_add, hv_def, zero_smul, zero_add]
    abel
  have hlval : l = c / a := by
    have hdet := collinear_det huv hu hv hI1 hI2 hLA hLcol
    field_simp at hdet
    rw [eq_div_iff ha']
    have key : (a * b * (a + b + c)) * (l * a) = (a * b * (a + b + c)) * c := by
      linear_combination -hdet
    exact mul_left_cancel₀ (by positivity) key
  -- The two areas.
  have hKA' : K - A = (b / a) • u := by rw [hKA, hkval]; module
  have hLA' : L - A = (c / a) • v := by rw [hLA, hlval]; module
  have hdAK : dist A K = b * c / a := by
    rw [dist_eq_norm, show A - K = -(K - A) by abel, norm_neg, hKA', norm_smul,
      Real.norm_eq_abs, abs_of_pos (by positivity), hc_def]
    ring
  have hdAL : dist A L = b * c / a := by
    rw [dist_eq_norm, show A - L = -(L - A) by abel, norm_neg, hLA', norm_smul,
      Real.norm_eq_abs, abs_of_pos (by positivity), hb_def]
    ring
  have hperpKL : ⟪K - A, L - A⟫ = 0 := by
    rw [hKA', hLA', real_inner_smul_left, real_inner_smul_right, huv]
    ring
  have harea : area A B C = 1 / 2 * c * b := by
    rw [area_of_right_angle hright, hdAB, hdAC]
  have harea1 : area A K L = 1 / 2 * (b * c / a) * (b * c / a) := by
    rw [area_of_right_angle hperpKL, hdAK, hdAL]
  refine ⟨by rw [hdAK, hdAD], by rw [hdAL, hdAD], ?_⟩
  rw [harea, harea1, le_div_iff₀ (by positivity),
    show 2 * (1 / 2 * (b * c / a) * (b * c / a)) = (b * c) ^ 2 / a ^ 2 by field_simp,
    div_le_iff₀ (by positivity : (0:ℝ) < a ^ 2)]
  nlinarith [mul_nonneg (mul_pos hbpos hcpos).le (sq_nonneg (b - c)), ha2]

/-- **IMO 1988, Problem 5.**
In a right-angled triangle `ABC` (with the right angle at `A`), let `AD` be the altitude drawn to
the hypotenuse, and let the straight line joining the incentres of the triangles `ABD`, `ACD`
intersect the sides `AB`, `AC` at the points `K`, `L` respectively.  If `E` and `E₁` denote the
areas of the triangles `ABC` and `AKL` respectively, then `E / E₁ ≥ 2`. -/
theorem imo1988_p5 (A B C D K L : Pt) (T₁ T₂ : Affine.Triangle ℝ Pt)
    (hT₁ : T₁.points = ![A, B, D]) (hT₂ : T₂.points = ![A, C, D])
    (hAB : A ≠ B) (hAC : A ≠ C) (hright : ⟪B - A, C - A⟫ = 0)
    (hD : D ∈ line[ℝ, B, C]) (hDperp : ⟪A - D, C - B⟫ = 0)
    (hK : K ∈ line[ℝ, A, B]) (hL : L ∈ line[ℝ, A, C])
    (hKcol : Collinear ℝ ({T₁.incenter, T₂.incenter, K} : Set Pt))
    (hLcol : Collinear ℝ ({T₁.incenter, T₂.incenter, L} : Set Pt)) :
    2 ≤ area A B C / area A K L :=
  (imo1988_p5_aux A B C D K L T₁ T₂ hT₁ hT₂ hAB hAC hright hD hDperp hK hL hKcol hLcol).2.2

/-- In the configuration of IMO 1988, Problem 5, the line through the two incentres cuts off
the segments `AK = AL = AD` on the legs of the right angle. -/
theorem dist_eq_dist_altitude (A B C D K L : Pt) (T₁ T₂ : Affine.Triangle ℝ Pt)
    (hT₁ : T₁.points = ![A, B, D]) (hT₂ : T₂.points = ![A, C, D])
    (hAB : A ≠ B) (hAC : A ≠ C) (hright : ⟪B - A, C - A⟫ = 0)
    (hD : D ∈ line[ℝ, B, C]) (hDperp : ⟪A - D, C - B⟫ = 0)
    (hK : K ∈ line[ℝ, A, B]) (hL : L ∈ line[ℝ, A, C])
    (hKcol : Collinear ℝ ({T₁.incenter, T₂.incenter, K} : Set Pt))
    (hLcol : Collinear ℝ ({T₁.incenter, T₂.incenter, L} : Set Pt)) :
    dist A K = dist A D ∧ dist A L = dist A D :=
  ⟨(imo1988_p5_aux A B C D K L T₁ T₂ hT₁ hT₂ hAB hAC hright hD hDperp hK hL hKcol hLcol).1,
    (imo1988_p5_aux A B C D K L T₁ T₂ hT₁ hT₂ hAB hAC hright hD hDperp hK hL hKcol hLcol).2.1⟩

end Imo1988P5
