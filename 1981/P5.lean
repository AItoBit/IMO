import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open RealInnerProductSpace

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# IMO 1981, Problem 5

*Three congruent circles have a common point `O` and lie inside a given triangle.  Each circle
touches a pair of sides of the triangle.  Prove that the incenter and the circumcenter of the
triangle and the point `O` are collinear.*

The configuration is formalised in the Euclidean plane `EuclideanSpace ℝ (Fin 2)`:

* the triangle is given by three non-collinear points `A`, `B`, `C`;
* the three circles have a common radius `r` and centres `OA`, `OB`, `OC`, each of which lies
  inside the triangle (i.e. in the convex hull of `{A, B, C}`);
* the circle with centre `OA` is tangent to the lines `AB` and `AC`, the circle with centre `OB`
  is tangent to `AB` and `BC`, and the circle with centre `OC` is tangent to `AC` and `BC`;
* `O` lies on all three circles;
* `X` is a circumcenter of the triangle, i.e. a point equidistant from `A`, `B` and `C`.

One nondegeneracy assumption has to be added: the three circles must not all coincide.  (If the
common radius equals the inradius, then all three circles are the incircle, every point `O` of
the incircle satisfies the hypotheses, and the conclusion fails.)  We express this as
`OA ≠ OB`.

The conclusion is that the incenter, the circumcenter `X` and `O` are collinear.
-/

namespace IMO1981P5

/-- Points of the Euclidean plane. -/
abbrev Pt := EuclideanSpace ℝ (Fin 2)

/-! ### Elementary inner-product computations -/

theorem norm_lin_comb_sq (a b : ℝ) (u v : Pt) :
    ‖a • u + b • v‖ ^ 2 = a ^ 2 * ‖u‖ ^ 2 + 2 * a * b * ⟪u, v⟫ + b ^ 2 * ‖v‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq, real_inner_comm v u, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

theorem inner_lin_comb (a b : ℝ) (u v : Pt) :
    ⟪a • u + b • v, u⟫ = a * ‖u‖ ^ 2 + b * ⟪u, v⟫ := by
  simp only [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
    real_inner_comm v u]

theorem inner_coord (x y : Pt) : ⟪x, y⟫ = x 0 * y 0 + x 1 * y 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]; ring

theorem normsq_coord (x : Pt) : ‖x‖ ^ 2 = x 0 * x 0 + x 1 * x 1 := by
  rw [← real_inner_self_eq_norm_sq, inner_coord]

/-- In the plane, a vector orthogonal to two linearly independent vectors vanishes. -/
theorem eq_zero_of_orthogonal_two (w u v : Pt) (h1 : ⟪w, u⟫ = 0) (h2 : ⟪w, v⟫ = 0)
    (hd : 0 < ‖u‖ ^ 2 * ‖v‖ ^ 2 - ⟪u, v⟫ ^ 2) : w = 0 := by
  rw [inner_coord] at h1 h2
  rw [normsq_coord, normsq_coord, inner_coord] at hd
  have hdet : u 0 * v 1 - u 1 * v 0 ≠ 0 := by
    intro h
    rw [show (u 0 * u 0 + u 1 * u 1) * (v 0 * v 0 + v 1 * v 1) - (u 0 * v 0 + u 1 * v 1) ^ 2
      = (u 0 * v 1 - u 1 * v 0) ^ 2 by ring, h] at hd
    simp at hd
  have e0 : w 0 * (u 0 * v 1 - u 1 * v 0) = 0 := by linear_combination v 1 * h1 - u 1 * h2
  have e1 : w 1 * (u 0 * v 1 - u 1 * v 0) = 0 := by linear_combination u 0 * h2 - v 0 * h1
  have f0 := (mul_eq_zero.1 e0).resolve_right hdet
  have f1 := (mul_eq_zero.1 e1).resolve_right hdet
  ext i; fin_cases i <;> simpa

/-- Two points that are both equidistant from `P` and from `Q` differ by a vector orthogonal
to `Q - P`. -/
theorem inner_eq_zero_of_dist_eq (P Q Z W : Pt) (h1 : dist Z P = dist Z Q)
    (h2 : dist W P = dist W Q) : ⟪Z - W, Q - P⟫ = 0 := by
  have e : ∀ Y : Pt, dist Y P = dist Y Q → 2 * ⟪Y, Q⟫ - 2 * ⟪Y, P⟫ = ‖Q‖ ^ 2 - ‖P‖ ^ 2 := by
    intro Y hY
    have : ‖Y - P‖ ^ 2 = ‖Y - Q‖ ^ 2 := by rw [← dist_eq_norm, ← dist_eq_norm, hY]
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq] at this
    simp only [inner_sub_left, inner_sub_right, real_inner_self_eq_norm_sq] at this
    rw [real_inner_comm Y P, real_inner_comm Y Q] at this
    linarith
  have hZ := e Z h1
  have hW := e W h2
  simp only [inner_sub_left, inner_sub_right]
  linarith

/-! ### The Gram determinant of a triangle -/

/-- Twice the area of the triangle `A B C`, squared:
`gram A B C = ‖B - A‖² ‖C - A‖² - ⟪B - A, C - A⟫²`. -/
noncomputable def gram (A B C : Pt) : ℝ :=
  ‖B - A‖ ^ 2 * ‖C - A‖ ^ 2 - ⟪B - A, C - A⟫ ^ 2

theorem gram_nonneg (A B C : Pt) : 0 ≤ gram A B C := by
  have h1 := abs_real_inner_le_norm (B - A) (C - A)
  have h2 := sq_abs (⟪B - A, C - A⟫)
  simp only [gram]
  nlinarith [abs_nonneg (⟪B - A, C - A⟫), norm_nonneg (B - A), norm_nonneg (C - A)]

theorem gram_swap (A B C : Pt) : gram A C B = gram A B C := by
  simp only [gram, real_inner_comm (C - A) (B - A)]; ring

theorem gram_cycl (A B C : Pt) : gram B C A = gram A B C := by
  simp only [gram, ← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, real_inner_comm]
  ring

theorem collinear_of_gram_eq_zero (A B C : Pt) (h : gram A B C = 0) :
    Collinear ℝ ({A, B, C} : Set Pt) := by
  set u := B - A with hu
  set v := C - A with hv
  by_cases hu0 : u = 0
  · have hB : B = A := by rw [← sub_eq_zero]; exact hu0
    subst hB
    exact (collinear_pair ℝ B C).subset (by intro x hx; simp at hx ⊢; tauto)
  · have hnu : ‖u‖ ≠ 0 := by simpa using hu0
    have key : ‖(‖u‖ ^ 2) • v + (-⟪u, v⟫) • u‖ ^ 2 = 0 := by
      rw [norm_lin_comb_sq, real_inner_comm u v]
      simp only [gram, ← hu, ← hv] at h
      nlinarith [h]
    have key2 : (‖u‖ ^ 2) • v = ⟪u, v⟫ • u := by
      have h0 : ‖(‖u‖ ^ 2) • v + (-⟪u, v⟫) • u‖ = 0 := by
        nlinarith [norm_nonneg ((‖u‖ ^ 2) • v + (-⟪u, v⟫) • u)]
      have h3 : (‖u‖ ^ 2) • v - ⟪u, v⟫ • u = 0 := by
        rw [← norm_eq_zero.1 h0]; module
      exact sub_eq_zero.1 h3
    have hvk : v = (⟪u, v⟫ / ‖u‖ ^ 2) • u := by
      have hne : (‖u‖ ^ 2 : ℝ) ≠ 0 := pow_ne_zero 2 hnu
      rw [div_eq_inv_mul, mul_smul, ← key2, smul_smul, inv_mul_cancel₀ hne, one_smul]
    rw [collinear_iff_of_mem (Set.mem_insert A {B, C})]
    refine ⟨u, ?_⟩
    rintro p (rfl | rfl | rfl)
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp [hu]⟩
    · exact ⟨⟪u, v⟫ / ‖u‖ ^ 2, by rw [← hvk, hv]; simp⟩

theorem gram_pos (A B C : Pt) (h : ¬ Collinear ℝ ({A, B, C} : Set Pt)) : 0 < gram A B C := by
  rcases (gram_nonneg A B C).lt_or_eq with h' | h'
  · exact h'
  · exact absurd (collinear_of_gram_eq_zero A B C h'.symm) h

/-! ### Tangency -/

/-- The circle with centre `P` and radius `r` is tangent to the line `AB`: the foot of the
perpendicular dropped from `P` to the line `AB` is at distance `r` from `P`. -/
def TangentToLine (P : Pt) (r : ℝ) (A B : Pt) : Prop :=
  ∃ s : ℝ, dist P (A + s • (B - A)) = r ∧ ⟪P - (A + s • (B - A)), B - A⟫ = 0

theorem tangentToLine_symm (P : Pt) (r : ℝ) (A B : Pt) (h : TangentToLine P r A B) :
    TangentToLine P r B A := by
  obtain ⟨s, hd, hperp⟩ := h
  refine ⟨1 - s, ?_, ?_⟩
  · rw [show B + (1 - s) • (A - B) = A + s • (B - A) by module]; exact hd
  · rw [show B + (1 - s) • (A - B) = A + s • (B - A) by module,
      show A - B = -(B - A) by module, inner_neg_right, hperp, neg_zero]

/-- If the circle with centre `P = A + β (B - A) + γ (C - A)` and radius `r` is tangent to the
line `AB`, then `r ‖B - A‖ = |γ| √(gram A B C)`; i.e. the distance from `P` to the line `AB` is
`|γ|` times the distance from `C` to that line. -/
theorem tangent_coeff (A B C P : Pt) (β γ r : ℝ) (hP : P = A + β • (B - A) + γ • (C - A))
    (h : TangentToLine P r A B) :
    r * ‖B - A‖ = |γ| * Real.sqrt (gram A B C) := by
  obtain ⟨s, hd, hperp⟩ := h
  set u := B - A with hu
  set v := C - A with hv
  have hPX : P - (A + s • u) = (β - s) • u + γ • v := by rw [hP]; module
  rw [hPX, inner_lin_comb] at hperp
  rw [dist_eq_norm, hPX] at hd
  have hr : r ^ 2 = (β - s) ^ 2 * ‖u‖ ^ 2 + 2 * (β - s) * γ * ⟪u, v⟫ + γ ^ 2 * ‖v‖ ^ 2 := by
    rw [← hd, norm_lin_comb_sq]
  have key : r ^ 2 * ‖u‖ ^ 2 = γ ^ 2 * gram A B C := by
    simp only [gram, ← hu, ← hv]
    nlinarith [hperp, hr]
  have hrn : 0 ≤ r := by rw [← hd]; positivity
  have hsq : r * ‖u‖ = Real.sqrt (r ^ 2 * ‖u‖ ^ 2) := by
    rw [show r ^ 2 * ‖u‖ ^ 2 = (r * ‖u‖) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  rw [hsq, key, Real.sqrt_mul (sq_nonneg γ), Real.sqrt_sq_eq_abs]

/-- Tangency to the line `AB` pins down the barycentric coordinate of `P` opposite to `AB`. -/
theorem coeff_AB (A B C P : Pt) (α β γ r : ℝ) (hsum : α + β + γ = 1) (hγ : 0 ≤ γ)
    (hP : P = α • A + β • B + γ • C) (h : TangentToLine P r A B) :
    r * ‖B - A‖ = γ * Real.sqrt (gram A B C) := by
  have hα : α = 1 - β - γ := by linarith
  subst hα
  rw [tangent_coeff A B C P β γ r (by rw [hP]; module) h, abs_of_nonneg hγ]

/-- Tangency to the line `AC` pins down the barycentric coordinate of `P` opposite to `AC`. -/
theorem coeff_AC (A B C P : Pt) (α β γ r : ℝ) (hsum : α + β + γ = 1) (hβ : 0 ≤ β)
    (hP : P = α • A + β • B + γ • C) (h : TangentToLine P r A C) :
    r * ‖C - A‖ = β * Real.sqrt (gram A B C) := by
  have hα : α = 1 - β - γ := by linarith
  subst hα
  rw [tangent_coeff A C B P γ β r (by rw [hP]; module) h, abs_of_nonneg hβ, gram_swap]

/-- Tangency to the line `BC` pins down the barycentric coordinate of `P` opposite to `BC`. -/
theorem coeff_BC (A B C P : Pt) (α β γ r : ℝ) (hsum : α + β + γ = 1) (hα' : 0 ≤ α)
    (hP : P = α • A + β • B + γ • C) (h : TangentToLine P r B C) :
    r * ‖C - B‖ = α * Real.sqrt (gram A B C) := by
  have hβ : β = 1 - α - γ := by linarith
  subst hβ
  rw [tangent_coeff B C A P γ α r (by rw [hP]; module) h, abs_of_nonneg hα', gram_cycl]

/-! ### Barycentric coordinates -/

theorem exists_barycentric (A B C P : Pt) (h : P ∈ convexHull ℝ ({A, B, C} : Set Pt)) :
    ∃ α β γ : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧ α + β + γ = 1 ∧ P = α • A + β • B + γ • C := by
  rw [show ({A, B, C} : Set Pt) = insert A {B, C} from rfl, convexHull_insert (by simp),
    convexHull_pair, mem_convexJoin] at h
  obtain ⟨x, hx, z, hz, hP⟩ := h
  simp only [Set.mem_singleton_iff] at hx
  subst hx
  rw [segment_eq_image] at hz hP
  obtain ⟨b, hb, rfl⟩ := hz
  obtain ⟨a, ha, rfl⟩ := hP
  exact ⟨1 - a, a * (1 - b), a * b, by linarith [ha.1, ha.2], by nlinarith [ha.1, hb.1, hb.2],
    by nlinarith [ha.1, hb.1], by ring, by module⟩

/-! ### The incenter -/

/-- The incenter of the triangle `A B C`, given by its barycentric coordinates
`(a : b : c)` where `a = |BC|`, `b = |CA|`, `c = |AB|`. -/
noncomputable def incenter (A B C : Pt) : Pt :=
  (dist B C / (dist B C + dist C A + dist A B)) • A +
  (dist C A / (dist B C + dist C A + dist A B)) • B +
  (dist A B / (dist B C + dist C A + dist A B)) • C

/-! ### The main theorem -/

/-- **IMO 1981, Problem 5.**  Three congruent circles with common radius `r` and centres
`OA`, `OB`, `OC` lie inside the triangle `A B C`; the one centred at `OA` touches the sides
`AB` and `AC`, the one centred at `OB` touches `AB` and `BC`, and the one centred at `OC`
touches `AC` and `BC`.  If they all pass through a point `O` (and they are not all the same
circle), then the incenter, the circumcenter `X` and `O` are collinear. -/
theorem imo1981_p5 (A B C OA OB OC O X : Pt) (r : ℝ)
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set Pt))
    (hOAmem : OA ∈ convexHull ℝ ({A, B, C} : Set Pt))
    (hOBmem : OB ∈ convexHull ℝ ({A, B, C} : Set Pt))
    (hOCmem : OC ∈ convexHull ℝ ({A, B, C} : Set Pt))
    (hOA1 : TangentToLine OA r A B) (hOA2 : TangentToLine OA r A C)
    (hOB1 : TangentToLine OB r A B) (hOB2 : TangentToLine OB r B C)
    (hOC1 : TangentToLine OC r A C) (hOC2 : TangentToLine OC r B C)
    (hne : OA ≠ OB)
    (hOOA : dist O OA = r) (hOOB : dist O OB = r) (hOOC : dist O OC = r)
    (hXB : dist X A = dist X B) (hXC : dist X A = dist X C) :
    Collinear ℝ ({incenter A B C, X, O} : Set Pt) := by
  -- notation for the side lengths, twice the area, and the perimeter
  set na := ‖C - B‖ with hna
  set nb := ‖C - A‖ with hnb
  set nc := ‖B - A‖ with hnc
  set D := Real.sqrt (gram A B C) with hD
  have hDpos : 0 < D := Real.sqrt_pos.2 (gram_pos A B C hABC)
  have hAB : B - A ≠ 0 := by
    intro h
    refine hABC ?_
    have hBA : B = A := by rw [← sub_eq_zero]; exact h
    subst hBA
    exact (collinear_pair ℝ B C).subset (by intro x hx; simp at hx ⊢; tauto)
  have hncpos : 0 < nc := by rw [hnc, norm_pos_iff]; exact hAB
  have hsp : 0 < na + nb + nc := by
    have h1 : 0 ≤ na := norm_nonneg _
    have h2 : 0 ≤ nb := norm_nonneg _
    linarith
  -- barycentric coordinates of the three centres
  obtain ⟨a1, b1, c1, ha1, hb1, hc1, hs1, hOA⟩ := exists_barycentric A B C OA hOAmem
  obtain ⟨a2, b2, c2, ha2, hb2, hc2, hs2, hOB⟩ := exists_barycentric A B C OB hOBmem
  obtain ⟨a3, b3, c3, ha3, hb3, hc3, hs3, hOC⟩ := exists_barycentric A B C OC hOCmem
  have e1 : r * nc = c1 * D := coeff_AB A B C OA a1 b1 c1 r hs1 hc1 hOA hOA1
  have e2 : r * nb = b1 * D := coeff_AC A B C OA a1 b1 c1 r hs1 hb1 hOA hOA2
  have e3 : r * nc = c2 * D := coeff_AB A B C OB a2 b2 c2 r hs2 hc2 hOB hOB1
  have e4 : r * na = a2 * D := coeff_BC A B C OB a2 b2 c2 r hs2 ha2 hOB hOB2
  have e5 : r * nb = b3 * D := coeff_AC A B C OC a3 b3 c3 r hs3 hb3 hOC hOC1
  have e6 : r * na = a3 * D := coeff_BC A B C OC a3 b3 c3 r hs3 ha3 hOC hOC2
  have hDne : D ≠ 0 := ne_of_gt hDpos
  have hsne : na + nb + nc ≠ 0 := ne_of_gt hsp
  -- the common ratio of the homothety
  set t : ℝ := r * (na + nb + nc) / D with ht
  -- the incenter, written in barycentric coordinates
  set I : Pt := (na / (na + nb + nc)) • A + (nb / (na + nb + nc)) • B +
    (nc / (na + nb + nc)) • C with hI
  have hIeq : incenter A B C = I := by
    rw [hI, incenter, dist_eq_norm, dist_eq_norm, dist_eq_norm, norm_sub_rev B C,
      norm_sub_rev A B, ← hna, ← hnb, ← hnc]
  -- the homothety with centre `I` and ratio `1 - t` maps the vertices to the centres
  have hOAeq : OA = (1 - t) • A + t • I := by
    rw [hOA, hI, ht]
    have hb1' : b1 = r * nb / D := by field_simp; linarith
    have hc1' : c1 = r * nc / D := by field_simp; linarith
    have ha1' : a1 = 1 - r * nb / D - r * nc / D := by rw [← hb1', ← hc1']; linarith
    rw [ha1', hb1', hc1']
    match_scalars <;> (field_simp; try ring)
  have hOBeq : OB = (1 - t) • B + t • I := by
    rw [hOB, hI, ht]
    have ha2' : a2 = r * na / D := by field_simp; linarith
    have hc2' : c2 = r * nc / D := by field_simp; linarith
    have hb2' : b2 = 1 - r * na / D - r * nc / D := by rw [← ha2', ← hc2']; linarith
    rw [ha2', hb2', hc2']
    match_scalars <;> (field_simp; try ring)
  have hOCeq : OC = (1 - t) • C + t • I := by
    rw [hOC, hI, ht]
    have ha3' : a3 = r * na / D := by field_simp; linarith
    have hb3' : b3 = r * nb / D := by field_simp; linarith
    have hc3' : c3 = 1 - r * na / D - r * nb / D := by rw [← ha3', ← hb3']; linarith
    rw [ha3', hb3', hc3']
    match_scalars <;> (field_simp; try ring)
  -- the homothety is nondegenerate
  have h1t : (1 : ℝ) - t ≠ 0 := by
    intro h
    exact hne (by rw [hOAeq, hOBeq, h]; module)
  -- the image of the circumcenter under the homothety
  set Y : Pt := (1 - t) • X + t • I with hY
  have hYA : Y - OA = (1 - t) • (X - A) := by rw [hY, hOAeq]; module
  have hYB : Y - OB = (1 - t) • (X - B) := by rw [hY, hOBeq]; module
  have hYC : Y - OC = (1 - t) • (X - C) := by rw [hY, hOCeq]; module
  have hnXB : ‖X - A‖ = ‖X - B‖ := by rw [← dist_eq_norm, ← dist_eq_norm]; exact hXB
  have hnXC : ‖X - A‖ = ‖X - C‖ := by rw [← dist_eq_norm, ← dist_eq_norm]; exact hXC
  have hYAB : dist Y OA = dist Y OB := by
    rw [dist_eq_norm, dist_eq_norm, hYA, hYB, norm_smul, norm_smul, hnXB]
  have hYAC : dist Y OA = dist Y OC := by
    rw [dist_eq_norm, dist_eq_norm, hYA, hYC, norm_smul, norm_smul, hnXC]
  -- `O` and `Y` are both equidistant from the three centres, hence equal
  have hOAB : dist O OA = dist O OB := by rw [hOOA, hOOB]
  have hOAC : dist O OA = dist O OC := by rw [hOOA, hOOC]
  have hp1 : ⟪O - Y, OB - OA⟫ = 0 := inner_eq_zero_of_dist_eq OA OB O Y hOAB hYAB
  have hp2 : ⟪O - Y, OC - OA⟫ = 0 := inner_eq_zero_of_dist_eq OA OC O Y hOAC hYAC
  have hdiff1 : OB - OA = (1 - t) • (B - A) := by rw [hOAeq, hOBeq]; module
  have hdiff2 : OC - OA = (1 - t) • (C - A) := by rw [hOAeq, hOCeq]; module
  rw [hdiff1, real_inner_smul_right] at hp1
  rw [hdiff2, real_inner_smul_right] at hp2
  have hq1 : ⟪O - Y, B - A⟫ = 0 := by
    rcases mul_eq_zero.1 hp1 with h | h
    · exact absurd h h1t
    · exact h
  have hq2 : ⟪O - Y, C - A⟫ = 0 := by
    rcases mul_eq_zero.1 hp2 with h | h
    · exact absurd h h1t
    · exact h
  have hOY : O = Y := by
    have := eq_zero_of_orthogonal_two (O - Y) (B - A) (C - A) hq1 hq2
      (by rw [← hnb, ← hnc]; exact gram_pos A B C hABC)
    rwa [sub_eq_zero] at this
  -- conclude
  rw [hIeq, collinear_iff_of_mem (Set.mem_insert I {X, O})]
  refine ⟨X - I, ?_⟩
  rintro p (rfl | rfl | rfl)
  · exact ⟨0, by simp⟩
  · exact ⟨1, by simp⟩
  · exact ⟨1 - t, by rw [hOY, hY]; simp only [vadd_eq_add]; module⟩

/-! ### The hypotheses are not vacuous

We exhibit an explicit configuration satisfying all the hypotheses of `imo1981_p5`: the
`3`-`4`-`5` right triangle with vertices `(0,0)`, `(4,0)`, `(0,3)`, three circles of radius
`5/7` centred at `(5/7, 5/7)`, `(13/7, 5/7)` and `(5/7, 11/7)`, all passing through the
common point `(9/7, 8/7)`, and the circumcenter `(2, 3/2)`.
-/

/-- A point of the plane given by its two coordinates. -/
noncomputable def pt (x y : ℝ) : Pt := !₂[x, y]

theorem pt_dist (x y a b : ℝ) : dist (pt x y) (pt a b) = Real.sqrt ((x - a) ^ 2 + (y - b) ^ 2) := by
  rw [EuclideanSpace.dist_eq]
  simp only [pt, Fin.sum_univ_two, Real.dist_eq, sq_abs]
  norm_num

theorem pt_dist_eq (x y a b r : ℝ) (hr : 0 ≤ r) (h : (x - a) ^ 2 + (y - b) ^ 2 = r ^ 2) :
    dist (pt x y) (pt a b) = r := by
  rw [pt_dist, h, Real.sqrt_sq hr]

theorem pt_sub (x y a b : ℝ) : pt x y - pt a b = pt (x - a) (y - b) := by
  ext i; fin_cases i <;> simp [pt]

theorem pt_add_smul (x y a b s : ℝ) : pt x y + s • pt a b = pt (x + s * a) (y + s * b) := by
  ext i; fin_cases i <;> simp [pt]

theorem pt_inner (x y a b : ℝ) : ⟪pt x y, pt a b⟫ = x * a + y * b := by
  simp [pt, PiLp.inner_apply, Fin.sum_univ_two]; ring

theorem pt_normsq (x y : ℝ) : ‖pt x y‖ ^ 2 = x ^ 2 + y ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, pt_inner]; ring

theorem pt_combo (a b c x1 y1 x2 y2 x3 y3 : ℝ) :
    a • pt x1 y1 + b • pt x2 y2 + c • pt x3 y3 =
      pt (a * x1 + b * x2 + c * x3) (a * y1 + b * y2 + c * y3) := by
  ext i; fin_cases i <;> simp [pt]

theorem pt_ne (x y a b : ℝ) (h : x ≠ a) : pt x y ≠ pt a b := by
  intro hc
  exact h (by simpa [pt] using congrFun (congrArg WithLp.ofLp hc) 0)

/-- A coordinate criterion for tangency. -/
theorem tangent_pt (px py ax ay bx byy s r : ℝ) (hr : 0 ≤ r)
    (hd : (px - (ax + s * (bx - ax))) ^ 2 + (py - (ay + s * (byy - ay))) ^ 2 = r ^ 2)
    (hp : (px - (ax + s * (bx - ax))) * (bx - ax) + (py - (ay + s * (byy - ay))) * (byy - ay)
      = 0) :
    TangentToLine (pt px py) r (pt ax ay) (pt bx byy) := by
  refine ⟨s, ?_, ?_⟩ <;> rw [pt_sub, pt_add_smul]
  · exact pt_dist_eq _ _ _ _ _ hr hd
  · rw [pt_sub, pt_inner]; exact hp

theorem gram_eq_zero_of_collinear (A B C : Pt) (h : Collinear ℝ ({A, B, C} : Set Pt)) :
    gram A B C = 0 := by
  rw [collinear_iff_of_mem (Set.mem_insert A {B, C})] at h
  obtain ⟨v, hv⟩ := h
  obtain ⟨r1, hr1⟩ := hv B (by simp)
  obtain ⟨r2, hr2⟩ := hv C (by simp)
  have h1 : B - A = r1 • v := by rw [hr1]; simp
  have h2 : C - A = r2 • v := by rw [hr2]; simp
  rw [gram, h1, h2, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq, Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs,
    sq_abs]
  ring

theorem mem_convexHull_of_barycentric (A B C : Pt) (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hsum : a + b + c = 1) :
    a • A + b • B + c • C ∈ convexHull ℝ ({A, B, C} : Set Pt) := by
  rw [show ({A, B, C} : Set Pt) = insert A {B, C} from rfl, convexHull_insert (by simp),
    convexHull_pair, mem_convexJoin]
  by_cases h : b + c = 0
  · have hb0 : b = 0 := by linarith
    have hc0 : c = 0 := by linarith
    have ha1 : a = 1 := by linarith
    refine ⟨A, Set.mem_singleton A, B, left_mem_segment ℝ B C, ?_⟩
    rw [show a • A + b • B + c • C = A by rw [hb0, hc0, ha1]; module]
    exact left_mem_segment ℝ A B
  · have hpos : 0 < b + c := lt_of_le_of_ne (by linarith) (Ne.symm h)
    refine ⟨A, Set.mem_singleton A, (b / (b + c)) • B + (c / (b + c)) • C, ?_, ?_⟩
    · rw [segment_eq_image]
      refine ⟨c / (b + c), ⟨by positivity, by rw [div_le_one hpos]; linarith⟩, ?_⟩
      simp only
      match_scalars <;> (field_simp; try ring)
    · rw [segment_eq_image]
      refine ⟨b + c, ⟨by linarith, by linarith⟩, ?_⟩
      simp only
      match_scalars <;> (field_simp; try linarith)

/-- The hypotheses of `imo1981_p5` are satisfiable: an explicit configuration of three
congruent circles inside a `3`-`4`-`5` triangle, each touching a pair of sides and all passing
through a common point. -/
theorem exists_configuration :
    ∃ (A B C OA OB OC O X : Pt) (r : ℝ), 0 < r ∧
      ¬ Collinear ℝ ({A, B, C} : Set Pt) ∧
      OA ∈ convexHull ℝ ({A, B, C} : Set Pt) ∧
      OB ∈ convexHull ℝ ({A, B, C} : Set Pt) ∧
      OC ∈ convexHull ℝ ({A, B, C} : Set Pt) ∧
      TangentToLine OA r A B ∧ TangentToLine OA r A C ∧
      TangentToLine OB r A B ∧ TangentToLine OB r B C ∧
      TangentToLine OC r A C ∧ TangentToLine OC r B C ∧
      OA ≠ OB ∧
      dist O OA = r ∧ dist O OB = r ∧ dist O OC = r ∧
      dist X A = dist X B ∧ dist X A = dist X C := by
  refine ⟨pt 0 0, pt 4 0, pt 0 3, pt (5/7) (5/7), pt (13/7) (5/7), pt (5/7) (11/7),
    pt (9/7) (8/7), pt 2 (3/2), 5/7, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have hg := gram_eq_zero_of_collinear _ _ _ h
    rw [gram, pt_sub, pt_sub, pt_normsq, pt_normsq, pt_inner] at hg
    norm_num at hg
  · rw [show pt (5/7) (5/7) = (7/12 : ℝ) • pt 0 0 + (5/28 : ℝ) • pt 4 0 + (5/21 : ℝ) • pt 0 3 by
      rw [pt_combo]; norm_num]
    exact mem_convexHull_of_barycentric _ _ _ _ _ _ (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  · rw [show pt (13/7) (5/7) = (25/84 : ℝ) • pt 0 0 + (13/28 : ℝ) • pt 4 0 + (5/21 : ℝ) • pt 0 3 by
      rw [pt_combo]; norm_num]
    exact mem_convexHull_of_barycentric _ _ _ _ _ _ (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  · rw [show pt (5/7) (11/7) = (25/84 : ℝ) • pt 0 0 + (5/28 : ℝ) • pt 4 0 + (11/21 : ℝ) • pt 0 3 by
      rw [pt_combo]; norm_num]
    exact mem_convexHull_of_barycentric _ _ _ _ _ _ (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  · exact tangent_pt _ _ _ _ _ _ (5/28) _ (by norm_num) (by norm_num) (by norm_num)
  · exact tangent_pt _ _ _ _ _ _ (5/21) _ (by norm_num) (by norm_num) (by norm_num)
  · exact tangent_pt _ _ _ _ _ _ (13/28) _ (by norm_num) (by norm_num) (by norm_num)
  · exact tangent_pt _ _ _ _ _ _ (3/7) _ (by norm_num) (by norm_num) (by norm_num)
  · exact tangent_pt _ _ _ _ _ _ (11/21) _ (by norm_num) (by norm_num) (by norm_num)
  · exact tangent_pt _ _ _ _ _ _ (5/7) _ (by norm_num) (by norm_num) (by norm_num)
  · exact pt_ne _ _ _ _ (by norm_num)
  · exact pt_dist_eq _ _ _ _ _ (by norm_num) (by norm_num)
  · exact pt_dist_eq _ _ _ _ _ (by norm_num) (by norm_num)
  · exact pt_dist_eq _ _ _ _ _ (by norm_num) (by norm_num)
  · rw [pt_dist_eq 2 (3/2) 0 0 (5/2) (by norm_num) (by norm_num),
      pt_dist_eq 2 (3/2) 4 0 (5/2) (by norm_num) (by norm_num)]
  · rw [pt_dist_eq 2 (3/2) 0 0 (5/2) (by norm_num) (by norm_num),
      pt_dist_eq 2 (3/2) 0 3 (5/2) (by norm_num) (by norm_num)]

end IMO1981P5
