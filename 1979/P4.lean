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

set_option grind.warning false

/-!
# IMO 1979 Problem 4

We consider a point `P` in a plane `p` and a point `Q ∉ p`.  Determine all points `R` of `p` for
which
$$\frac{QP + PR}{QR}$$
is maximum.

**Answer.** Let `T` be the orthogonal projection of `Q` on `p`.  The ratio is maximal exactly for
the points `R` of `p` lying on the ray `PT` with `PR = PQ`; that is, `R` is the intersection of the
ray `PT` with the sphere of centre `P` and radius `PQ`.  (If `PQ ⊥ p`, then `T = P`, the ray is
undefined and the maximum is attained at every point `R` of `p` with `PR = PQ`.)  The maximal value
of the ratio is `√(2·PQ / (PQ - PT))`.

Below the plane through `P` with (nonzero) normal vector `nv` is `Imo1979P4.plane P nv`, and `T` is
`Imo1979P4.foot P Q nv`.  The condition "`R` lies on the ray `PT`, this condition being vacuous
when `T = P`" is expressed as the equality case of the Cauchy–Schwarz inequality,
`⟪R - P, T - P⟫ = ‖R - P‖ * ‖T - P‖`.
-/

namespace Imo1979P4

open scoped RealInnerProductSpace

/-- The ambient Euclidean 3-space. -/
abbrev E : Type := EuclideanSpace ℝ (Fin 3)

/-- The plane through the point `P` with normal vector `nv`. -/
def plane (P nv : E) : Set E := {R : E | ⟪nv, R - P⟫ = 0}

/-- The orthogonal projection (the "foot") of the point `Q` on the plane
`Imo1979P4.plane P nv`. -/
noncomputable def foot (P Q nv : E) : E := Q - (⟪nv, Q - P⟫ / ‖nv‖ ^ 2) • nv

/-- The maximal value of `(QP + PR)/QR` for `R` in the plane through `P` with normal `nv`. -/
noncomputable def maxRatio (P Q nv : E) : ℝ :=
  Real.sqrt (2 * dist P Q / (dist P Q - dist P (foot P Q nv)))

section Basic

variable {P Q nv : E}

lemma mem_plane_iff {R : E} : R ∈ plane P nv ↔ ⟪nv, R - P⟫ = 0 := Iff.rfl

lemma self_mem_plane : P ∈ plane P nv := by
  simp [plane]

/-- The vector from `P` to the foot `T` of the perpendicular from `Q`. -/
lemma foot_sub (P Q nv : E) :
    foot P Q nv - P = (Q - P) - (⟪nv, Q - P⟫ / ‖nv‖ ^ 2) • nv := by
  simp [foot]
  abel

lemma inner_nv_foot_sub (hnv : nv ≠ 0) : ⟪nv, foot P Q nv - P⟫ = 0 := by
  have hn : ‖nv‖ ^ 2 ≠ 0 := by positivity
  rw [foot_sub, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
  field_simp
  ring

/-- Pythagoras: `PQ² = PT² + TQ²`, with `TQ ≠ 0` exactly when `Q` is off the plane. -/
lemma norm_sq_decomp (hnv : nv ≠ 0) :
    ‖Q - P‖ ^ 2 = ‖foot P Q nv - P‖ ^ 2 + (⟪nv, Q - P⟫ / ‖nv‖ ^ 2) ^ 2 * ‖nv‖ ^ 2 := by
  set c : ℝ := ⟪nv, Q - P⟫ / ‖nv‖ ^ 2 with hc
  have hu : foot P Q nv - P = (Q - P) - c • nv := foot_sub P Q nv
  have h0 : ⟪nv, (Q - P) - c • nv⟫ = 0 := by
    have := inner_nv_foot_sub (P := P) (Q := Q) (nv := nv) hnv
    rwa [hu] at this
  have hQP : Q - P = ((Q - P) - c • nv) + c • nv := by abel
  rw [hQP, hu]
  rw [norm_add_sq_real]
  have : ⟪(Q - P) - c • nv, c • nv⟫ = 0 := by
    rw [real_inner_smul_right, real_inner_comm, h0]
    ring
  rw [this, norm_smul]
  simp [mul_pow, sq_abs]

/-- `PT < PQ` : the foot of the perpendicular is strictly closer to `P` than `Q` is. -/
lemma dist_foot_lt (hnv : nv ≠ 0) (hQ : Q ∉ plane P nv) :
    ‖foot P Q nv - P‖ < ‖Q - P‖ := by
  have hc : ⟪nv, Q - P⟫ ≠ 0 := hQ
  have hn : (0:ℝ) < ‖nv‖ ^ 2 := by positivity
  have hpos : 0 < (⟪nv, Q - P⟫ / ‖nv‖ ^ 2) ^ 2 * ‖nv‖ ^ 2 := by
    have : (⟪nv, Q - P⟫ / ‖nv‖ ^ 2) ≠ 0 := by
      exact div_ne_zero hc (ne_of_gt hn)
    positivity
  have hsq := norm_sq_decomp (P := P) (Q := Q) (nv := nv) hnv
  have h1 : ‖foot P Q nv - P‖ ^ 2 < ‖Q - P‖ ^ 2 := by nlinarith
  have h2 : (0:ℝ) ≤ ‖foot P Q nv - P‖ := norm_nonneg _
  nlinarith [norm_nonneg (Q - P)]

/-- For `R` in the plane, the inner product with `Q - P` only sees the in-plane part `T - P`. -/
lemma inner_eq_inner_foot {R : E} (hR : R ∈ plane P nv) :
    ⟪R - P, Q - P⟫ = ⟪R - P, foot P Q nv - P⟫ := by
  have h : ⟪nv, R - P⟫ = 0 := hR
  have h' : ⟪R - P, nv⟫ = 0 := by rw [real_inner_comm]; exact h
  have h2 : ⟪R - P, (⟪nv, Q - P⟫ / ‖nv‖ ^ 2) • nv⟫ = 0 := by
    rw [real_inner_smul_right, h', mul_zero]
  rw [foot_sub]
  conv_rhs => rw [inner_sub_right, h2]
  ring

end Basic

/-- The algebraic heart of the problem: with `d = PQ`, `a = PT`, `r = PR` and
`t = ⟪R - P, T - P⟫` we have `2·d·QR² - (d + r)²·(d - a) = (d + a)(r - d)² + 4d(ra - t) ≥ 0`. -/
lemma key_identity (d a r t : ℝ) :
    2 * d * (d ^ 2 - 2 * t + r ^ 2) - (d + r) ^ 2 * (d - a)
      = (d + a) * (r - d) ^ 2 + 4 * d * (r * a - t) := by
  ring

section Main

variable {P Q nv : E}

/-- The distance from `Q` to a point of the plane is positive. -/
lemma dist_pos_of_mem (hQ : Q ∉ plane P nv) {R : E} (hR : R ∈ plane P nv) : 0 < ‖Q - R‖ := by
  have hne : Q ≠ R := by
    rintro rfl
    exact hQ hR
  simpa [sub_eq_zero] using (norm_pos_iff.mpr (sub_ne_zero.mpr hne))

/-- The common core of the solution: the bound together with its equality case. -/
lemma core (hnv : nv ≠ 0) (hQ : Q ∉ plane P nv) {R : E} (hR : R ∈ plane P nv) :
    (dist Q P + dist P R) / dist Q R ≤ maxRatio P Q nv ∧
      ((dist Q P + dist P R) / dist Q R = maxRatio P Q nv ↔
        dist P R = dist P Q ∧
          ⟪R - P, foot P Q nv - P⟫ = ‖R - P‖ * ‖foot P Q nv - P‖) := by
  set d : ℝ := ‖Q - P‖ with hd_def
  set a : ℝ := ‖foot P Q nv - P‖ with ha_def
  set r : ℝ := ‖R - P‖ with hr_def
  set t : ℝ := ⟪R - P, foot P Q nv - P⟫ with ht_def
  have ha : 0 ≤ a := norm_nonneg _
  have hr : 0 ≤ r := norm_nonneg _
  have had : a < d := dist_foot_lt hnv hQ
  have hd : 0 < d := lt_of_le_of_lt ha had
  have hDpos : 0 < d - a := by linarith
  have hcs : t ≤ r * a := real_inner_le_norm _ _
  have hQRpos : 0 < ‖Q - R‖ := dist_pos_of_mem hQ hR
  have hinner : ⟪Q - P, R - P⟫ = t := by
    rw [real_inner_comm]; exact inner_eq_inner_foot hR
  have hQRsq : ‖Q - R‖ ^ 2 = d ^ 2 - 2 * t + r ^ 2 := by
    have hsplit : Q - R = (Q - P) - (R - P) := by abel
    rw [hsplit, norm_sub_sq_real, hinner]
  have eQP : dist Q P = d := by rw [hd_def, dist_eq_norm]
  have ePR : dist P R = r := by rw [hr_def, dist_eq_norm, norm_sub_rev]
  have eQR : dist Q R = ‖Q - R‖ := dist_eq_norm Q R
  have ePQ : dist P Q = d := by rw [hd_def, dist_eq_norm, norm_sub_rev]
  have ePT : dist P (foot P Q nv) = a := by rw [ha_def, dist_eq_norm, norm_sub_rev]
  have hM : maxRatio P Q nv = Real.sqrt (2 * d / (d - a)) := by
    simp only [maxRatio, ePQ, ePT]
  set M : ℝ := Real.sqrt (2 * d / (d - a)) with hM_def
  have hMsq : M ^ 2 = 2 * d / (d - a) := Real.sq_sqrt (by positivity)
  have hnn : 0 ≤ M * ‖Q - R‖ := by positivity
  have hX2 : (M * ‖Q - R‖) ^ 2 * (d - a) = 2 * d * (d ^ 2 - 2 * t + r ^ 2) := by
    have hexp : (M * ‖Q - R‖) ^ 2 = M ^ 2 * ‖Q - R‖ ^ 2 := by ring
    rw [hexp, hMsq, hQRsq]
    field_simp
  have hid := key_identity d a r t
  have hA : 0 ≤ (d + a) * (r - d) ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg _)
  have hB : 0 ≤ 4 * d * (r * a - t) :=
    mul_nonneg (by linarith) (by linarith)
  have h1 : (d + r) ^ 2 * (d - a) ≤ 2 * d * (d ^ 2 - 2 * t + r ^ 2) := by linarith
  have hkey : (d + r) ^ 2 ≤ (M * ‖Q - R‖) ^ 2 :=
    le_of_mul_le_mul_right (by linarith [hX2]) hDpos
  rw [eQP, ePR, eQR, hM]
  constructor
  · rw [div_le_iff₀ hQRpos]
    nlinarith [hkey, hnn, hd, hr]
  · rw [div_eq_iff (ne_of_gt hQRpos), ePQ]
    constructor
    · intro heq
      have hsq : (d + r) ^ 2 * (d - a) = 2 * d * (d ^ 2 - 2 * t + r ^ 2) := by
        rw [heq]; exact hX2
      have hA0 : (d + a) * (r - d) ^ 2 = 0 := by linarith
      have hB0 : 4 * d * (r * a - t) = 0 := by linarith
      have hrd : r = d := by
        rcases mul_eq_zero.mp hA0 with h | h
        · linarith
        · have : r - d = 0 := by
            exact pow_eq_zero_iff (two_ne_zero) |>.mp h
          linarith
      have hta : t = r * a := by
        rcases mul_eq_zero.mp hB0 with h | h
        · linarith
        · linarith
      exact ⟨hrd, hta⟩
    · rintro ⟨hrd, hta⟩
      have hsq : (d + r) ^ 2 * (d - a) = 2 * d * (d ^ 2 - 2 * t + r ^ 2) := by
        rw [hrd, hta, hrd]; ring
      have : (d + r) ^ 2 = (M * ‖Q - R‖) ^ 2 := by
        have := hX2
        have hmul : (d + r) ^ 2 * (d - a) = (M * ‖Q - R‖) ^ 2 * (d - a) := by
          rw [hsq, hX2]
        exact mul_right_cancel₀ (ne_of_gt hDpos) hmul
      nlinarith [this, hnn, hd, hr]

/-- **IMO 1979, Problem 4** (the inequality): for every point `R` of the plane `p` through `P`
with normal `nv`, the ratio `(QP + PR)/QR` is at most `√(2·PQ/(PQ - PT))`, where `T` is the
orthogonal projection of `Q` on `p`. -/
theorem ratio_le_maxRatio (hnv : nv ≠ 0) (hQ : Q ∉ plane P nv) {R : E} (hR : R ∈ plane P nv) :
    (dist Q P + dist P R) / dist Q R ≤ maxRatio P Q nv := (core hnv hQ hR).1

/-- **IMO 1979, Problem 4** (the equality case): the ratio `(QP + PR)/QR` attains its maximal
value exactly when `PR = PQ` and `R` lies on the ray `PT` (the latter condition being automatic
when `T = P`, i.e. when `PQ ⊥ p`). -/
theorem ratio_eq_maxRatio_iff (hnv : nv ≠ 0) (hQ : Q ∉ plane P nv) {R : E}
    (hR : R ∈ plane P nv) :
    (dist Q P + dist P R) / dist Q R = maxRatio P Q nv ↔
      dist P R = dist P Q ∧
        ⟪R - P, foot P Q nv - P⟫ = ‖R - P‖ * ‖foot P Q nv - P‖ := (core hnv hQ hR).2

/-- In `3`-space every nonzero vector admits a nonzero orthogonal vector. -/
lemma exists_orthogonal_ne_zero (hnv : nv ≠ 0) : ∃ w : E, w ≠ 0 ∧ ⟪nv, w⟫ = 0 := by
  have h1 : Module.finrank ℝ ((ℝ ∙ nv)ᗮ : Submodule ℝ E) = 2 := by
    have h := Submodule.finrank_add_finrank_orthogonal (𝕜 := ℝ) (ℝ ∙ nv)
    rw [finrank_span_singleton hnv] at h
    simp at h
    omega
  obtain ⟨w, hw⟩ := Module.finrank_pos_iff_exists_ne_zero.mp
    (by omega : 0 < Module.finrank ℝ ((ℝ ∙ nv)ᗮ : Submodule ℝ E))
  refine ⟨w.1, by simpa using hw, ?_⟩
  have hmem := w.2
  rw [Submodule.mem_orthogonal] at hmem
  exact hmem nv (Submodule.mem_span_singleton_self nv)

/-- Any admissible direction in the plane produces a maximizing point. -/
lemma exists_of_direction (hnv : nv ≠ 0) (hQ : Q ∉ plane P nv) {w : E} (hw0 : w ≠ 0)
    (hwperp : ⟪nv, w⟫ = 0)
    (hcond : ⟪w, foot P Q nv - P⟫ = ‖w‖ * ‖foot P Q nv - P‖) :
    ∃ R ∈ plane P nv, (dist Q P + dist P R) / dist Q R = maxRatio P Q nv := by
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  set d : ℝ := ‖Q - P‖ with hd_def
  have hd0 : 0 ≤ d := norm_nonneg _
  set R : E := P + (d / ‖w‖) • w with hR_def
  have hRP : R - P = (d / ‖w‖) • w := by rw [hR_def]; abel
  have hmem : R ∈ plane P nv := by
    show ⟪nv, R - P⟫ = 0
    rw [hRP, real_inner_smul_right, hwperp, mul_zero]
  have hnorm : ‖R - P‖ = d := by
    rw [hRP, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ d / ‖w‖)]
    field_simp
  refine ⟨R, hmem, ?_⟩
  rw [ratio_eq_maxRatio_iff hnv hQ hmem]
  constructor
  · rw [dist_eq_norm, dist_eq_norm, norm_sub_rev P R, norm_sub_rev P Q, hnorm]
  · rw [hRP, real_inner_smul_left, hcond, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ d / ‖w‖)]
    field_simp

/-- **IMO 1979, Problem 4** (existence): the maximum is attained. -/
theorem exists_ratio_eq_maxRatio (hnv : nv ≠ 0) (hQ : Q ∉ plane P nv) :
    ∃ R ∈ plane P nv, (dist Q P + dist P R) / dist Q R = maxRatio P Q nv := by
  by_cases hu0 : foot P Q nv - P = 0
  · obtain ⟨w, hw0, hwperp⟩ := exists_orthogonal_ne_zero hnv
    refine exists_of_direction hnv hQ hw0 hwperp ?_
    rw [hu0]
    simp
  · refine exists_of_direction hnv hQ hu0 (inner_nv_foot_sub hnv) ?_
    rw [real_inner_self_eq_norm_mul_norm]

/-- **IMO 1979, Problem 4** (the non-degenerate case, explicitly): if `PQ` is not perpendicular
to the plane, i.e. `T ≠ P`, then the ratio `(QP + PR)/QR` is maximal for exactly one point of the
plane, namely the intersection `P + (PQ/PT) • (T - P)` of the ray `PT` with the sphere of centre
`P` and radius `PQ`. -/
theorem eq_maximizer_iff_of_foot_ne (hnv : nv ≠ 0) (hQ : Q ∉ plane P nv)
    (hT : foot P Q nv ≠ P) {R : E} (hR : R ∈ plane P nv) :
    (dist Q P + dist P R) / dist Q R = maxRatio P Q nv ↔
      R = P + (dist P Q / dist P (foot P Q nv)) • (foot P Q nv - P) := by
  have hu : foot P Q nv - P ≠ 0 := sub_ne_zero.mpr hT
  have ha : 0 < ‖foot P Q nv - P‖ := norm_pos_iff.mpr hu
  have ePQ : dist P Q = ‖Q - P‖ := by rw [dist_eq_norm, norm_sub_rev]
  have ePR : dist P R = ‖R - P‖ := by rw [dist_eq_norm, norm_sub_rev]
  have ePT : dist P (foot P Q nv) = ‖foot P Q nv - P‖ := by rw [dist_eq_norm, norm_sub_rev]
  rw [ratio_eq_maxRatio_iff hnv hQ hR, ePQ, ePR, ePT]
  constructor
  · rintro ⟨h1, h2⟩
    rw [inner_eq_norm_mul_iff_real] at h2
    have h3 : ‖foot P Q nv - P‖ • (R - P) = ‖Q - P‖ • (foot P Q nv - P) := by
      rw [h2, h1]
    have h4 := congrArg (fun v : E => (‖foot P Q nv - P‖)⁻¹ • v) h3
    have hw : R - P = (‖Q - P‖ / ‖foot P Q nv - P‖) • (foot P Q nv - P) := by
      simpa [smul_smul, inv_mul_cancel₀ (ne_of_gt ha), div_eq_inv_mul] using h4
    rw [← hw]
    abel
  · rintro rfl
    have hw : (P + (‖Q - P‖ / ‖foot P Q nv - P‖) • (foot P Q nv - P)) - P
        = (‖Q - P‖ / ‖foot P Q nv - P‖) • (foot P Q nv - P) := by abel
    rw [hw]
    have habs : |‖Q - P‖ / ‖foot P Q nv - P‖| = ‖Q - P‖ / ‖foot P Q nv - P‖ :=
      abs_of_nonneg (by positivity)
    constructor
    · rw [norm_smul, Real.norm_eq_abs, habs]
      field_simp
    · rw [real_inner_smul_left, real_inner_self_eq_norm_mul_norm, norm_smul, Real.norm_eq_abs,
        habs]
      field_simp

/-- **IMO 1979, Problem 4** (complete answer).  Let `P` be a point of the plane `p` (given here
as the plane through `P` with nonzero normal vector `nv`) and let `Q ∉ p`.  Then
`√(2·PQ/(PQ - PT))`, with `T` the orthogonal projection of `Q` on `p`, is the greatest value of
`(QP + PR)/QR` for `R ∈ p`, and it is attained exactly at those points `R` of `p` with `PR = PQ`
lying on the ray `PT` (the ray condition degenerating to no condition at all when `T = P`, i.e.
when `PQ ⊥ p`). -/
theorem imo1979_p4 (hnv : nv ≠ 0) (hQ : Q ∉ plane P nv) :
    IsGreatest ((fun R : E => (dist Q P + dist P R) / dist Q R) '' plane P nv)
        (maxRatio P Q nv) ∧
      ∀ R ∈ plane P nv,
        ((dist Q P + dist P R) / dist Q R = maxRatio P Q nv ↔
          dist P R = dist P Q ∧
            ⟪R - P, foot P Q nv - P⟫ = ‖R - P‖ * ‖foot P Q nv - P‖) := by
  refine ⟨⟨?_, ?_⟩, fun R hR => ratio_eq_maxRatio_iff hnv hQ hR⟩
  · obtain ⟨R, hR, hval⟩ := exists_ratio_eq_maxRatio hnv hQ
    exact ⟨R, hR, hval⟩
  · rintro y ⟨R, hR, rfl⟩
    exact ratio_le_maxRatio hnv hQ hR

end Main

end Imo1979P4
