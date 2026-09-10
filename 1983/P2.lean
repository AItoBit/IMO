import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped RealInnerProductSpace

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

/-!
# IMO 1983, Problem 2

Let `A` be one of the two distinct points of intersection of two unequal coplanar circles
`C₁` and `C₂` with centres `O₁` and `O₂` respectively.  One of the common tangents to the
circles touches `C₁` at `P₁` and `C₂` at `P₂`, while the other touches `C₁` at `Q₁` and `C₂`
at `Q₂`.  Let `M₁` be the midpoint of `P₁Q₁` and `M₂` the midpoint of `P₂Q₂`.
Prove that `∠O₁AO₂ = ∠M₁AM₂`.

The plane is modelled by `EuclideanSpace ℝ (Fin 2)`.  A line through two distinct points `S`
and `T` is tangent to a circle with centre `O` and radius `r` at a point `Z` of the circle
exactly when `Z` lies on the circle and `OZ` is perpendicular to the direction of the line;
this is how the tangency hypotheses are phrased below.
-/

namespace IMO1983Q2

/-- The Euclidean plane. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- In the plane, two vectors orthogonal to one and the same nonzero vector are parallel. -/
lemma perp_parallel (n x y : Plane) (hn : n ≠ 0) (hx : ⟪x, n⟫ = 0) (hy : ⟪y, n⟫ = 0)
    (hx0 : x ≠ 0) : ∃ c : ℝ, y = c • x := by
  have hinner : ∀ a b : Plane, ⟪a, b⟫ = a 0 * b 0 + a 1 * b 1 := by
    intro a b; simp [PiLp.inner_apply, Fin.sum_univ_two]; ring
  rw [hinner] at hx hy
  have hn' : n 0 ≠ 0 ∨ n 1 ≠ 0 := by
    by_contra hc; push_neg at hc
    exact hn (by ext i; fin_cases i <;> simp [hc.1, hc.2])
  have hdet : x 0 * y 1 - x 1 * y 0 = 0 := by
    rcases hn' with h | h
    · have h2 : (x 0 * y 1 - x 1 * y 0) * n 0 = 0 := by
        linear_combination (y 1) * hx - (x 1) * hy
      rcases mul_eq_zero.1 h2 with h' | h'
      · exact h'
      · exact absurd h' h
    · have h2 : (x 0 * y 1 - x 1 * y 0) * n 1 = 0 := by
        linear_combination (-(y 0)) * hx + (x 0) * hy
      rcases mul_eq_zero.1 h2 with h' | h'
      · exact h'
      · exact absurd h' h
  have hx' : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
    by_contra hc; push_neg at hc
    exact hx0 (by ext i; fin_cases i <;> simp [hc.1, hc.2])
  rcases hx' with h | h
  · refine ⟨y 0 / x 0, ?_⟩
    ext i
    fin_cases i <;> simp [PiLp.smul_apply]
    all_goals (field_simp; try nlinarith [hdet])
  · refine ⟨y 1 / x 1, ?_⟩
    ext i
    fin_cases i <;> simp [PiLp.smul_apply]
    all_goals (field_simp; try nlinarith [hdet])

/-- A common tangent line of two circles that meet (so that the distance of the centres is at
most the sum of the radii) touches them at points that correspond under the homothety with
ratio `r₂ / r₁`, and the radius to the point of tangency makes the expected inner product with
the line of centres. -/
lemma tangent_facts (O1 O2 P1 P2 : Plane) (r1 r2 : ℝ) (hr1 : 0 < r1) (hr2 : 0 < r2)
    (hP1 : ‖P1 - O1‖ = r1) (hP2 : ‖P2 - O2‖ = r2) (hne : P1 ≠ P2)
    (h1 : ⟪P1 - O1, P2 - P1⟫ = 0) (h2 : ⟪P2 - O2, P2 - P1⟫ = 0)
    (hd : ‖O2 - O1‖ ≤ r1 + r2) :
    P2 - O2 = (r2 / r1) • (P1 - O1) ∧ ⟪P1 - O1, O2 - O1⟫ = r1 * (r1 - r2) := by
  have hnz : P2 - P1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hu0 : P1 - O1 ≠ 0 := by
    intro h; rw [h, norm_zero] at hP1; exact absurd hP1.symm (ne_of_gt hr1)
  obtain ⟨c, hc⟩ := perp_parallel (P2 - P1) (P1 - O1) (P2 - O2) hnz h1 h2 hu0
  have hnorm : |c| * r1 = r2 := by
    rw [← hP2, hc, norm_smul, hP1]; simp [Real.norm_eq_abs]
  have hdec : O2 - O1 = (1 - c) • (P1 - O1) + (P2 - P1) := by
    have h' : O2 = P2 - c • (P1 - O1) := by rw [← hc]; abel
    rw [h']; module
  have hperp : ⟪(1 - c) • (P1 - O1), P2 - P1⟫ = 0 := by
    rw [real_inner_smul_left, h1, mul_zero]
  have hsq : ‖O2 - O1‖^2 = (1-c)^2 * r1^2 + ‖P2 - P1‖^2 := by
    rw [hdec, norm_add_sq_real, hperp, norm_smul, hP1]
    simp [Real.norm_eq_abs, mul_pow, sq_abs]
  have hnpos : 0 < ‖P2 - P1‖ := norm_pos_iff.mpr hnz
  have hcpos : 0 < c := by
    rcases lt_trichotomy c 0 with h | h | h
    · exfalso
      rw [abs_of_neg h] at hnorm
      have h1c : (1 - c) * r1 = r1 + r2 := by nlinarith
      have hgt : ‖O2 - O1‖^2 > (r1+r2)^2 := by nlinarith [hsq]
      nlinarith [norm_nonneg (O2 - O1), hd]
    · exfalso; rw [h] at hnorm; simp at hnorm; nlinarith
    · exact h
  have hcv : c = r2 / r1 := by
    rw [abs_of_pos hcpos] at hnorm
    field_simp; linarith [hnorm]
  refine ⟨by rw [hc, hcv], ?_⟩
  -- the inner product of the radius with the line of centres
  have hsplit : P2 - P1 = ((r2/r1) - 1) • (P1 - O1) + (O2 - O1) := by
    have h' : P2 = O2 + (r2/r1) • (P1 - O1) := by rw [← hcv, ← hc]; abel
    rw [h']; module
  rw [hsplit, inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hP1] at h1
  have hr1' : r1 ≠ 0 := ne_of_gt hr1
  field_simp at h1 ⊢
  nlinarith [h1]

/-- The core computation, in vector form.  Here `u` and `v` are the radius vectors of the two
points of tangency on the first circle, `e` is the vector from the first to the second centre
and `p` is the vector from the first centre to `A`. -/
lemma angle_eq_of_config (u v e p : Plane) (r1 r2 : ℝ) (hr1 : 0 < r1) (hr2 : 0 < r2)
    (hne : r1 ≠ r2) (hu : ‖u‖ = r1) (hv : ‖v‖ = r1) (hp : ‖p‖ = r1) (hq : ‖p - e‖ = r2)
    (huv : u ≠ v) (hue : ⟪u, e⟫ = r1 * (r1 - r2)) (hve : ⟪v, e⟫ = r1 * (r1 - r2)) :
    InnerProductGeometry.angle (-p) (e - p)
      = InnerProductGeometry.angle ((1/2 : ℝ) • (u + v) - p)
          (e + (r2 / (2*r1)) • (u + v) - p) := by
  have he0 : e ≠ 0 := by
    intro h
    rw [h, inner_zero_right] at hue
    rcases mul_eq_zero.1 hue.symm with h' | h'
    · exact absurd h' (ne_of_gt hr1)
    · exact hne (by linarith)
  have hd2pos : (0:ℝ) < ‖e‖^2 := pow_pos (norm_pos_iff.mpr he0) 2
  have hee : ⟪e, e⟫ = ‖e‖^2 := real_inner_self_eq_norm_sq e
  have hperp1 : ⟪e, u - v⟫ = 0 := by
    rw [inner_sub_right]; linarith [real_inner_comm u e, real_inner_comm v e, hue, hve]
  have hperp2 : ⟪u + v, u - v⟫ = 0 := by
    rw [inner_sub_right, inner_add_left, inner_add_left, real_inner_self_eq_norm_sq,
      real_inner_self_eq_norm_sq, hu, hv]
    linarith [real_inner_comm u v]
  have huvne : u - v ≠ 0 := sub_ne_zero.mpr huv
  obtain ⟨c, hc⟩ := perp_parallel (u - v) e (u + v) huvne hperp1 hperp2 he0
  have hcval : c * ‖e‖^2 = 2 * r1 * (r1 - r2) := by
    have h0 : ⟪u + v, e⟫ = 2 * r1 * (r1 - r2) := by rw [inner_add_left, hue, hve]; ring
    rw [hc, real_inner_smul_left, hee] at h0
    linarith [h0]
  have huv2 : ⟪u, v⟫ < r1^2 := by
    have h1 : 0 < ‖u - v‖^2 := pow_pos (norm_pos_iff.mpr huvne) 2
    rw [← real_inner_self_eq_norm_sq, inner_sub_sub_self, real_inner_self_eq_norm_sq,
      real_inner_self_eq_norm_sq, hu, hv] at h1
    linarith [real_inner_comm u v]
  have hsum2 : ‖u + v‖^2 = 2*r1^2 + 2*⟪u,v⟫ := by
    rw [← real_inner_self_eq_norm_sq, inner_add_add_self, real_inner_self_eq_norm_sq,
      real_inner_self_eq_norm_sq, hu, hv]
    linarith [real_inner_comm u v]
  have hlt : (r1 - r2)^2 < ‖e‖^2 := by
    have h1 : ‖u + v‖^2 = c^2 * ‖e‖^2 := by
      rw [hc, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    have h2 : c^2 * ‖e‖^2 < 4 * r1^2 := by rw [← h1]; linarith [hsum2, huv2]
    have h3 : (2*r1*(r1-r2))^2 = (c^2*‖e‖^2) * ‖e‖^2 := by rw [← hcval]; ring
    have h4 : (2*r1*(r1-r2))^2 < 4*r1^2*‖e‖^2 := by
      rw [h3]; exact (mul_lt_mul_of_pos_right h2 hd2pos).trans_le (le_of_eq (by ring))
    nlinarith [h4, mul_pos hr1 hr1]
  -- replace `u + v` by a multiple of `e`
  have hr1' : (r1 : ℝ) ≠ 0 := ne_of_gt hr1
  have hrw1 : (1/2 : ℝ) • (u + v) - p = (c/2) • e - p := by rw [hc]; module
  have hrw2 : e + (r2 / (2*r1)) • (u + v) - p = (1 + r2/(2*r1)*c) • e - p := by
    rw [hc]; module
  rw [hrw1, hrw2]
  -- now everything is expressed via `e` and `p`
  obtain ⟨D, hD⟩ : ∃ D : ℝ, ⟪e, e⟫ = D := ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ X : ℝ, ⟪e, p⟫ = X := ⟨_, rfl⟩
  have hXp : ⟪p, e⟫ = X := by rw [real_inner_comm]; exact hX
  have hpp : ⟪p, p⟫ = r1^2 := by rw [real_inner_self_eq_norm_sq, hp]
  have hDval : D = ‖e‖^2 := by rw [← hD, real_inner_self_eq_norm_sq]
  have hDpos : 0 < D := by rw [hDval]; exact hd2pos
  have hDlt : (r1-r2)^2 < D := by rw [hDval]; exact hlt
  have hcval' : c * D = 2 * r1 * (r1 - r2) := by rw [hDval]; exact hcval
  have hXval : X = (r1^2 - r2^2 + D)/2 := by
    have h1 : ‖p - e‖^2 = r2^2 := by rw [hq]
    rw [← real_inner_self_eq_norm_sq, inner_sub_sub_self, hpp, hD, hX, hXp] at h1
    linarith
  have expand : ∀ a b : ℝ, ⟪a • e - p, b • e - p⟫ = a*b*D - (a+b)*X + r1^2 := by
    intro a b
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      hD, hX, hXp, hpp]
    ring
  have hDne : D ≠ 0 := ne_of_gt hDpos
  have hsne : D - (r1-r2)^2 ≠ 0 := by linarith
  have hc' : c = 2*r1*(r1-r2)/D := by field_simp; linarith [hcval']
  have key1 : ⟪(c/2) • e - p, (c/2) • e - p⟫ = r1*r2*(D-(r1-r2)^2)/D := by
    rw [expand, hXval, hc']; field_simp; ring
  have key2 : ⟪(1 + r2/(2*r1)*c) • e - p, (1 + r2/(2*r1)*c) • e - p⟫
      = r1*r2*(D-(r1-r2)^2)/D := by
    rw [expand, hXval, hc']; field_simp; ring
  have key3 : ⟪(c/2) • e - p, (1 + r2/(2*r1)*c) • e - p⟫
      = (r1^2 - X)*(D-(r1-r2)^2)/D := by
    rw [expand, hXval, hc']; field_simp; ring
  have hnn1 : ‖(c/2) • e - p‖^2 = r1*r2*(D-(r1-r2)^2)/D := by
    rw [← real_inner_self_eq_norm_sq]; exact key1
  have hnn2 : ‖(1 + r2/(2*r1)*c) • e - p‖^2 = r1*r2*(D-(r1-r2)^2)/D := by
    rw [← real_inner_self_eq_norm_sq]; exact key2
  have hprod : ‖(c/2) • e - p‖ * ‖(1 + r2/(2*r1)*c) • e - p‖ = r1*r2*(D-(r1-r2)^2)/D := by
    have h : ‖(c/2) • e - p‖ = ‖(1 + r2/(2*r1)*c) • e - p‖ := by
      nlinarith [norm_nonneg ((c/2) • e - p), norm_nonneg ((1 + r2/(2*r1)*c) • e - p)]
    rw [h, ← sq]; exact hnn2
  have hip : ⟪-p, e - p⟫ = r1^2 - X := by
    simp only [inner_neg_left, inner_sub_right, hXp, hpp]; ring
  have hnp : ‖(-p : Plane)‖ = r1 := by rw [norm_neg]; exact hp
  have hep : ‖e - p‖ = r2 := by rw [norm_sub_rev]; exact hq
  simp only [InnerProductGeometry.angle]
  congr 1
  rw [hip, hnp, hep, key3, hprod]
  field_simp

/-- **IMO 1983, Problem 2.**
`C₁` is the circle with centre `O₁` and radius `r₁`, `C₂` the circle with centre `O₂` and
radius `r₂`; the circles are unequal (`r₁ ≠ r₂`) and `A` is a common point.  The line `P₁P₂`
is a common tangent (touching `C₁` at `P₁` and `C₂` at `P₂`) and the line `Q₁Q₂` is the other
one (touching `C₁` at `Q₁` and `C₂` at `Q₂`).  With `M₁` the midpoint of `P₁Q₁` and `M₂` the
midpoint of `P₂Q₂`, we have `∠O₁AO₂ = ∠M₁AM₂`. -/
theorem angle_O1AO2_eq_angle_M1AM2
    (O1 O2 A P1 P2 Q1 Q2 M1 M2 : Plane) (r1 r2 : ℝ)
    (hr1 : 0 < r1) (hr2 : 0 < r2) (hrne : r1 ≠ r2)
    (hA1 : dist A O1 = r1) (hA2 : dist A O2 = r2)
    (hP1 : dist P1 O1 = r1) (hP2 : dist P2 O2 = r2)
    (hQ1 : dist Q1 O1 = r1) (hQ2 : dist Q2 O2 = r2)
    (hPne : P1 ≠ P2) (htP1 : ⟪P1 - O1, P2 - P1⟫ = 0) (htP2 : ⟪P2 - O2, P2 - P1⟫ = 0)
    (hQne : Q1 ≠ Q2) (htQ1 : ⟪Q1 - O1, Q2 - Q1⟫ = 0) (htQ2 : ⟪Q2 - O2, Q2 - Q1⟫ = 0)
    (htangents : P1 ≠ Q1)
    (hM1 : M1 = midpoint ℝ P1 Q1) (hM2 : M2 = midpoint ℝ P2 Q2) :
    EuclideanGeometry.angle O1 A O2 = EuclideanGeometry.angle M1 A M2 := by
  -- translate the distance hypotheses into norms
  rw [dist_eq_norm] at hA1 hA2 hP1 hP2 hQ1 hQ2
  -- the distance between the centres is at most the sum of the radii
  have hd : ‖O2 - O1‖ ≤ r1 + r2 := by
    have : O2 - O1 = -(A - O2) + (A - O1) := by abel
    calc ‖O2 - O1‖ ≤ ‖(-(A - O2) : Plane)‖ + ‖A - O1‖ := by rw [this]; exact norm_add_le _ _
    _ = r1 + r2 := by rw [norm_neg, hA1, hA2]; ring
  obtain ⟨hP2eq, hPue⟩ :=
    tangent_facts O1 O2 P1 P2 r1 r2 hr1 hr2 hP1 hP2 hPne htP1 htP2 hd
  obtain ⟨hQ2eq, hQue⟩ :=
    tangent_facts O1 O2 Q1 Q2 r1 r2 hr1 hr2 hQ1 hQ2 hQne htQ1 htQ2 hd
  have huv : P1 - O1 ≠ Q1 - O1 := fun h => htangents (sub_left_inj.mp h)
  have hpq : ‖(A - O1) - (O2 - O1)‖ = r2 := by
    have : (A - O1) - (O2 - O1) = A - O2 := by abel
    rw [this]; exact hA2
  have main := angle_eq_of_config (P1 - O1) (Q1 - O1) (O2 - O1) (A - O1) r1 r2 hr1 hr2 hrne
    hP1 hQ1 hA1 hpq huv hPue hQue
  have e1 : O1 - A = -(A - O1) := by abel
  have e2 : O2 - A = (O2 - O1) - (A - O1) := by abel
  have e3 : M1 - A = (1/2 : ℝ) • ((P1 - O1) + (Q1 - O1)) - (A - O1) := by
    rw [hM1, midpoint_eq_smul_add]
    simp only [invOf_eq_inv]
    module
  have e4 : M2 - A = (O2 - O1) + (r2 / (2*r1)) • ((P1 - O1) + (Q1 - O1)) - (A - O1) := by
    have hP2' : P2 = O2 + (r2/r1) • (P1 - O1) := by rw [← hP2eq]; abel
    have hQ2' : Q2 = O2 + (r2/r1) • (Q1 - O1) := by rw [← hQ2eq]; abel
    rw [hM2, midpoint_eq_smul_add, hP2', hQ2']
    simp only [invOf_eq_inv]
    have hr1' : (r1 : ℝ) ≠ 0 := ne_of_gt hr1
    match_scalars <;> field_simp <;> ring
  show InnerProductGeometry.angle (O1 - A) (O2 - A) = InnerProductGeometry.angle (M1 - A) (M2 - A)
  rw [e1, e2, e3, e4]
  exact main

/-! ### The hypotheses are satisfiable

To make sure the theorem above is not vacuous, we exhibit an explicit configuration: the
circles of radii `2` and `1` centred at `(0,0)` and `(2,0)`. -/

/-- A point of the plane given by its two coordinates. -/
noncomputable def mkP (a b : ℝ) : Plane := !₂[a, b]

lemma mkP_sub (a b c d : ℝ) : mkP a b - mkP c d = mkP (a-c) (b-d) := by
  simp only [mkP]; ext i; fin_cases i <;> simp

lemma mkP_inner (a b c d : ℝ) : ⟪mkP a b, mkP c d⟫ = a*c + b*d := by
  simp [mkP, PiLp.inner_apply, Fin.sum_univ_two]; ring

lemma mkP_norm (a b : ℝ) : ‖mkP a b‖ = Real.sqrt (a^2 + b^2) := by
  rw [mkP, EuclideanSpace.norm_eq]; simp [Fin.sum_univ_two]

lemma mkP_ne_of_fst (a b c d : ℝ) (h : a ≠ c) : mkP a b ≠ mkP c d := by
  intro hh
  have h0 : (mkP a b) 0 = (mkP c d) 0 := by rw [hh]
  simp [mkP] at h0; exact h h0

lemma mkP_ne_of_snd (a b c d : ℝ) (h : b ≠ d) : mkP a b ≠ mkP c d := by
  intro hh
  have h0 : (mkP a b) 1 = (mkP c d) 1 := by rw [hh]
  simp [mkP] at h0; exact h h0

lemma mkP_midpoint (a b c d : ℝ) :
    midpoint ℝ (mkP a b) (mkP c d) = mkP ((a+c)/2) ((b+d)/2) := by
  rw [midpoint_eq_smul_add]; simp only [invOf_eq_inv]
  ext i; fin_cases i <;> simp [mkP] <;> ring

/-- The configuration described in the problem does occur: there are circles, tangency points
and midpoints satisfying all the hypotheses of `angle_O1AO2_eq_angle_M1AM2`. -/
theorem exists_configuration :
    ∃ (O1 O2 A P1 P2 Q1 Q2 M1 M2 : Plane) (r1 r2 : ℝ),
      0 < r1 ∧ 0 < r2 ∧ r1 ≠ r2 ∧
      dist A O1 = r1 ∧ dist A O2 = r2 ∧
      dist P1 O1 = r1 ∧ dist P2 O2 = r2 ∧ dist Q1 O1 = r1 ∧ dist Q2 O2 = r2 ∧
      P1 ≠ P2 ∧ ⟪P1 - O1, P2 - P1⟫ = 0 ∧ ⟪P2 - O2, P2 - P1⟫ = 0 ∧
      Q1 ≠ Q2 ∧ ⟪Q1 - O1, Q2 - Q1⟫ = 0 ∧ ⟪Q2 - O2, Q2 - Q1⟫ = 0 ∧
      P1 ≠ Q1 ∧ M1 = midpoint ℝ P1 Q1 ∧ M2 = midpoint ℝ P2 Q2 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h15 : Real.sqrt 15 ^ 2 = 15 := Real.sq_sqrt (by norm_num)
  have h3pos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  refine ⟨mkP 0 0, mkP 2 0, mkP (7/4) (Real.sqrt 15/4), mkP 1 (Real.sqrt 3),
    mkP (5/2) (Real.sqrt 3/2), mkP 1 (-Real.sqrt 3), mkP (5/2) (-(Real.sqrt 3)/2),
    mkP 1 0, mkP (5/2) 0, 2, 1, by norm_num, by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [dist_eq_norm, mkP_sub, mkP_norm,
      show (7/4-0:ℝ)^2 + (Real.sqrt 15/4 - 0)^2 = 2^2 by
        rw [show (Real.sqrt 15/4-0) = Real.sqrt 15/4 by ring, div_pow, h15]; norm_num]
    exact Real.sqrt_sq (by norm_num)
  · rw [dist_eq_norm, mkP_sub, mkP_norm,
      show (7/4-2:ℝ)^2 + (Real.sqrt 15/4 - 0)^2 = 1^2 by
        rw [show (Real.sqrt 15/4-0) = Real.sqrt 15/4 by ring, div_pow, h15]; norm_num]
    exact Real.sqrt_sq (by norm_num)
  · rw [dist_eq_norm, mkP_sub, mkP_norm,
      show (1-0:ℝ)^2 + (Real.sqrt 3 - 0)^2 = 2^2 by
        rw [show (Real.sqrt 3-0) = Real.sqrt 3 by ring, h3]; norm_num]
    exact Real.sqrt_sq (by norm_num)
  · rw [dist_eq_norm, mkP_sub, mkP_norm,
      show (5/2-2:ℝ)^2 + (Real.sqrt 3/2 - 0)^2 = 1^2 by
        rw [show (Real.sqrt 3/2-0) = Real.sqrt 3/2 by ring, div_pow, h3]; norm_num]
    exact Real.sqrt_sq (by norm_num)
  · rw [dist_eq_norm, mkP_sub, mkP_norm,
      show (1-0:ℝ)^2 + (-Real.sqrt 3 - 0)^2 = 2^2 by
        rw [show (-Real.sqrt 3-0) = -Real.sqrt 3 by ring, neg_pow, h3]; norm_num]
    exact Real.sqrt_sq (by norm_num)
  · rw [dist_eq_norm, mkP_sub, mkP_norm,
      show (5/2-2:ℝ)^2 + (-(Real.sqrt 3)/2 - 0)^2 = 1^2 by
        rw [show (-(Real.sqrt 3)/2-0) = -(Real.sqrt 3)/2 by ring, div_pow, neg_pow, h3]
        norm_num]
    exact Real.sqrt_sq (by norm_num)
  · exact mkP_ne_of_fst _ _ _ _ (by norm_num)
  · rw [mkP_sub, mkP_sub, mkP_inner]; nlinarith [h3]
  · rw [mkP_sub, mkP_sub, mkP_inner]; nlinarith [h3]
  · exact mkP_ne_of_fst _ _ _ _ (by norm_num)
  · rw [mkP_sub, mkP_sub, mkP_inner]; nlinarith [h3]
  · rw [mkP_sub, mkP_sub, mkP_inner]; nlinarith [h3]
  · exact mkP_ne_of_snd _ _ _ _ (by intro h; nlinarith [h3pos])
  · rw [mkP_midpoint]; norm_num
  · rw [mkP_midpoint, show (Real.sqrt 3 / 2 + -Real.sqrt 3 / 2) / 2 = 0 by ring]; norm_num

end IMO1983Q2
