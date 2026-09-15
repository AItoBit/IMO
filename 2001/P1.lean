/-
IMO 2001, Problem 1.
Verified with Lean 4.34.0 and mathlib commit
7801e8406155c31b340d28e2762f754d02b5e9b0.

Vertices: t.points 0 = A, t.points 1 = B, t.points 2 = C.
P is constructed by orthogonal projection onto BC.
O is mathlib's circumcenter. Angles are in radians.

Main theorem: IMO2001P1.imo2001_p1
Axiom audit: propext, Classical.choice, Quot.sound only.
-/

import Mathlib.Geometry.Euclidean.Angle.Sphere
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Projection
import Mathlib.Geometry.Euclidean.Angle.Unoriented.RightAngle
import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Tactic

open Real EuclideanGeometry
open scoped EuclideanGeometry

namespace IMO2001P1

lemma trig_bound {B C : ℝ} (hB : 0 ≤ B) (hC : C < π / 2)
    (hgap : B + π / 6 ≤ C) : 4 * sin B * cos C ≤ 1 := by
  have hs : 0 ≤ sin B := Real.sin_nonneg_of_nonneg_of_le_pi hB (by linarith [Real.pi_pos])
  have hc : cos C ≤ cos (B + π / 6) :=
    Real.cos_le_cos_of_nonneg_of_le_pi (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos]) hgap
  have hm := mul_le_mul_of_nonneg_left hc hs
  have ha := Real.sin_add B (B + π / 6)
  have hb := Real.sin_sub (B + π / 6) B
  rw [show B + π / 6 - B = π / 6 by ring, Real.sin_pi_div_six] at hb
  nlinarith [Real.sin_le_one (B + (B + π / 6))]

variable {V E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MetricSpace E] [NormedAddTorsor V E] [Fact (Module.finrank ℝ V = 2)]

/-- IMO 2001, Problem 1. The vertices 0, 1, 2 are A, B, C.
The altitude foot is specified by strict betweenness and a right angle.
All angles are unoriented angles in radians. -/
theorem imo2001_p1_of_sbtw (t : Affine.Triangle ℝ E) (P : E)
    (hA : ∠ (t.points 1) (t.points 0) (t.points 2) < π / 2)
    (hC : ∠ (t.points 0) (t.points 2) (t.points 1) < π / 2)
    (hP : Sbtw ℝ (t.points 1) P (t.points 2))
    (hperp : ∠ (t.points 0) P (t.points 2) = π / 2)
    (hgap : ∠ (t.points 0) (t.points 1) (t.points 2) + π / 6 ≤
      ∠ (t.points 0) (t.points 2) (t.points 1)) :
    ∠ (t.points 1) (t.points 0) (t.points 2) +
      ∠ (t.points 2) t.circumcenter P < π / 2 := by
  let A := t.points 0
  let B := t.points 1
  let C := t.points 2
  let O := t.circumcenter
  let R := t.circumradius
  change ∠ B A C + ∠ C O P < π / 2
  change ∠ B A C < π / 2 at hA
  change ∠ A C B < π / 2 at hC
  change Sbtw ℝ B P C at hP
  change ∠ A P C = π / 2 at hperp
  change ∠ A B C + π / 6 ≤ ∠ A C B at hgap
  have hAB : A ≠ B := t.independent.injective.ne (by decide : (0 : Fin 3) ≠ 1)
  have hAC : A ≠ C := t.independent.injective.ne (by decide : (0 : Fin 3) ≠ 2)
  have hnc : ¬ Collinear ℝ ({A, B, C} : Set E) :=
    (affineIndependent_iff_not_collinear_of_ne
      (by decide : (0 : Fin 3) ≠ 1) (by decide : (0 : Fin 3) ≠ 2)
      (by decide : (1 : Fin 3) ≠ 2)).mp t.independent
  have hsinB : 0 < sin (∠ A B C) := sin_pos_of_not_collinear hnc
  have hR : 0 < R := t.circumradius_pos
  have hOC : dist O C = R := by
    simpa only [dist_comm] using t.dist_circumcenter_eq_circumradius 2
  have hOB : dist O B = R := by
    simpa only [dist_comm] using t.dist_circumcenter_eq_circumradius 1
  have hCO : C ≠ O := by
    intro h
    have : dist O C = 0 := by rw [h]; exact dist_self O
    linarith
  have hBO : B ≠ O := by
    intro h
    have : dist O B = 0 := by rw [h]; exact dist_self O
    linarith
  have hPC : ∠ P C A = ∠ A C B := by
    rw [angle_comm]
    exact hP.symm.angle_eq_right A
  have hproj : cos (∠ A C B) * dist A C = dist P C := by
    have h := cos_angle_mul_dist_of_angle_eq_pi_div_two hperp
    rw [hPC, dist_comm C P] at h
    exact h
  have hsine : dist A C = 2 * R * sin (∠ A B C) := by
    have h := t.dist_div_sin_angle_eq_two_mul_circumradius
      (by decide : (0 : Fin 3) ≠ 1) (by decide : (0 : Fin 3) ≠ 2)
      (by decide : (1 : Fin 3) ≠ 2)
    exact (div_eq_iff (ne_of_gt hsinB)).mp h
  have hsmall : 2 * dist P C ≤ R := by
    have ht := trig_bound (angle_nonneg A B C) hC hgap
    have hm := mul_le_mul_of_nonneg_left ht hR.le
    rw [hsine] at hproj
    nlinarith [hproj]
  have hcenter : ∠ B O C = 2 * ∠ B A C := by
    exact Sphere.angle_center_eq_two_mul_angle_of_two_mul_angle_le_pi
      (t.mem_circumsphere 1) (t.mem_circumsphere 0) (t.mem_circumsphere 2)
      hAB hAC (by linarith)
  have hiso : ∠ O B C = ∠ O C B := angle_eq_angle_of_dist_eq (hOB.trans hOC.symm)
  have hsum := angle_add_angle_add_angle_eq_pi C hBO
  have hcomplement : ∠ P C O = π / 2 - ∠ B A C := by
    have hpco : ∠ P C O = ∠ B C O := hP.symm.angle_eq_left O
    rw [hpco]
    rw [angle_comm C O B, angle_comm B C O] at hsum
    rw [angle_comm B C O]
    linarith
  have hapos : 0 < ∠ B A C := by
    apply angle_pos_of_not_collinear
    simpa only [Set.insert_comm] using hnc
  have hpcopos : 0 < ∠ P C O := by rw [hcomplement]; linarith
  have hpcolt : ∠ P C O < π / 2 := by rw [hcomplement]; linarith
  have hnPCO : ¬ Collinear ℝ ({P, C, O} : Set E) := by
    intro hcol
    rcases collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi.mp hcol with h | h | h | h
    · exact hP.ne_right h
    · exact hCO h.symm
    · linarith
    · linarith [Real.pi_pos]
  have hnCPO : ¬ Collinear ℝ ({C, P, O} : Set E) := by
    simpa only [Set.insert_comm] using hnPCO
  have hstrict : dist C O < dist C P + dist P O := by
    apply dist_lt_dist_add_dist_iff.mpr
    intro h
    exact hnCPO h.collinear
  have hside : dist P C < dist P O := by
    rw [dist_comm C O, dist_comm C P, hOC] at hstrict
    linarith
  have hangle : ∠ P O C < ∠ P C O := (angle_lt_iff_dist_lt hnPCO).mpr hside
  rw [angle_comm C O P]
  linarith

omit [Fact (Module.finrank ℝ V = 2)] in
/-- The altitude foot of an acute triangle lies strictly inside the opposite side. -/
lemma altitude_sbtw {A B C P : E} (hBC : B ≠ C)
    (hcol : Collinear ℝ ({B, P, C} : Set E))
    (hB : ∠ A B C < π / 2) (hC : ∠ A C B < π / 2)
    (hpB : ∠ A P B = π / 2) (hpC : ∠ A P C = π / 2) :
    Sbtw ℝ B P C := by
  have hPB : P ≠ B := by intro h; subst P; linarith
  have hPC : P ≠ C := by intro h; subst P; linarith
  rcases hcol.wbtw_or_wbtw_or_wbtw with h | h | h
  · exact ⟨h, hPB, hPC⟩
  · have hs : Sbtw ℝ P C B := ⟨h, hPC.symm, hBC.symm⟩
    have hadd := angle_add_angle_eq_pi_of_angle_eq_pi A hs.angle₁₂₃_eq_pi
    have hlt := angle_lt_pi_div_two_of_angle_eq_pi_div_two hpC hPC.symm
    rw [angle_comm P C A] at hlt
    linarith
  · have hs : Sbtw ℝ C B P := ⟨h, hBC, hPB.symm⟩
    have hadd := angle_add_angle_eq_pi_of_angle_eq_pi A hs.angle₁₂₃_eq_pi
    have hlt := angle_lt_pi_div_two_of_angle_eq_pi_div_two hpB hPB.symm
    rw [angle_comm P B A] at hlt
    linarith

/-- The orthogonal projection of A onto the line BC. -/
noncomputable def altitudeFoot (t : Affine.Triangle ℝ E) : E :=
  orthogonalProjection (line[ℝ, t.points 1, t.points 2]) (t.points 0)

/-- IMO 2001, Problem 1, with the altitude foot and circumcenter constructed by mathlib. -/
theorem imo2001_p1 (t : Affine.Triangle ℝ E)
    (hA : ∠ (t.points 1) (t.points 0) (t.points 2) < π / 2)
    (hB : ∠ (t.points 0) (t.points 1) (t.points 2) < π / 2)
    (hC : ∠ (t.points 0) (t.points 2) (t.points 1) < π / 2)
    (hgap : ∠ (t.points 0) (t.points 1) (t.points 2) + π / 6 ≤
      ∠ (t.points 0) (t.points 2) (t.points 1)) :
    ∠ (t.points 1) (t.points 0) (t.points 2) +
      ∠ (t.points 2) t.circumcenter (altitudeFoot t) < π / 2 := by
  have hpB : ∠ (t.points 0) (altitudeFoot t) (t.points 1) = π / 2 :=
    angle_self_orthogonalProjection _ (left_mem_affineSpan_pair ℝ _ _)
  have hpC : ∠ (t.points 0) (altitudeFoot t) (t.points 2) = π / 2 :=
    angle_self_orthogonalProjection _ (right_mem_affineSpan_pair ℝ _ _)
  have hcol : Collinear ℝ ({t.points 1, altitudeFoot t, t.points 2} : Set E) := by
    have hmem : altitudeFoot t ∈ line[ℝ, t.points 1, t.points 2] :=
      orthogonalProjection_mem _
    have h := collinear_insert_of_mem_affineSpan_pair hmem
    simpa only [Set.insert_comm] using h
  exact imo2001_p1_of_sbtw t (altitudeFoot t) hA hC
    (altitude_sbtw (t.independent.injective.ne (by decide : (1 : Fin 3) ≠ 2))
      hcol hB hC hpB hpC) hpC hgap

end IMO2001P1
