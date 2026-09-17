import Mathlib

/-!
# IMO 2007, Problem 2

The final theorem is stated for arbitrary points of the Euclidean plane.
The parallelogram is nondegenerate. Circle membership, the interior of DC,
the line BC, and the line AF are expressed by their usual metric/affine
equations. The conclusion uses Mathlib's Euclidean angle, not a replacement
predicate for angle bisection.
-/

namespace IMO2007P2

open scoped InnerProductSpace RealInnerProductSpace

set_option maxHeartbeats 1000000

section InnerProduct

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

private lemma norm_combo_sub_sq (u v o : V) (a b : ℝ) :
    ‖a • u + b • v - o‖ ^ 2 =
      a ^ 2 * ‖u‖ ^ 2 + 2 * a * b * ⟪u, v⟫_ℝ + b ^ 2 * ‖v‖ ^ 2 -
        2 * a * ⟪u, o⟫_ℝ - 2 * b * ⟪v, o⟫_ℝ + ‖o‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
  rw [real_inner_comm v u, real_inner_comm o u, real_inner_comm o v]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

private lemma norm_combo_sq (u v : V) (a b : ℝ) :
    ‖a • u + b • v‖ ^ 2 =
      a ^ 2 * ‖u‖ ^ 2 + 2 * a * b * ⟪u, v⟫_ℝ + b ^ 2 * ‖v‖ ^ 2 := by
  simpa using norm_combo_sub_sq u v 0 a b

private lemma pair_coefficients (u v : V)
    (hi : LinearIndependent ℝ ![u, v]) (a b : ℝ)
    (h : a • u + b • v = 0) : a = 0 ∧ b = 0 := by
  have hh : ∑ i : Fin 2, (![a, b] i) • (![u, v] i) = 0 := by
    simpa [Fin.sum_univ_two] using h
  have hz := (Fintype.linearIndependent_iff.mp hi) ![a, b] hh
  exact ⟨by simpa using hz 0, by simpa using hz 1⟩

private lemma angle_of_equal_norm (x y : V) (h : ‖x‖ = ‖y‖) :
    InnerProductGeometry.angle x (x + y) =
      InnerProductGeometry.angle (x + y) y := by
  unfold InnerProductGeometry.angle
  congr 1
  simp only [inner_add_left, inner_add_right, real_inner_self_eq_norm_sq, h]
  congr 1 <;> ring

end InnerProduct

/-- The algebraic elimination at the heart of the proof. -/
private lemma algebra (U V W r z t s : ℝ)
    (hU : 0 < U) (hV : 0 < V) (ht : 0 < t) (ht1 : t < 1)
    (hst : s * t = 1)
    (hc : U * (r ^ 2 + r) + 2 * W * r * z + V * (z ^ 2 + z) = 0)
    (hf : 2 * (U * r + W * z) = U * (t - 1))
    (hg : 2 * (W * r + V * z) = V * (s - 1)) :
    V = t ^ 2 * U := by
  have ha : U * (t + 1) * r + V * (s + 1) * z = 0 := by
    linear_combination 2 * hc - r * hf - z * hg
  have hb : (t + 1) * (t * U * r + V * z) = 0 := by
    linear_combination t * ha - V * z * hst
  have hl : t * U * r + V * z = 0 :=
    (mul_eq_zero.mp hb).resolve_left (by linarith)
  have hr : r ≠ 0 := by
    intro hr
    have hz : z = 0 := by
      have hvz : V * z = 0 := by simpa [hr] using hl
      exact (mul_eq_zero.mp hvz).resolve_left (ne_of_gt hV)
    have hp : U * (t - 1) = 0 := by simpa [hr, hz] using hf.symm
    have ht' := (mul_eq_zero.mp hp).resolve_left (ne_of_gt hU)
    linarith
  have hp : (2 * U * r) * (V - t ^ 2 * U) = 0 := by
    linear_combination V * hf + U * t * hg -
      2 * (W + t * U) * hl + U * V * hst
  have hn : 2 * U * r ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (ne_of_gt hU)) hr
  have he := (mul_eq_zero.mp hp).resolve_left hn
  linarith

section Core

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- A translated vector form of the geometric argument. -/
private theorem core (u v o : V) (r z t s k R : ℝ)
    (hi : LinearIndependent ℝ ![u, v])
    (ht : 0 < t) (ht1 : t < 1)
    (hline : u + s • v = k • (v + t • u))
    (hB : ‖u - o‖ ^ 2 = R ^ 2)
    (hD : ‖v - o‖ ^ 2 = R ^ 2)
    (hC : ‖u + v - o‖ ^ 2 = R ^ 2)
    (hE : ‖(1 + r) • u + (1 + z) • v - o‖ ^ 2 = R ^ 2)
    (hEF : ‖((1 + r) • u + (1 + z) • v) - (v + t • u)‖ ^ 2 =
      ‖((1 + r) • u + (1 + z) • v) - (u + v)‖ ^ 2)
    (hEG : ‖((1 + r) • u + (1 + z) • v) - (u + s • v)‖ ^ 2 =
      ‖((1 + r) • u + (1 + z) • v) - (u + v)‖ ^ 2) :
    InnerProductGeometry.angle v (v + t • u) =
      InnerProductGeometry.angle (v + t • u) u := by
  have hzero : (1 - k * t) • u + (s - k) • v = 0 := by
    calc
      _ = (u + s • v) - k • (v + t • u) := by module
      _ = 0 := sub_eq_zero.mpr hline
  obtain ⟨hk, hs⟩ := pair_coefficients u v hi (1 - k * t) (s - k) hzero
  have hst : s * t = 1 := by
    have hsk : s = k := by linarith
    rw [hsk]
    linarith
  have hs1 : 1 - s ≠ 0 := by
    intro h
    have hs' : s = 1 := by linarith
    rw [hs'] at hst
    linarith
  have hu : u ≠ 0 := by simpa using hi.ne_zero (0 : Fin 2)
  have hv : v ≠ 0 := by simpa using hi.ne_zero (1 : Fin 2)
  have hU : 0 < ‖u‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hu)
  have hV : 0 < ‖v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hv)
  have hb : ‖u‖ ^ 2 - 2 * ⟪u, o⟫_ℝ + ‖o‖ ^ 2 = R ^ 2 := by
    calc
      _ = ‖u - o‖ ^ 2 := by simpa using (norm_combo_sub_sq u v o 1 0).symm
      _ = R ^ 2 := hB
  have hd : ‖v‖ ^ 2 - 2 * ⟪v, o⟫_ℝ + ‖o‖ ^ 2 = R ^ 2 := by
    calc
      _ = ‖v - o‖ ^ 2 := by simpa using (norm_combo_sub_sq u v o 0 1).symm
      _ = R ^ 2 := hD
  have hc : ‖u‖ ^ 2 + 2 * ⟪u, v⟫_ℝ + ‖v‖ ^ 2 -
      2 * ⟪u, o⟫_ℝ - 2 * ⟪v, o⟫_ℝ + ‖o‖ ^ 2 = R ^ 2 := by
    calc
      _ = ‖u + v - o‖ ^ 2 := by simpa using (norm_combo_sub_sq u v o 1 1).symm
      _ = R ^ 2 := hC
  rw [norm_combo_sub_sq] at hE
  have hcircle : ‖u‖ ^ 2 * (r ^ 2 + r) + 2 * ⟪u, v⟫_ℝ * r * z +
      ‖v‖ ^ 2 * (z ^ 2 + z) = 0 := by
    linear_combination hE + z * hb + r * hd - (1 + r + z) * hc
  have ec : ((1 + r) • u + (1 + z) • v) - (u + v) =
      r • u + z • v := by module
  have ef : ((1 + r) • u + (1 + z) • v) - (v + t • u) =
      (1 + r - t) • u + z • v := by module
  have eg : ((1 + r) • u + (1 + z) • v) - (u + s • v) =
      r • u + (1 + z - s) • v := by module
  rw [ef, ec, norm_combo_sq, norm_combo_sq] at hEF
  rw [eg, ec, norm_combo_sq, norm_combo_sq] at hEG
  have hfprod : (1 - t) *
      (‖u‖ ^ 2 * (1 - t + 2 * r) + 2 * ⟪u, v⟫_ℝ * z) = 0 := by
    nlinarith only [hEF]
  have hgprod : (1 - s) *
      (‖v‖ ^ 2 * (1 - s + 2 * z) + 2 * ⟪u, v⟫_ℝ * r) = 0 := by
    nlinarith only [hEG]
  have hfzero := (mul_eq_zero.mp hfprod).resolve_left (by linarith : 1 - t ≠ 0)
  have hgzero := (mul_eq_zero.mp hgprod).resolve_left hs1
  have hf : 2 * (‖u‖ ^ 2 * r + ⟪u, v⟫_ℝ * z) = ‖u‖ ^ 2 * (t - 1) := by
    nlinarith only [hfzero]
  have hg : 2 * (⟪u, v⟫_ℝ * r + ‖v‖ ^ 2 * z) = ‖v‖ ^ 2 * (s - 1) := by
    nlinarith only [hgzero]
  have hsq := algebra (‖u‖ ^ 2) (‖v‖ ^ 2) ⟪u, v⟫_ℝ r z t s
    hU hV ht ht1 hst hcircle hf hg
  have hnorm : ‖v‖ = t * ‖u‖ := by
    apply (sq_eq_sq₀ (norm_nonneg v) (mul_nonneg ht.le (norm_nonneg u))).mp
    nlinarith only [hsq]
  have hequal : ‖v‖ = ‖t • u‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    exact hnorm
  exact (angle_of_equal_norm v (t • u) hequal).trans
    (InnerProductGeometry.angle_smul_right_of_pos (v + t • u) u ht)

end Core

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/--
IMO 2007 P2: AF is the internal bisector of angle DAB.

* `hpar` and `hnd` say ABCD is a nondegenerate parallelogram.
* `hcyclic` places B,C,D,E on one circle.
* `hF` places F strictly inside DC.
* `hG` places G on the full line BC.
* `hline` places G on the full line through A and F.
* `hEF` and `hEG` express EF = EC and EG = EC.
-/
theorem imo2007_p2 (A B C D E F G : Plane)
    (hpar : C = B + D - A)
    (hnd : LinearIndependent ℝ ![B - A, D - A])
    (hcyclic : ∃ O : Plane, ∃ R : ℝ,
      dist B O = R ∧ dist C O = R ∧ dist D O = R ∧ dist E O = R)
    (hF : ∃ t : ℝ, 0 < t ∧ t < 1 ∧ F = D + t • (C - D))
    (hG : ∃ s : ℝ, G = B + s • (C - B))
    (hline : ∃ k : ℝ, G - A = k • (F - A))
    (hEF : dist E F = dist E C)
    (hEG : dist E G = dist E C) :
    EuclideanGeometry.angle D A F = EuclideanGeometry.angle F A B := by
  let u := B - A
  let v := D - A
  have hi : LinearIndependent ℝ ![u, v] := hnd
  have hspan : Submodule.span ℝ ({u, v} : Set Plane) = ⊤ := by
    simpa [Set.pair_comm] using hi.span_eq_top_of_card_eq_finrank (by simp)
  have hmem : E - A ∈ Submodule.span ℝ ({u, v} : Set Plane) := by
    rw [hspan]
    trivial
  obtain ⟨p, q, hpq⟩ := Submodule.mem_span_pair.mp hmem
  have he : E - A = (1 + (p - 1)) • u + (1 + (q - 1)) • v := by
    calc
      _ = p • u + q • v := hpq.symm
      _ = _ := by module
  obtain ⟨t, ht, ht1, hFt⟩ := hF
  obtain ⟨s, hGs⟩ := hG
  obtain ⟨k, hk⟩ := hline
  obtain ⟨O, R, hBO, hCO, hDO, hEO⟩ := hcyclic
  have hc : C - A = u + v := by
    rw [hpar]
    dsimp [u, v]
    abel
  have hf : F - A = v + t • u := by
    rw [hFt, hpar]
    dsimp [u, v]
    module
  have hg : G - A = u + s • v := by
    rw [hGs, hpar]
    dsimp [u, v]
    module
  rw [hg, hf] at hk
  have circle_eq (X : Plane) (hX : dist X O = R) :
      ‖(X - A) - (O - A)‖ ^ 2 = R ^ 2 := by
    have hh : (X - A) - (O - A) = X - O := by abel
    rw [hh]
    simpa only [dist_eq_norm] using congrArg (fun a : ℝ => a ^ 2) hX
  have distance_eq (X Y Z : Plane) (h : dist X Y = dist X Z) :
      ‖(X - A) - (Y - A)‖ ^ 2 = ‖(X - A) - (Z - A)‖ ^ 2 := by
    have hy : (X - A) - (Y - A) = X - Y := by abel
    have hz : (X - A) - (Z - A) = X - Z := by abel
    rw [hy, hz]
    simpa only [dist_eq_norm] using congrArg (fun a : ℝ => a ^ 2) h
  have hBC := circle_eq B hBO
  have hDC := circle_eq D hDO
  have hCC := circle_eq C hCO
  have hEC := circle_eq E hEO
  have hFC := distance_eq E F C hEF
  have hGC := distance_eq E G C hEG
  rw [hc] at hCC
  rw [he] at hEC
  rw [he, hf, hc] at hFC
  rw [he, hg, hc] at hGC
  have hresult := core u v (O - A) (p - 1) (q - 1) t s k R
    hi ht ht1 hk hBC hDC hCC hEC hFC hGC
  change InnerProductGeometry.angle v (F - A) = InnerProductGeometry.angle (F - A) u
  rw [hf]
  exact hresult

end IMO2007P2
