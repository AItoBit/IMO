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
# IMO 1975, Problem 3

On the sides of an arbitrary triangle `ABC`, triangles `ABR`, `BCP`, `CAQ` are constructed
externally with `∠CBP = ∠CAQ = 45°`, `∠BCP = ∠ACQ = 30°`, `∠ABR = ∠BAR = 15°`.
Prove that `∠QRP = 90°` and `QR = RP`.

The plane is modelled as `ℂ`.  Directed angles are used, which encodes at the same time the
size of each of the given angles and the fact that the auxiliary triangles are erected on the
outside of `ABC`; the triangle `ABC` is assumed to be positively oriented, which is the
hypothesis `horient` below (it also encodes the nondegeneracy of the triangle `ABC`).  The
statement that the ray from `X` towards `Z` is obtained from the ray from `X` towards `Y` by
the rotation through the angle `θ` is written as `∃ t : ℝ, 0 < t ∧ Z - X = t * rot θ * (Y - X)`,
where `rot θ` denotes the rotation by `θ`.
-/

namespace IMO1975Q3

open Complex Real

/-- Multiplication by `rot θ` is the counterclockwise rotation of the plane `ℂ` by `θ`. -/
noncomputable def rot (θ : ℝ) : ℂ := Complex.exp ((θ : ℂ) * Complex.I)

lemma rot_eq (θ : ℝ) : rot θ = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I := by
  simp [rot, Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]

/-! ### Trigonometric values at `π / 12` -/

lemma cos_pi_div_twelve : Real.cos (π / 12) = Real.sqrt 2 * (Real.sqrt 3 + 1) / 4 := by
  have h : π / 12 = π / 3 - π / 4 := by ring
  rw [h, Real.cos_sub, Real.cos_pi_div_three, Real.cos_pi_div_four, Real.sin_pi_div_three,
    Real.sin_pi_div_four]
  ring

lemma sin_pi_div_twelve : Real.sin (π / 12) = Real.sqrt 2 * (Real.sqrt 3 - 1) / 4 := by
  have h : π / 12 = π / 3 - π / 4 := by ring
  rw [h, Real.sin_sub, Real.cos_pi_div_three, Real.cos_pi_div_four, Real.sin_pi_div_three,
    Real.sin_pi_div_four]
  ring

lemma sqrt2C : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
  exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) (Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2))

lemma sqrt3C : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
  exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) (Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3))

/-! ### The three similarity coefficients -/

/-- The coefficient of the apex `P`:  `P = B + pC * (C - B)`. -/
noncomputable def pC : ℂ := (((Real.sqrt 3 - 1) / 2 : ℝ) : ℂ) * (1 - Complex.I)

/-- The coefficient of the apex `Q`:  `Q = C + qC * (A - C)`. -/
noncomputable def qC : ℂ :=
  ((Real.sqrt 3 - 1 : ℝ) : ℂ) * (((Real.sqrt 3 : ℝ) : ℂ) - Complex.I) / 2

/-- The coefficient of the apex `R`:  `R = A + rC * (B - A)`. -/
noncomputable def rC : ℂ := (1 + ((Real.sqrt 3 - 2 : ℝ) : ℂ) * Complex.I) / 2

lemma coeff_i : 1 - qC = Complex.I * pC := by
  have s3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  simp only [pC, qC, Complex.ext_iff]
  constructor <;> simp <;> nlinarith [s3]

lemma coeff_ii : -rC = Complex.I * (1 - pC - rC) := by
  have s3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  simp only [pC, rC, Complex.ext_iff]
  constructor <;> simp <;> nlinarith [s3]

lemma coeff_deg : pC + rC - 1 = (1 - ((Real.sqrt 3 : ℝ) : ℂ) * Complex.I) / 2 * pC := by
  have s3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  simp only [pC, rC, Complex.ext_iff]
  constructor <;> simp <;> nlinarith [s3]

lemma pC_ne_zero : pC ≠ 0 := by
  have h1 : (1 : ℝ) < Real.sqrt 3 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3]
  intro h
  have h2 := congrArg Complex.re h
  simp [pC, Complex.mul_re] at h2
  linarith

/-! ### The coefficients do come from the prescribed rotations -/

lemma pC_eq : (((Real.sqrt 3 - 1) / Real.sqrt 2 : ℝ) : ℂ) * rot (-(π / 4)) = pC := by
  rw [rot_eq, pC, Real.cos_neg, Real.sin_neg, Real.cos_pi_div_four, Real.sin_pi_div_four]
  push_cast
  field_simp
  ring

lemma one_sub_pC_eq : ((Real.sqrt 3 - 1 : ℝ) : ℂ) * rot (π / 6) = 1 - pC := by
  rw [rot_eq, pC, Real.cos_pi_div_six, Real.sin_pi_div_six]
  push_cast
  linear_combination (1 / 2 : ℂ) * sqrt3C

lemma qC_eq : ((Real.sqrt 3 - 1 : ℝ) : ℂ) * rot (-(π / 6)) = qC := by
  rw [rot_eq, qC, Real.cos_neg, Real.sin_neg, Real.cos_pi_div_six, Real.sin_pi_div_six]
  push_cast
  ring

lemma one_sub_qC_eq : (((Real.sqrt 3 - 1) / Real.sqrt 2 : ℝ) : ℂ) * rot (π / 4) = 1 - qC := by
  rw [rot_eq, qC, Real.cos_pi_div_four, Real.sin_pi_div_four]
  push_cast
  field_simp
  linear_combination sqrt3C

lemma rC_eq : (((Real.sqrt 3 - 1) / Real.sqrt 2 : ℝ) : ℂ) * rot (-(π / 12)) = rC := by
  rw [rot_eq, rC, Real.cos_neg, Real.sin_neg, cos_pi_div_twelve, sin_pi_div_twelve]
  push_cast
  field_simp
  linear_combination (2 - 2 * Complex.I : ℂ) * sqrt3C

lemma one_sub_rC_eq : (((Real.sqrt 3 - 1) / Real.sqrt 2 : ℝ) : ℂ) * rot (π / 12) = 1 - rC := by
  rw [rot_eq, rC, cos_pi_div_twelve, sin_pi_div_twelve]
  push_cast
  field_simp
  linear_combination (2 + 2 * Complex.I : ℂ) * sqrt3C

/-! ### Determining the auxiliary points from the two angle conditions -/

/-- If `Z` is seen from `X` in the direction `u` relative to `Y - X`, and from `Y` in the
direction `v` relative to `X - Y`, then the two coefficients satisfy `t * u + s * v = 1`. -/
lemma coeff_sum {X Y Z : ℂ} {t s : ℝ} {u v : ℂ} (hXY : X ≠ Y)
    (h1 : Z - X = (t : ℂ) * u * (Y - X)) (h2 : Z - Y = (s : ℂ) * v * (X - Y)) :
    (t : ℂ) * u + (s : ℂ) * v = 1 := by
  have hne : Y - X ≠ 0 := sub_ne_zero.mpr (Ne.symm hXY)
  have h : (Y - X) * ((t : ℂ) * u + (s : ℂ) * v - 1) = 0 := by linear_combination h2 - h1
  rcases mul_eq_zero.mp h with h | h
  · exact absurd h hne
  · exact sub_eq_zero.mp h

lemma solve_P {t s : ℝ} (h : (t : ℂ) * rot (-(π / 4)) + (s : ℂ) * rot (π / 6) = 1) :
    (t : ℂ) * rot (-(π / 4)) = pC := by
  rw [rot_eq, rot_eq] at h
  rw [rot_eq, pC]
  rw [Real.cos_neg, Real.sin_neg, Real.cos_pi_div_four, Real.sin_pi_div_four] at h ⊢
  rw [Real.cos_pi_div_six, Real.sin_pi_div_six] at h
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp [Complex.add_re, Complex.add_im] at h1 h2
  have s3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have s3p : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hs : s = t * Real.sqrt 2 := by linear_combination 2 * h2
  have hX : (t * Real.sqrt 2) * (1 + Real.sqrt 3) = 2 := by
    linear_combination 2 * h1 - Real.sqrt 3 * hs
  have hz : (t * Real.sqrt 2 - (Real.sqrt 3 - 1)) * (1 + Real.sqrt 3) = 0 := by
    linear_combination hX - s3
  have key : t * Real.sqrt 2 = Real.sqrt 3 - 1 := by
    rcases mul_eq_zero.mp hz with hh | hh
    · linarith [sub_eq_zero.mp hh]
    · linarith
  have keyC : (t : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = ((Real.sqrt 3 : ℝ) : ℂ) - 1 := by
    exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) key
  push_cast
  linear_combination (1 - Complex.I) / 2 * keyC

lemma solve_Q {t s : ℝ} (h : (t : ℂ) * rot (-(π / 6)) + (s : ℂ) * rot (π / 4) = 1) :
    (t : ℂ) * rot (-(π / 6)) = qC := by
  rw [rot_eq, rot_eq] at h
  rw [rot_eq, qC]
  rw [Real.cos_neg, Real.sin_neg, Real.cos_pi_div_six, Real.sin_pi_div_six] at h ⊢
  rw [Real.cos_pi_div_four, Real.sin_pi_div_four] at h
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp [Complex.add_re, Complex.add_im] at h1 h2
  have s3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have s3p : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hd : t * (Real.sqrt 3 / 2) + t * (1 / 2) = 1 := by linear_combination h1 - h2
  have hz : (t - (Real.sqrt 3 - 1)) * (Real.sqrt 3 + 1) = 0 := by linear_combination 2 * hd - s3
  have key : t = Real.sqrt 3 - 1 := by
    rcases mul_eq_zero.mp hz with hh | hh
    · linarith [sub_eq_zero.mp hh]
    · linarith
  have keyC : (t : ℂ) = ((Real.sqrt 3 : ℝ) : ℂ) - 1 := by
    exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) key
  push_cast
  linear_combination (((Real.sqrt 3 : ℝ) : ℂ) - Complex.I) / 2 * keyC

lemma solve_R {t s : ℝ} (h : (t : ℂ) * rot (-(π / 12)) + (s : ℂ) * rot (π / 12) = 1) :
    (t : ℂ) * rot (-(π / 12)) = rC := by
  rw [rot_eq, rot_eq] at h
  rw [rot_eq, rC]
  rw [Real.cos_neg, Real.sin_neg, cos_pi_div_twelve, sin_pi_div_twelve] at h ⊢
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp [Complex.add_re, Complex.add_im] at h1 h2
  have s2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have s3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have s2p : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have s3p : (1 : ℝ) < Real.sqrt 3 := by nlinarith [s3, Real.sqrt_nonneg 3]
  have hst : s = t := by
    have hz : (s - t) * (Real.sqrt 2 * (Real.sqrt 3 - 1)) = 0 := by linear_combination 4 * h2
    rcases mul_eq_zero.mp hz with hh | hh
    · linarith [sub_eq_zero.mp hh]
    · nlinarith [hh, s2p, s3p]
  have hX : (t * Real.sqrt 2) * (1 + Real.sqrt 3) = 2 := by
    linear_combination 2 * h1 - (Real.sqrt 2 * (Real.sqrt 3 + 1) / 2) * hst
  have hz : (t * Real.sqrt 2 - (Real.sqrt 3 - 1)) * (1 + Real.sqrt 3) = 0 := by
    linear_combination hX - s3
  have key : t * Real.sqrt 2 = Real.sqrt 3 - 1 := by
    rcases mul_eq_zero.mp hz with hh | hh
    · linarith [sub_eq_zero.mp hh]
    · linarith
  have keyC : (t : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = ((Real.sqrt 3 : ℝ) : ℂ) - 1 := by
    exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) key
  push_cast
  linear_combination
    ((((Real.sqrt 3 : ℝ) : ℂ) + 1) / 4 - (((Real.sqrt 3 : ℝ) : ℂ) - 1) / 4 * Complex.I) * keyC +
      ((1 - Complex.I) / 4) * sqrt3C

/-! ### Nondegeneracy consequences of the orientation hypothesis -/

lemma ne_of_orient {A B C : ℂ} (h : 0 < ((C - A) / (B - A)).im) :
    A ≠ B ∧ B ≠ C ∧ C ≠ A := by
  have hBA : B - A ≠ 0 := by
    intro h0; rw [h0, div_zero] at h; simp at h
  have hCA : C - A ≠ 0 := by
    intro h0; rw [h0, zero_div] at h; simp at h
  refine ⟨fun hh => hBA (by simp [hh]), ?_, fun hh => hCA (by simp [hh])⟩
  intro hh
  rw [← hh, div_self hBA] at h
  simp at h

/-! ### The key identity -/

/-- With `P`, `Q`, `R` constructed as in the problem, `Q - R` is obtained from `P - R` by a
quarter turn; this contains both assertions of the problem. -/
theorem quarter_turn {A B C P Q R : ℂ} (horient : 0 < ((C - A) / (B - A)).im)
    (hPB : ∃ t : ℝ, 0 < t ∧ P - B = (t : ℂ) * rot (-(π / 4)) * (C - B))
    (hPC : ∃ t : ℝ, 0 < t ∧ P - C = (t : ℂ) * rot (π / 6) * (B - C))
    (hQC : ∃ t : ℝ, 0 < t ∧ Q - C = (t : ℂ) * rot (-(π / 6)) * (A - C))
    (hQA : ∃ t : ℝ, 0 < t ∧ Q - A = (t : ℂ) * rot (π / 4) * (C - A))
    (hRA : ∃ t : ℝ, 0 < t ∧ R - A = (t : ℂ) * rot (-(π / 12)) * (B - A))
    (hRB : ∃ t : ℝ, 0 < t ∧ R - B = (t : ℂ) * rot (π / 12) * (A - B)) :
    Q - R = Complex.I * (P - R) := by
  obtain ⟨hAB, hBC, hCA⟩ := ne_of_orient horient
  obtain ⟨tP, -, hP1⟩ := hPB
  obtain ⟨sP, -, hP2⟩ := hPC
  obtain ⟨tQ, -, hQ1⟩ := hQC
  obtain ⟨sQ, -, hQ2⟩ := hQA
  obtain ⟨tR, -, hR1⟩ := hRA
  obtain ⟨sR, -, hR2⟩ := hRB
  have hP : P - B = pC * (C - B) := by
    rw [hP1, solve_P (coeff_sum hBC hP1 hP2)]
  have hQ : Q - C = qC * (A - C) := by
    rw [hQ1, solve_Q (coeff_sum hCA hQ1 hQ2)]
  have hR : R - A = rC * (B - A) := by
    rw [hR1, solve_R (coeff_sum hAB hR1 hR2)]
  linear_combination hQ - (1 - Complex.I) * hR - Complex.I * hP + (C - A) * coeff_i +
    (B - A) * coeff_ii

/-- Under the hypotheses of the problem `R ≠ P`, so that the angle `∠QRP` is a genuine angle. -/
theorem R_ne_P {A B C P R : ℂ} (horient : 0 < ((C - A) / (B - A)).im)
    (hPB : ∃ t : ℝ, 0 < t ∧ P - B = (t : ℂ) * rot (-(π / 4)) * (C - B))
    (hPC : ∃ t : ℝ, 0 < t ∧ P - C = (t : ℂ) * rot (π / 6) * (B - C))
    (hRA : ∃ t : ℝ, 0 < t ∧ R - A = (t : ℂ) * rot (-(π / 12)) * (B - A))
    (hRB : ∃ t : ℝ, 0 < t ∧ R - B = (t : ℂ) * rot (π / 12) * (A - B)) :
    R ≠ P := by
  obtain ⟨hAB, hBC, hCA⟩ := ne_of_orient horient
  obtain ⟨tP, -, hP1⟩ := hPB
  obtain ⟨sP, -, hP2⟩ := hPC
  obtain ⟨tR, -, hR1⟩ := hRA
  obtain ⟨sR, -, hR2⟩ := hRB
  have hP : P - B = pC * (C - B) := by
    rw [hP1, solve_P (coeff_sum hBC hP1 hP2)]
  have hR : R - A = rC * (B - A) := by
    rw [hR1, solve_R (coeff_sum hAB hR1 hR2)]
  intro hRP
  have hBA : B - A ≠ 0 := sub_ne_zero.mpr (Ne.symm hAB)
  have hkey : pC * ((C - A) - (1 - ((Real.sqrt 3 : ℝ) : ℂ) * Complex.I) / 2 * (B - A)) = 0 := by
    linear_combination -hP + hR - hRP + (B - A) * coeff_deg
  have hCA' : C - A = (1 - ((Real.sqrt 3 : ℝ) : ℂ) * Complex.I) / 2 * (B - A) := by
    rcases mul_eq_zero.mp hkey with h | h
    · exact absurd h pC_ne_zero
    · exact sub_eq_zero.mp h
  have hq : (C - A) / (B - A) = (1 - ((Real.sqrt 3 : ℝ) : ℂ) * Complex.I) / 2 := by
    rw [hCA']; field_simp
  rw [hq] at horient
  have h3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  simp [Complex.sub_im] at horient
  linarith

/-! ### The theorem -/

/-- **IMO 1975, Problem 3.**  On the sides of an arbitrary (positively oriented) triangle
`ABC`, triangles `ABR`, `BCP`, `CAQ` are constructed externally with
`∠CBP = ∠CAQ = 45°`, `∠BCP = ∠ACQ = 30°` and `∠ABR = ∠BAR = 15°`.
Then `∠QRP = 90°` and `QR = RP` (and the points `R`, `P`, `Q` are pairwise distinct, so that
the angle `∠QRP` is a genuine angle). -/
theorem imo1975_q3 {A B C P Q R : ℂ} (horient : 0 < ((C - A) / (B - A)).im)
    (hPB : ∃ t : ℝ, 0 < t ∧ P - B = (t : ℂ) * rot (-(π / 4)) * (C - B))
    (hPC : ∃ t : ℝ, 0 < t ∧ P - C = (t : ℂ) * rot (π / 6) * (B - C))
    (hQC : ∃ t : ℝ, 0 < t ∧ Q - C = (t : ℂ) * rot (-(π / 6)) * (A - C))
    (hQA : ∃ t : ℝ, 0 < t ∧ Q - A = (t : ℂ) * rot (π / 4) * (C - A))
    (hRA : ∃ t : ℝ, 0 < t ∧ R - A = (t : ℂ) * rot (-(π / 12)) * (B - A))
    (hRB : ∃ t : ℝ, 0 < t ∧ R - B = (t : ℂ) * rot (π / 12) * (A - B)) :
    R ≠ P ∧ R ≠ Q ∧ EuclideanGeometry.angle Q R P = π / 2 ∧ dist Q R = dist R P := by
  have hkey : Q - R = Complex.I * (P - R) := quarter_turn horient hPB hPC hQC hQA hRA hRB
  have hRP : R ≠ P := R_ne_P horient hPB hPC hRA hRB
  refine ⟨hRP, ?_, ?_, ?_⟩
  · intro h
    apply hRP
    have h0 : Complex.I * (P - R) = 0 := by rw [← hkey, ← h]; ring
    rcases mul_eq_zero.mp h0 with h' | h'
    · exact absurd h' Complex.I_ne_zero
    · exact (sub_eq_zero.mp h').symm
  · rw [EuclideanGeometry.angle, vsub_eq_sub, vsub_eq_sub,
      ← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two, hkey]
    simp
    ring
  · rw [Complex.dist_eq, Complex.dist_eq, hkey, norm_mul, Complex.norm_I, one_mul, norm_sub_rev]

/-- The hypotheses of `imo1975_q3` are not vacuous:  for any three points `A`, `B`, `C` the
required points `P`, `Q`, `R` exist (and they are unique, by `solve_P`, `solve_Q`, `solve_R`). -/
theorem exists_config (A B C : ℂ) :
    ∃ P Q R : ℂ,
      (∃ t : ℝ, 0 < t ∧ P - B = (t : ℂ) * rot (-(π / 4)) * (C - B)) ∧
      (∃ t : ℝ, 0 < t ∧ P - C = (t : ℂ) * rot (π / 6) * (B - C)) ∧
      (∃ t : ℝ, 0 < t ∧ Q - C = (t : ℂ) * rot (-(π / 6)) * (A - C)) ∧
      (∃ t : ℝ, 0 < t ∧ Q - A = (t : ℂ) * rot (π / 4) * (C - A)) ∧
      (∃ t : ℝ, 0 < t ∧ R - A = (t : ℂ) * rot (-(π / 12)) * (B - A)) ∧
      (∃ t : ℝ, 0 < t ∧ R - B = (t : ℂ) * rot (π / 12) * (A - B)) := by
  have h1 : (1 : ℝ) < Real.sqrt 3 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3]
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have ht2 : (0 : ℝ) < Real.sqrt 3 - 1 := by linarith
  have ht1 : (0 : ℝ) < (Real.sqrt 3 - 1) / Real.sqrt 2 := div_pos ht2 h2
  refine ⟨B + pC * (C - B), C + qC * (A - C), A + rC * (B - A), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨_, ht1, by rw [pC_eq]; ring⟩
  · exact ⟨_, ht2, by rw [one_sub_pC_eq]; ring⟩
  · exact ⟨_, ht2, by rw [qC_eq]; ring⟩
  · exact ⟨_, ht1, by rw [one_sub_qC_eq]; ring⟩
  · exact ⟨_, ht1, by rw [rC_eq]; ring⟩
  · exact ⟨_, ht1, by rw [one_sub_rC_eq]; ring⟩

end IMO1975Q3
