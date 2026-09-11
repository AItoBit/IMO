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
# IMO 1988 Problem 1

Consider two concentric circles with radii `R` and `r` (`R > r`) and centre `O`.
Fix `P` on the small circle and consider a variable chord `AP` of the small circle.
Points `B` and `C` lie on the large circle, `B`, `P`, `C` are collinear and `BC ⊥ AP`.

* (i)  For which values of `∠OPA` is `BC² + CA² + AB²` extremal?
       Answer: the quantity is **constant**, equal to `6R² + 2r²`, so it is extremal
       for every value of the angle.
* (ii) What are the possible positions of the midpoints `U` of `AB` and `V` of `AC`?
       Answer: they lie on the circle of radius `R/2` centred at the midpoint `M` of `OP`.
       In fact the locus is exactly that circle with its two points on the line `OP`
       removed: those two points would force the degenerate chord `A = P`.

Points are modelled as elements of the Euclidean plane `EuclideanSpace ℝ (Fin 2)`.
-/

namespace IMO1988Q1

open RealInnerProductSpace

/-- The Euclidean plane. -/
abbrev Pt := EuclideanSpace ℝ (Fin 2)

/-! ### Elementary two–dimensional facts -/

private lemma inner_coord (x y : Pt) : ⟪x, y⟫ = x 0 * y 0 + x 1 * y 1 := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_two]
  ring

private lemma norm_sq_coord (x : Pt) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_two]
  ring

private lemma algebraic_parseval (p0 p1 d0 d1 u0 u1 : ℝ) (h : d0 * u0 + d1 * u1 = 0)
    (hd : d0 ^ 2 + d1 ^ 2 ≠ 0) :
    (p0 ^ 2 + p1 ^ 2) * (d0 ^ 2 + d1 ^ 2) * (u0 ^ 2 + u1 ^ 2)
      = (p0 * d0 + p1 * d1) ^ 2 * (u0 ^ 2 + u1 ^ 2)
        + (p0 * u0 + p1 * u1) ^ 2 * (d0 ^ 2 + d1 ^ 2) := by
  have key : ((p0 ^ 2 + p1 ^ 2) * (d0 ^ 2 + d1 ^ 2) * (u0 ^ 2 + u1 ^ 2)
      - ((p0 * d0 + p1 * d1) ^ 2 * (u0 ^ 2 + u1 ^ 2)
        + (p0 * u0 + p1 * u1) ^ 2 * (d0 ^ 2 + d1 ^ 2))) * (d0 ^ 2 + d1 ^ 2) = 0 := by
    linear_combination ((p0 * d1 - p1 * d0) ^ 2 * (d0 * u0 + d1 * u1)
      - (d0 * u0 + d1 * u1) * (p0 * d0 + p1 * d1) ^ 2
      + 2 * (p0 * d0 + p1 * d1) * (p0 * d1 - p1 * d0) * (d0 * u1 - d1 * u0)) * h
  rcases mul_eq_zero.1 key with h1 | h1
  · linarith
  · exact absurd h1 hd

/-- Parseval's identity in the plane: if `d` and `u` are orthogonal and `d ≠ 0`,
then any vector decomposes along them. -/
private lemma parseval_two (x d u : Pt) (hdu : ⟪d, u⟫ = 0) (hd : d ≠ 0) :
    ‖x‖ ^ 2 * ‖d‖ ^ 2 * ‖u‖ ^ 2 = ⟪x, d⟫ ^ 2 * ‖u‖ ^ 2 + ⟪x, u⟫ ^ 2 * ‖d‖ ^ 2 := by
  have hd' : ‖d‖ ^ 2 ≠ 0 := by
    simpa using hd
  rw [norm_sq_coord x, norm_sq_coord d, norm_sq_coord u, inner_coord, inner_coord]
  refine algebraic_parseval _ _ _ _ _ _ ?_ ?_
  · rw [inner_coord] at hdu; linarith
  · rw [norm_sq_coord d] at hd'; exact hd'

private lemma norm_add_smul_sq (x y : Pt) (t : ℝ) :
    ‖x + t • y‖ ^ 2 = ‖x‖ ^ 2 + 2 * t * ⟪x, y⟫ + t ^ 2 * ‖y‖ ^ 2 := by
  rw [norm_add_sq_real, real_inner_smul_right, norm_smul]
  simp only [Real.norm_eq_abs, mul_pow, sq_abs]
  ring

/-- Norm of a linear combination of two orthogonal vectors. -/
private lemma norm_sq_orth_comb (d u : Pt) (h : ⟪d, u⟫ = 0) (a b : ℝ) :
    ‖a • d + b • u‖ ^ 2 = a ^ 2 * ‖d‖ ^ 2 + b ^ 2 * ‖u‖ ^ 2 := by
  rw [norm_add_sq_real, real_inner_smul_left, real_inner_smul_right, h, norm_smul, norm_smul]
  simp only [Real.norm_eq_abs, mul_pow, sq_abs]
  ring

/-! ### The configuration -/

/-- The hypotheses of the problem, packaged for reuse. -/
structure Config (R r : ℝ) (O A P B C : Pt) : Prop where
  /-- `A` lies on the small circle. -/
  hA : dist A O = r
  /-- `P` lies on the small circle. -/
  hP : dist P O = r
  /-- `B` lies on the large circle. -/
  hB : dist B O = R
  /-- `C` lies on the large circle. -/
  hC : dist C O = R
  /-- `AP` is a genuine chord of the small circle. -/
  hAP : A ≠ P
  /-- `B` and `C` are distinct, so they span the line `BC`. -/
  hBC : B ≠ C
  /-- `B`, `P`, `C` are collinear. -/
  hcol : Collinear ℝ ({B, P, C} : Set Pt)
  /-- `BC` is perpendicular to `AP`. -/
  hperp : ⟪C - B, A - P⟫ = 0

namespace Config

variable {R r : ℝ} {O A P B C : Pt}

/-- `P` lies on the line `BC`: `P - B` is a multiple of `C - B`. -/
lemma exists_param (h : Config R r O A P B C) : ∃ s : ℝ, P - B = s • (C - B) := by
  obtain ⟨v, hv⟩ := (collinear_iff_of_mem (Set.mem_insert B {P, C})).1 h.hcol
  obtain ⟨sp, hsp⟩ := hv P (by simp)
  obtain ⟨sc, hsc⟩ := hv C (by simp)
  have hCB : C - B = sc • v := by
    rw [hsc]; simp
  have hPB : P - B = sp • v := by
    rw [hsp]; simp
  have hsc0 : sc ≠ 0 := by
    rintro rfl
    apply h.hBC
    have : C - B = 0 := by rw [hCB]; simp
    have := sub_eq_zero.1 this
    exact this.symm
  refine ⟨sp / sc, ?_⟩
  rw [hPB, hCB, smul_smul]
  congr 1
  field_simp

end Config

/-- The hypotheses are satisfiable: an explicit configuration with `r = 1`, `R = 2`. -/
theorem config_example :
    Config 2 1 (!₂[0, 0] : Pt) (!₂[-1, 0] : Pt) (!₂[1, 0] : Pt) (!₂[1, Real.sqrt 3] : Pt)
      (!₂[1, -Real.sqrt 3] : Pt) where
  hA := by
    rw [EuclideanSpace.dist_eq]
    simp [Fin.sum_univ_two]
  hP := by
    rw [EuclideanSpace.dist_eq]
    simp [Fin.sum_univ_two]
  hB := by
    rw [EuclideanSpace.dist_eq]
    simp [Fin.sum_univ_two, Real.sq_sqrt]
    rw [show (1:ℝ) + 3 = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  hC := by
    rw [EuclideanSpace.dist_eq]
    simp [Fin.sum_univ_two, Real.sq_sqrt]
    rw [show (1:ℝ) + 3 = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  hAP := by
    intro h
    have h0 := congrArg (fun z : Pt => z 0) h
    norm_num at h0
  hBC := by
    intro h
    have h1 := congrArg (fun z : Pt => z 1) h
    simp at h1
    nlinarith [Real.sq_sqrt (by norm_num : (3:ℝ) ≥ 0), Real.sqrt_nonneg 3]
  hcol := by
    rw [collinear_iff_of_mem (Set.mem_insert_of_mem _ (Set.mem_insert _ _))]
    refine ⟨!₂[0, 1], ?_⟩
    rintro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, vadd_eq_add] at hq ⊢
    rcases hq with rfl | rfl | rfl
    · exact ⟨Real.sqrt 3, by ext i; fin_cases i <;> simp⟩
    · exact ⟨0, by ext i; fin_cases i <;> simp⟩
    · exact ⟨-Real.sqrt 3, by ext i; fin_cases i <;> simp⟩
  hperp := by simp [PiLp.inner_apply, Fin.sum_univ_two]

/-! ### Part (i) -/

/-- **IMO 1988, Problem 1 (i).**  In the above configuration the quantity
`BC² + CA² + AB²` is equal to `6R² + 2r²`; in particular it does not depend on the
position of `A`, hence it is extremal for every value of the angle `∠OPA`. -/
theorem sum_of_squares (R r : ℝ) (O A P B C : Pt) (h : Config R r O A P B C) :
    dist B C ^ 2 + dist C A ^ 2 + dist A B ^ 2 = 6 * R ^ 2 + 2 * r ^ 2 := by
  obtain ⟨s, hs⟩ := h.exists_param
  set d : Pt := C - B with hdef_d
  set u : Pt := A - P with hdef_u
  set p : Pt := P - O with hdef_p
  have hdu : ⟪d, u⟫ = 0 := h.hperp
  have hd0 : d ≠ 0 := sub_ne_zero.2 (Ne.symm h.hBC)
  have hu0 : u ≠ 0 := sub_ne_zero.2 h.hAP
  have hDpos : 0 < ‖d‖ ^ 2 := by positivity
  have hUpos : 0 < ‖u‖ ^ 2 := by positivity
  have hp2 : ‖p‖ ^ 2 = r ^ 2 := by rw [hdef_p, ← dist_eq_norm, h.hP]
  -- the position of `A`
  have hpu : ⟪p, u⟫ = -(‖u‖ ^ 2) / 2 := by
    have e1 : ‖p + (1 : ℝ) • u‖ ^ 2 = r ^ 2 := by
      have hAO : p + (1 : ℝ) • u = A - O := by rw [hdef_p, hdef_u]; module
      rw [hAO, ← dist_eq_norm, h.hA]
    rw [norm_add_smul_sq] at e1
    linarith
  -- the two intersection points of the line with the large circle
  have hBO : ‖p + (-s) • d‖ ^ 2 = R ^ 2 := by
    have : p + (-s) • d = B - O := by rw [hdef_p, hdef_d]; linear_combination (norm := module) hs
    rw [this, ← dist_eq_norm, h.hB]
  have hCO : ‖p + (1 - s) • d‖ ^ 2 = R ^ 2 := by
    have : p + (1 - s) • d = C - O := by rw [hdef_p, hdef_d]; linear_combination (norm := module) hs
    rw [this, ← dist_eq_norm, h.hC]
  rw [norm_add_smul_sq] at hBO hCO
  rw [hp2] at hBO hCO
  -- the foot of the perpendicular from `O`
  have hE : ⟪p, d⟫ = (2 * s - 1) * ‖d‖ ^ 2 / 2 := by linear_combination (-1/2 : ℝ) * hBO + (1/2 : ℝ) * hCO
  -- Pythagoras in the rectangle `O`, foot on `AP`, `P`, foot on `BC`
  have hpar := parseval_two p d u hdu hd0
  rw [hp2, hpu, hE] at hpar
  have hU : ‖u‖ ^ 2 = 4 * r ^ 2 - (2 * s - 1) ^ 2 * ‖d‖ ^ 2 := by
    have key : (‖u‖ ^ 2 - (4 * r ^ 2 - (2 * s - 1) ^ 2 * ‖d‖ ^ 2)) * (‖d‖ ^ 2 * ‖u‖ ^ 2) = 0 := by
      linear_combination (-4 : ℝ) * hpar
    have hne : ‖d‖ ^ 2 * ‖u‖ ^ 2 ≠ 0 := by positivity
    rcases mul_eq_zero.1 key with h1 | h1
    · linarith
    · exact absurd h1 hne
  have hR : R ^ 2 = r ^ 2 + (s - s ^ 2) * ‖d‖ ^ 2 := by
    rw [hE] at hBO; linear_combination -hBO
  -- the three squared distances
  have e1 : dist B C ^ 2 = ‖d‖ ^ 2 := by
    rw [dist_eq_norm, hdef_d, ← norm_neg (B - C)]
    congr 2
    abel
  have hCA : C - A = (1 - s) • d + (-1 : ℝ) • u := by
    rw [hdef_d, hdef_u]
    linear_combination (norm := module) -hs
  have hAB : A - B = s • d + (1 : ℝ) • u := by
    rw [hdef_d, hdef_u]
    linear_combination (norm := module) hs
  have e2 : dist C A ^ 2 = (1 - s) ^ 2 * ‖d‖ ^ 2 + (-1 : ℝ) ^ 2 * ‖u‖ ^ 2 := by
    rw [dist_eq_norm, hCA, norm_sq_orth_comb d u hdu]
  have e3 : dist A B ^ 2 = s ^ 2 * ‖d‖ ^ 2 + (1 : ℝ) ^ 2 * ‖u‖ ^ 2 := by
    rw [dist_eq_norm, hAB, norm_sq_orth_comb d u hdu]
  rw [e1, e2, e3]
  linear_combination (2 : ℝ) * hU - (6 : ℝ) * hR

/-- **IMO 1988, Problem 1 (i).**  The quantity `BC² + CA² + AB²` takes the same value for any
two admissible positions of the chord `AP`: it is constant, hence extremal for every value
of the angle `∠OPA`. -/
theorem sum_of_squares_const (R r : ℝ) (O P A₁ B₁ C₁ A₂ B₂ C₂ : Pt)
    (h₁ : Config R r O A₁ P B₁ C₁) (h₂ : Config R r O A₂ P B₂ C₂) :
    dist B₁ C₁ ^ 2 + dist C₁ A₁ ^ 2 + dist A₁ B₁ ^ 2
      = dist B₂ C₂ ^ 2 + dist C₂ A₂ ^ 2 + dist A₂ B₂ ^ 2 := by
  rw [sum_of_squares R r O A₁ P B₁ C₁ h₁, sum_of_squares R r O A₂ P B₂ C₂ h₂]

/-! ### Part (ii) -/

/-- Key computation for part (ii): if `X` lies on the large circle and on the line through
`P` with direction `d ⊥ AP`, then the midpoint of `AX` is at distance `R/2` from the
midpoint of `OP`. -/
private lemma midpoint_dist_aux {R r : ℝ} {O A P X d : Pt} {t : ℝ}
    (hdu : ⟪d, A - P⟫ = 0) (hA : dist A O = r) (hP : dist P O = r) (hX : dist X O = R)
    (hXO : X - O = (P - O) + t • d) :
    dist (midpoint ℝ A X) (midpoint ℝ O P) = R / 2 := by
  have hR0 : 0 ≤ R := hX ▸ dist_nonneg
  have hpu : 2 * ⟪P - O, A - P⟫ = -‖A - P‖ ^ 2 := by
    have e1 : ‖(P - O) + (1 : ℝ) • (A - P)‖ ^ 2 = r ^ 2 := by
      have : (P - O) + (1 : ℝ) • (A - P) = A - O := by module
      rw [this, ← dist_eq_norm, hA]
    have e2 : ‖P - O‖ ^ 2 = r ^ 2 := by rw [← dist_eq_norm, hP]
    rw [norm_add_smul_sq] at e1
    linarith
  have hXu : ⟪X - O, A - P⟫ = ⟪P - O, A - P⟫ := by
    rw [hXO, inner_add_left, real_inner_smul_left, hdu]
    ring
  have hnorm : ‖(X - O) + (1 : ℝ) • (A - P)‖ ^ 2 = R ^ 2 := by
    rw [norm_add_smul_sq, hXu, ← dist_eq_norm, hX]
    linarith
  have hval : ‖(X - O) + (1 : ℝ) • (A - P)‖ = R := by
    have h0 : 0 ≤ ‖(X - O) + (1 : ℝ) • (A - P)‖ := norm_nonneg _
    nlinarith [hnorm, h0, hR0]
  have hmid : midpoint ℝ A X - midpoint ℝ O P = (2⁻¹ : ℝ) • ((X - O) + (1 : ℝ) • (A - P)) := by
    simp only [midpoint_eq_smul_add, invOf_eq_inv]
    module
  rw [dist_eq_norm, hmid, norm_smul, hval]
  simp only [Real.norm_eq_abs]
  rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ (2⁻¹ : ℝ))]
  ring

/-- **IMO 1988, Problem 1 (ii).**  The midpoint `U` of `AB` lies on the circle with
centre the midpoint of `OP` and radius `R/2`. -/
theorem dist_midpoint_AB (R r : ℝ) (O A P B C : Pt) (h : Config R r O A P B C) :
    dist (midpoint ℝ A B) (midpoint ℝ O P) = R / 2 := by
  obtain ⟨s, hs⟩ := h.exists_param
  refine midpoint_dist_aux (d := C - B) (t := -s) h.hperp h.hA h.hP h.hB ?_
  linear_combination (norm := module) -hs

/-- **IMO 1988, Problem 1 (ii).**  The midpoint `V` of `AC` lies on the circle with
centre the midpoint of `OP` and radius `R/2`. -/
theorem dist_midpoint_AC (R r : ℝ) (O A P B C : Pt) (h : Config R r O A P B C) :
    dist (midpoint ℝ A C) (midpoint ℝ O P) = R / 2 := by
  obtain ⟨s, hs⟩ := h.exists_param
  refine midpoint_dist_aux (d := C - B) (t := 1 - s) h.hperp h.hA h.hP h.hC ?_
  linear_combination (norm := module) -hs

/-! ### Part (ii): the exact locus

The two points where the circle of radius `R/2` centred at the midpoint of `OP` meets the
line `OP` are *not* attained (they would force `A = P`, i.e. a degenerate chord); every
other point of that circle is attained. -/

/-- Rotation by a right angle in the plane. -/
private noncomputable def rot (x : Pt) : Pt := !₂[-(x 1), x 0]

private lemma inner_rot_self (x : Pt) : ⟪x, rot x⟫ = 0 := by
  simp [rot, PiLp.inner_apply, Fin.sum_univ_two]
  ring

private lemma norm_rot (x : Pt) : ‖rot x‖ = ‖x‖ := by
  simp [rot, EuclideanSpace.norm_eq, Fin.sum_univ_two]
  ring_nf

/-- In the plane, a vector orthogonal to `rot x` is parallel to `x`. -/
private lemma exists_smul_of_inner_rot {p x : Pt} (hp : p ≠ 0) (h : ⟪p, rot x⟫ = 0) :
    ∃ μ : ℝ, x = μ • p := by
  have hp2 : (p 0) ^ 2 + (p 1) ^ 2 ≠ 0 := by
    intro hc
    apply hp
    have h0 : p 0 = 0 := by nlinarith [sq_nonneg (p 0), sq_nonneg (p 1)]
    have h1 : p 1 = 0 := by nlinarith [sq_nonneg (p 0), sq_nonneg (p 1)]
    ext i
    fin_cases i <;> simpa using ‹_›
  have h' : p 1 * x 0 - p 0 * x 1 = 0 := by
    simp only [rot, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_two] at h
    simp at h
    linarith
  refine ⟨(x 0 * p 0 + x 1 * p 1) / ((p 0) ^ 2 + (p 1) ^ 2), ?_⟩
  ext i
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, PiLp.smul_apply, smul_eq_mul]
    field_simp
    linear_combination (p 1) * h'
  · simp only [Fin.mk_one, Fin.isValue, PiLp.smul_apply, smul_eq_mul]
    field_simp
    linear_combination (-(p 0)) * h'

private lemma dist_eq_of_sq {X Y : Pt} {c : ℝ} (hc : 0 ≤ c) (h : ‖X - Y‖ ^ 2 = c ^ 2) :
    dist X Y = c := by
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (X - Y)]

/-- The midpoint of `AB` never lands on one of the two points where the circle of radius
`R/2` about the midpoint of `OP` meets the line `OP`. -/
theorem midpoint_ne_on_axis {R r : ℝ} (hr : 0 < r) (hrR : r < R) {O A P B : Pt}
    (hA : dist A O = r) (hP : dist P O = r) (hB : dist B O = R) (hAP : A ≠ P) {e : ℝ}
    (he : e = 1 ∨ e = -1) :
    midpoint ℝ A B ≠ midpoint ℝ O P + (e * R / (2 * r)) • (P - O) := by
  intro hEq
  have he2 : e ^ 2 = 1 := by rcases he with rfl | rfl <;> norm_num
  have hsum : r + e * R ≠ 0 := by
    rcases he with rfl | rfl
    · simp only [one_mul]; intro hc; linarith
    · simp only [neg_mul, one_mul]; intro hc; linarith
  set t : ℝ := 1 + 2 * (e * R / (2 * r)) with ht_def
  have hk : t * r = r + e * R := by rw [ht_def]; field_simp
  have ht : t ≠ 0 := by
    intro hc
    rw [hc, zero_mul] at hk
    exact hsum hk.symm
  have hpn : ‖P - O‖ = r := by rw [← dist_eq_norm, hP]
  have han : ‖(-1 : ℝ) • (A - O)‖ = r := by
    have : (-1 : ℝ) • (A - O) = O - A := by module
    rw [this, ← dist_eq_norm, dist_comm, hA]
  set q : ℝ := ⟪A - O, P - O⟫ with hq_def
  have hBO : B - O = ((-1 : ℝ) • (A - O)) + t • (P - O) := by
    have h1 : (2⁻¹ : ℝ) • (A + B) = (2⁻¹ : ℝ) • (O + P) + (e * R / (2 * r)) • (P - O) := by
      simpa [midpoint_eq_smul_add, invOf_eq_inv] using hEq
    rw [ht_def]
    linear_combination (norm := module) (2 : ℝ) • h1
  have e1 : ‖B - O‖ ^ 2 = R ^ 2 := by rw [← dist_eq_norm, hB]
  rw [hBO, norm_add_smul_sq, han, hpn] at e1
  have hinner : ⟪(-1 : ℝ) • (A - O), P - O⟫ = -q := by
    rw [real_inner_smul_left, hq_def]; ring
  rw [hinner] at e1
  have h1 : t ^ 2 * r ^ 2 = r ^ 2 + 2 * e * r * R + R ^ 2 := by
    have h2 : (t * r) ^ 2 = (r + e * R) ^ 2 := by rw [hk]
    linear_combination h2 + R ^ 2 * he2
  have hq : q = r ^ 2 := by
    have h3 : t * q = t * r ^ 2 := by
      have h4 : t * r ^ 2 = r ^ 2 + e * r * R := by
        have : t * r ^ 2 = (t * r) * r := by ring
        rw [this, hk]; ring
      linarith [e1, h1, h4]
    exact mul_left_cancel₀ ht h3
  apply hAP
  have hAPzero : ‖(A - O) + (-1 : ℝ) • (P - O)‖ ^ 2 = 0 := by
    rw [norm_add_smul_sq, hpn, ← hq_def, hq]
    have : ‖A - O‖ = r := by rw [← dist_eq_norm, hA]
    rw [this]; ring
  have : (A - O) + (-1 : ℝ) • (P - O) = A - P := by module
  rw [this] at hAPzero
  have : A - P = 0 := by
    have := norm_nonneg (A - P)
    have h5 : ‖A - P‖ = 0 := by nlinarith
    exact norm_eq_zero.1 h5
  exact sub_eq_zero.1 this

/-- Every point of the circle of radius `R/2` about the midpoint of `OP`, apart from the two
points on the line `OP`, is the midpoint of `AB` for a suitable admissible configuration. -/
theorem exists_config_midpoint {R r : ℝ} (hr : 0 < r) (hrR : r < R) {O P X : Pt}
    (hP : dist P O = r) (hX : dist X (midpoint ℝ O P) = R / 2)
    (hne1 : X ≠ midpoint ℝ O P + (1 * R / (2 * r)) • (P - O))
    (hne2 : X ≠ midpoint ℝ O P + (-1 * R / (2 * r)) • (P - O)) :
    ∃ A B C : Pt, Config R r O A P B C ∧ X = midpoint ℝ A B := by
  have hR : 0 < R := lt_trans hr hrR
  set p : Pt := P - O with hp_def
  set x : Pt := X - O with hx_def
  have hpn : ‖p‖ = r := by rw [hp_def, ← dist_eq_norm, hP]
  have hp0 : p ≠ 0 := by
    intro hc; rw [hc, norm_zero] at hpn; exact absurd hpn.symm (ne_of_gt hr)
  set y : Pt := (2 : ℝ) • x + (-1 : ℝ) • p with hy_def
  have hyn : ‖y‖ = R := by
    have h1 : X - midpoint ℝ O P = (2⁻¹ : ℝ) • y := by
      rw [hy_def, hx_def, hp_def]
      simp only [midpoint_eq_smul_add, invOf_eq_inv]
      module
    have h2 : ‖X - midpoint ℝ O P‖ = R / 2 := by rw [← dist_eq_norm, hX]
    rw [h1, norm_smul] at h2
    simp only [Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0:ℝ) ≤ (2⁻¹:ℝ))] at h2
    linarith
  have hx0 : x ≠ 0 := by
    intro hc
    rw [hc] at hy_def
    have : ‖y‖ = r := by rw [hy_def]; simp [hpn]
    rw [hyn] at this; linarith
  set v : Pt := rot x with hv_def
  have hv0 : v ≠ 0 := by
    intro hc
    apply hx0
    have : ‖x‖ = 0 := by rw [← norm_rot x, ← hv_def, hc, norm_zero]
    exact norm_eq_zero.1 this
  have hvn : (0:ℝ) < ‖v‖ ^ 2 := by positivity
  have hxv : ⟪x, v⟫ = 0 := inner_rot_self x
  have hpv : ⟪p, v⟫ ≠ 0 := by
    intro hc
    obtain ⟨μ, hμ⟩ := exists_smul_of_inner_rot hp0 hc
    have hyμ : y = (2 * μ - 1) • p := by rw [hy_def, hμ]; module
    have hn : |2 * μ - 1| * r = R := by
      rw [← hyn, hyμ, norm_smul, hpn]; simp [Real.norm_eq_abs]
    have hcases : (2 * μ - 1) * r = R ∨ (2 * μ - 1) * r = -R := by
      rcases abs_cases (2 * μ - 1) with ⟨h1, _⟩ | ⟨h1, _⟩
      · left; rw [h1] at hn; linarith
      · right; rw [h1] at hn; nlinarith
    have hXeq : X = midpoint ℝ O P + μ • p - (2⁻¹ : ℝ) • p := by
      rw [← hμ, hx_def, hp_def]
      simp only [midpoint_eq_smul_add, invOf_eq_inv]
      module
    rcases hcases with h1 | h1
    · apply hne1
      have hμ' : μ = 1 * R / (2 * r) + 2⁻¹ := by field_simp at h1 ⊢; linarith
      rw [hXeq, hμ']
      module
    · apply hne2
      have hμ' : μ = -1 * R / (2 * r) + 2⁻¹ := by field_simp at h1 ⊢; linarith
      rw [hXeq, hμ']
      module
  set τ : ℝ := -2 * ⟪p, v⟫ / ‖v‖ ^ 2 with hτ_def
  have hτ0 : τ ≠ 0 := by
    rw [hτ_def]
    exact div_ne_zero (by simpa using hpv) (ne_of_gt hvn)
  have hkey : 2 * τ * ⟪p, v⟫ + τ ^ 2 * ‖v‖ ^ 2 = 0 := by
    rw [hτ_def]; field_simp; ring
  have hτv : τ * ‖v‖ ^ 2 = -2 * ⟪p, v⟫ := by rw [hτ_def]; field_simp
  have hyv : ⟪y, v⟫ = -⟪p, v⟫ := by
    rw [hy_def, inner_add_left, real_inner_smul_left, real_inner_smul_left, hxv]; ring
  obtain ⟨A, hA_def⟩ : ∃ A : Pt, A = P + τ • v := ⟨_, rfl⟩
  obtain ⟨B, hB_def⟩ : ∃ B : Pt, B = X + (X - A) := ⟨_, rfl⟩
  have hAO : A - O = p + τ • v := by rw [hA_def, hp_def]; module
  have hdA : dist A O = r := by
    refine dist_eq_of_sq hr.le ?_
    rw [hAO, norm_add_smul_sq, hpn]
    linarith [hkey]
  have hBOv : B - O = y + (-τ) • v := by
    rw [hB_def, hA_def, hy_def, hx_def, hp_def]; module
  have hdB : dist B O = R := by
    refine dist_eq_of_sq hR.le ?_
    rw [hBOv, norm_add_smul_sq, hyn, hyv]
    linarith [hkey]
  obtain ⟨w, hw_def⟩ : ∃ w : Pt, w = B - P := ⟨_, rfl⟩
  have hw0 : w ≠ 0 := by
    intro hc
    rw [hc] at hw_def
    have hBP : B = P := (sub_eq_zero.1 hw_def.symm)
    rw [hBP, hP] at hdB
    linarith
  have hW : (0:ℝ) < ‖w‖ ^ 2 := by positivity
  have hpw2 : 2 * ⟪p, w⟫ = R ^ 2 - r ^ 2 - ‖w‖ ^ 2 := by
    have h1 : p + (1 : ℝ) • w = B - O := by rw [hw_def, hp_def]; module
    have h2 : ‖p + (1 : ℝ) • w‖ ^ 2 = R ^ 2 := by rw [h1, ← dist_eq_norm, hdB]
    rw [norm_add_smul_sq, hpn] at h2
    linarith
  obtain ⟨t2, ht2_def⟩ : ∃ t : ℝ, t = (r ^ 2 - R ^ 2) / ‖w‖ ^ 2 := ⟨_, rfl⟩
  have ht2neg : t2 < 0 := by
    rw [ht2_def]
    apply div_neg_of_neg_of_pos _ hW
    nlinarith
  obtain ⟨C, hC_def⟩ : ∃ C : Pt, C = P + t2 • w := ⟨_, rfl⟩
  have hCO : C - O = p + t2 • w := by rw [hC_def, hp_def]; module
  have htW : t2 * ‖w‖ ^ 2 = r ^ 2 - R ^ 2 := by rw [ht2_def]; field_simp
  have hdC : dist C O = R := by
    refine dist_eq_of_sq hR.le ?_
    rw [hCO, norm_add_smul_sq, hpn]
    linear_combination t2 * hpw2 + (t2 - 1) * htW
  have hwv : ⟪w, v⟫ = 0 := by
    have h1 : w = (y + (-τ) • v) + (-1 : ℝ) • p := by
      rw [hw_def, hp_def, ← hBOv]; module
    rw [h1, inner_add_left, real_inner_smul_left, inner_add_left, real_inner_smul_left, hyv,
      real_inner_self_eq_norm_sq]
    linarith [hτv]
  have hCB : C - B = (t2 - 1) • w := by
    have hBw : B = P + w := by rw [hw_def]; module
    rw [hC_def, hBw]; module
  refine ⟨A, B, C, ⟨hdA, hP, hdB, hdC, ?_, ?_, ?_, ?_⟩, ?_⟩
  · -- `A ≠ P`
    intro hc
    have : τ • v = 0 := by
      have : A - P = τ • v := by rw [hA_def]; module
      rw [← this, hc, sub_self]
    rcases smul_eq_zero.1 this with h | h
    · exact hτ0 h
    · exact hv0 h
  · -- `B ≠ C`
    intro hc
    rw [← hc, sub_self] at hCB
    rcases smul_eq_zero.1 hCB.symm with h | h
    · linarith
    · exact hw0 h
  · -- `B`, `P`, `C` are collinear
    rw [collinear_iff_of_mem (Set.mem_insert_of_mem B (Set.mem_insert P {C}))]
    refine ⟨w, ?_⟩
    rintro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, vadd_eq_add] at hq ⊢
    rcases hq with rfl | rfl | rfl
    · exact ⟨1, by rw [hw_def]; module⟩
    · exact ⟨0, by module⟩
    · exact ⟨t2, by rw [hC_def]; module⟩
  · -- `BC ⊥ AP`
    have hAP' : A - P = τ • v := by rw [hA_def]; module
    rw [hCB, hAP', real_inner_smul_left, real_inner_smul_right, hwv]
    ring
  · -- `X` is the midpoint of `AB`
    rw [hB_def]
    simp only [midpoint_eq_smul_add, invOf_eq_inv]
    module

/-- Exchanging the roles of `B` and `C` preserves the configuration. -/
lemma Config.swap {R r : ℝ} {O A P B C : Pt} (h : Config R r O A P B C) :
    Config R r O A P C B where
  hA := h.hA
  hP := h.hP
  hB := h.hC
  hC := h.hB
  hAP := h.hAP
  hBC := h.hBC.symm
  hcol := by
    have hset : ({C, P, B} : Set Pt) = {B, P, C} := by
      ext z
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rw [hset]
    exact h.hcol
  hperp := by
    have : B - C = -(C - B) := by module
    rw [this, inner_neg_left, h.hperp, neg_zero]

/-- **IMO 1988, Problem 1 (ii), exact locus.**  As the chord `AP` varies, the midpoint `U`
of `AB` describes exactly the circle of radius `R/2` centred at the midpoint of `OP`, with
the two points of that circle lying on the line `OP` removed. -/
theorem locus_midpoint_AB {R r : ℝ} (hr : 0 < r) (hrR : r < R) {O P : Pt}
    (hP : dist P O = r) :
    {X : Pt | ∃ A B C : Pt, Config R r O A P B C ∧ X = midpoint ℝ A B}
      = Metric.sphere (midpoint ℝ O P) (R / 2)
        \ {midpoint ℝ O P + (1 * R / (2 * r)) • (P - O),
           midpoint ℝ O P + (-1 * R / (2 * r)) • (P - O)} := by
  ext X
  simp only [Set.mem_setOf_eq, Set.mem_diff, Metric.mem_sphere, Set.mem_insert_iff,
    Set.mem_singleton_iff, not_or]
  constructor
  · rintro ⟨A, B, C, hcfg, rfl⟩
    exact ⟨dist_midpoint_AB R r O A P B C hcfg,
      midpoint_ne_on_axis hr hrR hcfg.hA hcfg.hP hcfg.hB hcfg.hAP (Or.inl rfl),
      midpoint_ne_on_axis hr hrR hcfg.hA hcfg.hP hcfg.hB hcfg.hAP (Or.inr rfl)⟩
  · rintro ⟨h1, h2, h3⟩
    exact exists_config_midpoint hr hrR hP h1 h2 h3

/-- **IMO 1988, Problem 1 (ii), exact locus.**  The same circle, minus the same two points,
is described by the midpoint `V` of `AC`. -/
theorem locus_midpoint_AC {R r : ℝ} (hr : 0 < r) (hrR : r < R) {O P : Pt}
    (hP : dist P O = r) :
    {X : Pt | ∃ A B C : Pt, Config R r O A P B C ∧ X = midpoint ℝ A C}
      = Metric.sphere (midpoint ℝ O P) (R / 2)
        \ {midpoint ℝ O P + (1 * R / (2 * r)) • (P - O),
           midpoint ℝ O P + (-1 * R / (2 * r)) • (P - O)} := by
  ext X
  simp only [Set.mem_setOf_eq, Set.mem_diff, Metric.mem_sphere, Set.mem_insert_iff,
    Set.mem_singleton_iff, not_or]
  constructor
  · rintro ⟨A, B, C, hcfg, rfl⟩
    exact ⟨dist_midpoint_AC R r O A P B C hcfg,
      midpoint_ne_on_axis hr hrR hcfg.hA hcfg.hP hcfg.hC hcfg.hAP (Or.inl rfl),
      midpoint_ne_on_axis hr hrR hcfg.hA hcfg.hP hcfg.hC hcfg.hAP (Or.inr rfl)⟩
  · rintro ⟨h1, h2, h3⟩
    obtain ⟨A, B, C, hcfg, hXm⟩ := exists_config_midpoint hr hrR hP h1 h2 h3
    exact ⟨A, C, B, hcfg.swap, hXm⟩

end IMO1988Q1
