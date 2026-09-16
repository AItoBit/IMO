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
# IMO 2003, Problem 4

Let `ABCD` be a cyclic quadrilateral.  Let `P`, `Q`, `R` be the feet of the perpendiculars
from `D` to the lines `BC`, `CA`, `AB` respectively.  Show that `PQ = QR` if and only if the
bisectors of the angles `ABC` and `ADC` meet on the segment `AC`.

The plane is modelled as `ℂ`, with its usual (real) inner product and distance.
-/

namespace IMO2003Q4

/-- The two-dimensional cross product of two vectors of the plane `ℂ`. It vanishes exactly
when the two vectors are parallel. -/
noncomputable def cross (u v : ℂ) : ℝ := u.re * v.im - u.im * v.re

/-- The internal bisector ray of the angle `∠ X Y Z` at the vertex `Y`: the ray starting at `Y`
in the direction of the sum of the unit vectors pointing from `Y` to `X` and from `Y` to `Z`. -/
noncomputable def bisectorRay (X Y Z : ℂ) : Set ℂ :=
  {W | ∃ s : ℝ, 0 ≤ s ∧ W = Y + s • ((dist Y X)⁻¹ • (X - Y) + (dist Y Z)⁻¹ • (Z - Y))}

/-- The square of the distance in `ℂ`, in coordinates. -/
theorem dist_sq (z w : ℂ) : dist z w ^ 2 = (z.re - w.re) ^ 2 + (z.im - w.im) ^ 2 := by
  rw [Complex.dist_eq_re_im, Real.sq_sqrt (by positivity)]

/-- The real inner product of two vectors of the plane `ℂ`, in coordinates. -/
theorem inner_eq (z w : ℂ) : inner ℝ z w = z.re * w.re + z.im * w.im := by
  simp; ring

/-- A nonzero vector has nonzero squared length. -/
theorem sq_add_sq_ne_zero {u : ℂ} (hu : u ≠ 0) : u.re ^ 2 + u.im ^ 2 ≠ 0 := by
  intro hz
  have hr : u.re = 0 := by nlinarith [sq_nonneg u.re, sq_nonneg u.im]
  have hi : u.im = 0 := by nlinarith [sq_nonneg u.re, sq_nonneg u.im]
  exact hu (Complex.ext (by simp [hr]) (by simp [hi]))

/-- Two parallel vectors, the first one nonzero, are proportional. -/
theorem smul_of_cross_eq_zero {u v : ℂ} (hu : u ≠ 0) (h : cross u v = 0) :
    ∃ t : ℝ, v = t • u := by
  have hn := sq_add_sq_ne_zero hu
  simp only [cross] at h
  refine ⟨(u.re * v.re + u.im * v.im) / (u.re ^ 2 + u.im ^ 2), Complex.ext ?_ ?_⟩ <;>
    simp only [Complex.smul_re, Complex.smul_im, smul_eq_mul] <;> field_simp
  · linear_combination (-u.im) * h
  · linear_combination u.re * h

/-- If three points are not collinear, the corresponding cross product is nonzero. -/
theorem cross_ne_zero_of_not_collinear {A B C : ℂ} (h : ¬ Collinear ℝ ({A, B, C} : Set ℂ)) :
    cross (B - A) (C - A) ≠ 0 := by
  intro hcr
  apply h
  rw [collinear_iff_of_mem (Set.mem_insert A ({B, C} : Set ℂ))]
  rcases eq_or_ne B A with hBA | hBA
  · refine ⟨C - A, ?_⟩
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨0, by simp [hBA]⟩
    · exact ⟨1, by simp⟩
  · obtain ⟨t, ht⟩ := smul_of_cross_eq_zero (sub_ne_zero.2 hBA) hcr
    refine ⟨B - A, ?_⟩
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
    · exact ⟨t, by rw [← ht]; simp⟩

/-- Two non-parallel vectors are linearly independent. -/
theorem eq_zero_of_smul_add_smul {u v : ℂ} (h : cross u v ≠ 0) {p q : ℝ}
    (hpq : p • u + q • v = 0) : p = 0 ∧ q = 0 := by
  have h1 : p * u.re + q * v.re = 0 := by
    have := congrArg Complex.re hpq; simpa using this
  have h2 : p * u.im + q * v.im = 0 := by
    have := congrArg Complex.im hpq; simpa using this
  simp only [cross] at h
  refine ⟨?_, ?_⟩
  · rcases mul_eq_zero.1 (show p * (u.re * v.im - u.im * v.re) = 0 by
      linear_combination v.im * h1 - v.re * h2) with hp | hc
    · exact hp
    · exact absurd hc h
  · rcases mul_eq_zero.1 (show q * (u.re * v.im - u.im * v.re) = 0 by
      linear_combination u.re * h2 - u.im * h1) with hq | hc
    · exact hq
    · exact absurd hc h

/-- The distance between the feet of the perpendiculars dropped from `D` onto two lines through
a common point `Z`, with directions `u` and `v`. -/
theorem feet_dist_sq {Z D P Q u v : ℂ}
    (hP : ∃ t : ℝ, P = Z + t • u) (hPp : inner ℝ (D - P) u = (0 : ℝ))
    (hQ : ∃ t : ℝ, Q = Z + t • v) (hQp : inner ℝ (D - Q) v = (0 : ℝ))
    (hu : u ≠ 0) (hv : v ≠ 0) :
    dist P Q ^ 2 * ((u.re ^ 2 + u.im ^ 2) * (v.re ^ 2 + v.im ^ 2))
      = dist D Z ^ 2 * cross u v ^ 2 := by
  obtain ⟨t, rfl⟩ := hP
  obtain ⟨s, rfl⟩ := hQ
  have hnu := sq_add_sq_ne_zero hu
  have hnv := sq_add_sq_ne_zero hv
  rw [inner_eq] at hPp hQp
  simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
    Complex.smul_re, Complex.smul_im, smul_eq_mul] at hPp hQp
  have ht : t = ((D.re - Z.re) * u.re + (D.im - Z.im) * u.im) / (u.re ^ 2 + u.im ^ 2) := by
    field_simp
    linarith [hPp]
  have hs : s = ((D.re - Z.re) * v.re + (D.im - Z.im) * v.im) / (v.re ^ 2 + v.im ^ 2) := by
    field_simp
    linarith [hQp]
  subst ht hs
  rw [dist_sq, dist_sq, cross]
  simp only [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im, smul_eq_mul]
  field_simp
  ring

/-- Three distinct points on a circle are not collinear. -/
theorem cross_ne_zero_of_circle {O A C D : ℂ} {r : ℝ} (hA : dist O A = r) (hC : dist O C = r)
    (hD : dist O D = r) (hAC : A ≠ C) (hDA : D ≠ A) (hDC : D ≠ C) :
    cross (A - D) (C - D) ≠ 0 := by
  intro hcr
  have hu : C - A ≠ 0 := sub_ne_zero.2 (Ne.symm hAC)
  have hcr' : cross (C - A) (D - A) = 0 := by
    simp only [cross, Complex.sub_re, Complex.sub_im] at hcr ⊢
    linear_combination hcr
  obtain ⟨t, ht⟩ := smul_of_cross_eq_zero hu hcr'
  have hre : D.re - A.re = t * (C.re - A.re) := by
    have := congrArg Complex.re ht
    simpa [Complex.smul_re] using this
  have him : D.im - A.im = t * (C.im - A.im) := by
    have := congrArg Complex.im ht
    simpa [Complex.smul_im] using this
  have hA2 : (O.re - A.re) ^ 2 + (O.im - A.im) ^ 2 = r ^ 2 := by rw [← dist_sq, hA]
  have hC2 : (O.re - C.re) ^ 2 + (O.im - C.im) ^ 2 = r ^ 2 := by rw [← dist_sq, hC]
  have hD2 : (O.re - D.re) ^ 2 + (O.im - D.im) ^ 2 = r ^ 2 := by rw [← dist_sq, hD]
  have hDre : D.re = A.re + t * (C.re - A.re) := by linarith
  have hDim : D.im = A.im + t * (C.im - A.im) := by linarith
  rw [hDre, hDim] at hD2
  have hN := sq_add_sq_ne_zero hu
  simp only [Complex.sub_re, Complex.sub_im] at hN
  have key : t * (t - 1) * ((C.re - A.re) ^ 2 + (C.im - A.im) ^ 2) = 0 := by
    linear_combination hD2 - t * hC2 + (t - 1) * hA2
  rcases mul_eq_zero.1 key with h | h
  · rcases mul_eq_zero.1 h with h0 | h1
    · exact hDA (by rw [← sub_eq_zero, ht, h0, zero_smul])
    · have ht1 : t = 1 := by linarith
      have h2 : D - A = C - A := by rw [ht, ht1, one_smul]
      exact hDC (by linear_combination h2)
  · exact hN h

/-- The squared length of a difference, in coordinates. -/
theorem normsq_eq_dist_sq (z w : ℂ) : (z - w).re ^ 2 + (z - w).im ^ 2 = dist z w ^ 2 := by
  rw [dist_sq]; simp

/-- Feet of perpendiculars: `PQ = QR` if and only if `BA · DC = BC · DA`. -/
theorem feet_dist_eq_iff {A B C D P Q R : ℂ}
    (hABC : cross (B - A) (C - A) ≠ 0)
    (hP : ∃ t : ℝ, P = B + t • (C - B)) (hP' : inner ℝ (D - P) (C - B) = (0 : ℝ))
    (hQ : ∃ t : ℝ, Q = C + t • (A - C)) (hQ' : inner ℝ (D - Q) (A - C) = (0 : ℝ))
    (hR : ∃ t : ℝ, R = A + t • (B - A)) (hR' : inner ℝ (D - R) (B - A) = (0 : ℝ)) :
    dist P Q = dist Q R ↔ dist B A * dist D C = dist B C * dist D A := by
  have hBA : B - A ≠ 0 := by
    intro h; apply hABC; rw [h]; simp [cross]
  have hCA : C - A ≠ 0 := by
    intro h; apply hABC; rw [h]; simp [cross]
  have hCB : C - B ≠ 0 := by
    intro h; apply hABC
    have hCB' : C - A = B - A := by linear_combination h
    rw [hCB']; simp only [cross]; ring
  have hAC : A - C ≠ 0 := by
    intro h; apply hCA; have hh : C - A = -(A - C) := by ring
    rw [hh, h]; ring
  have hPc : ∃ s : ℝ, P = C + s • (C - B) := by
    obtain ⟨t, rfl⟩ := hP; exact ⟨t - 1, by module⟩
  have hQa : ∃ s : ℝ, Q = A + s • (C - A) := by
    obtain ⟨t, rfl⟩ := hQ; exact ⟨1 - t, by module⟩
  have hQ'' : inner ℝ (D - Q) (C - A) = (0 : ℝ) := by
    rw [inner_eq] at hQ' ⊢
    simp only [Complex.sub_re, Complex.sub_im] at hQ' ⊢
    linarith
  have e1 := feet_dist_sq hPc hP' hQ hQ' hCB hAC
  have e2 := feet_dist_sq hQa hQ'' hR hR' hCA hBA
  rw [normsq_eq_dist_sq, normsq_eq_dist_sq] at e1 e2
  have hc1 : cross (C - B) (A - C) = cross (B - A) (C - A) := by
    simp only [cross, Complex.sub_re, Complex.sub_im]; ring
  have hc2 : cross (C - A) (B - A) = -cross (B - A) (C - A) := by
    simp only [cross, Complex.sub_re, Complex.sub_im]; ring
  rw [hc1] at e1
  rw [hc2, neg_sq] at e2
  rw [dist_comm C B, dist_comm A C] at e1
  set S := cross (B - A) (C - A) with hS
  set x := dist B A with hx
  set y := dist B C with hy
  set z := dist C A with hz
  have hxpos : 0 < x := dist_pos.2 (fun h => hBA (by rw [h]; ring))
  have hypos : 0 < y := dist_pos.2 (fun h => hCB (by rw [h]; ring))
  have hzpos : 0 < z := dist_pos.2 (fun h => hCA (by rw [h]; ring))
  have main : dist P Q ^ 2 * (y ^ 2 * z ^ 2 * x ^ 2) = (x * dist D C) ^ 2 * S ^ 2 := by
    linear_combination x ^ 2 * e1
  have main2 : dist Q R ^ 2 * (y ^ 2 * z ^ 2 * x ^ 2) = (y * dist D A) ^ 2 * S ^ 2 := by
    linear_combination y ^ 2 * e2
  constructor
  · intro h
    have h2 : dist P Q ^ 2 = dist Q R ^ 2 := by rw [h]
    have h3 : (x * dist D C) ^ 2 * S ^ 2 = (y * dist D A) ^ 2 * S ^ 2 := by
      linear_combination -main + main2 + (y ^ 2 * z ^ 2 * x ^ 2) * h2
    have h4 : (x * dist D C) ^ 2 = (y * dist D A) ^ 2 :=
      mul_right_cancel₀ (pow_ne_zero 2 hABC) h3
    exact (pow_left_inj₀ (by positivity) (by positivity) two_ne_zero).1 h4
  · intro h
    have h4 : (x * dist D C) ^ 2 = (y * dist D A) ^ 2 := by rw [h]
    have h5 : dist P Q ^ 2 * (y ^ 2 * z ^ 2 * x ^ 2)
        = dist Q R ^ 2 * (y ^ 2 * z ^ 2 * x ^ 2) := by
      linear_combination main - main2 + S ^ 2 * h4
    have h6 : dist P Q ^ 2 = dist Q R ^ 2 := mul_right_cancel₀ (by positivity) h5
    exact (pow_left_inj₀ dist_nonneg dist_nonneg two_ne_zero).1 h6

/-- The bisectors of the angles `ABC` and `ADC` meet on the segment `AC` if and only if
`BA · DC = BC · DA`. -/
theorem bisectors_meet_iff {A B C D : ℂ} (hB : cross (A - B) (C - B) ≠ 0)
    (hD : cross (A - D) (C - D) ≠ 0) :
    (∃ X ∈ segment ℝ A C, X ∈ bisectorRay A B C ∧ X ∈ bisectorRay A D C) ↔
      dist B A * dist D C = dist B C * dist D A := by
  sorry

/-- **IMO 2003, Problem 4.**  Let `ABCD` be a cyclic quadrilateral (its vertices lie on the
circle with centre `O` and radius `r`, and `A`, `B`, `C` are not collinear, `D ≠ A`, `D ≠ C`).
Let `P`, `Q`, `R` be the feet of the perpendiculars from `D` to the lines `BC`, `CA`, `AB`.
Then `PQ = QR` if and only if the bisectors of the angles `ABC` and `ADC` meet on the
segment `AC`. -/
theorem imo2003_q4 {O A B C D P Q R : ℂ} {r : ℝ}
    (hOA : dist O A = r) (hOB : dist O B = r) (hOC : dist O C = r) (hOD : dist O D = r)
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set ℂ)) (hDA : D ≠ A) (hDC : D ≠ C)
    (hP : ∃ t : ℝ, P = B + t • (C - B)) (hP' : inner ℝ (D - P) (C - B) = (0 : ℝ))
    (hQ : ∃ t : ℝ, Q = C + t • (A - C)) (hQ' : inner ℝ (D - Q) (A - C) = (0 : ℝ))
    (hR : ∃ t : ℝ, R = A + t • (B - A)) (hR' : inner ℝ (D - R) (B - A) = (0 : ℝ)) :
    dist P Q = dist Q R ↔
      ∃ X ∈ segment ℝ A C, X ∈ bisectorRay A B C ∧ X ∈ bisectorRay A D C := by
  have hcABC : cross (B - A) (C - A) ≠ 0 := cross_ne_zero_of_not_collinear hABC
  have hAC : A ≠ C := by
    rintro rfl
    refine hABC ?_
    have hset : ({A, B, A} : Set ℂ) = {A, B} := by
      ext x; constructor <;> (intro hx; simp only [Set.mem_insert_iff,
        Set.mem_singleton_iff] at hx ⊢; tauto)
    rw [hset]
    exact collinear_pair ℝ A B
  have hcB : cross (A - B) (C - B) ≠ 0 := by
    intro h
    apply hcABC
    simp only [cross, Complex.sub_re, Complex.sub_im] at h ⊢
    linear_combination -h
  have hcD : cross (A - D) (C - D) ≠ 0 :=
    cross_ne_zero_of_circle hOA hOC hOD hAC hDA hDC
  rw [feet_dist_eq_iff hcABC hP hP' hQ hQ' hR hR', bisectors_meet_iff hcB hcD]

end IMO2003Q4
