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
# IMO 1983, Problem 4

Let `ABC` be an equilateral triangle and `E` the set of all points contained in the three
segments `AB`, `BC` and `CA` (including `A`, `B` and `C`).  For every partition of `E` into
two disjoint subsets, at least one of the two subsets contains the vertices of a
right-angled triangle.

The proof formalized here exhibits nine explicit points of `E` (three on each side) with the
property that any two-colouring of them produces a monochromatic right-angled triangle; the
relevant right angles are verified by computing inner products, and the colouring step is a
finite case check.
-/

namespace IMO1983Q4

open EuclideanGeometry RealInnerProductSpace

/-- The ambient Euclidean plane. -/
abbrev Pt := EuclideanSpace ℝ (Fin 2)

/-- The set `E` of the statement: the union of the three closed sides of the triangle
`A B C`. -/
def sides (A B C : Pt) : Set Pt :=
  segment ℝ A B ∪ segment ℝ B C ∪ segment ℝ C A

/-- `S` contains the vertices of a (nondegenerate) right-angled triangle. -/
def HasRightTriangle (S : Set Pt) : Prop :=
  ∃ P ∈ S, ∃ Q ∈ S, ∃ R ∈ S,
    P ≠ Q ∧ R ≠ Q ∧ P ≠ R ∧ ¬ Collinear ℝ ({P, Q, R} : Set Pt) ∧ ∠ P Q R = π / 2

/-! ### Elementary geometric lemmas -/

lemma angle_eq_pi_div_two_of_inner_eq_zero {P Q R : Pt} (h : ⟪P - Q, R - Q⟫ = 0) :
    ∠ P Q R = π / 2 := by
  rw [EuclideanGeometry.angle, ← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two]
  simpa using h

lemma not_collinear_of_inner_eq_zero {P Q R : Pt} (hPQ : P ≠ Q) (hRQ : R ≠ Q)
    (h : ⟪P - Q, R - Q⟫ = 0) : ¬ Collinear ℝ ({P, Q, R} : Set Pt) := by
  intro hc
  have hQmem : Q ∈ ({P, Q, R} : Set Pt) := by simp
  rw [collinear_iff_of_mem hQmem] at hc
  obtain ⟨w, hw⟩ := hc
  obtain ⟨r₁, hr₁⟩ := hw P (by simp)
  obtain ⟨r₂, hr₂⟩ := hw R (by simp)
  have e₁ : P - Q = r₁ • w := by rw [hr₁]; simp
  have e₂ : R - Q = r₂ • w := by rw [hr₂]; simp
  have hne₁ : r₁ • w ≠ 0 := by
    rw [← e₁]; exact sub_ne_zero_of_ne hPQ
  have hne₂ : r₂ • w ≠ 0 := by
    rw [← e₂]; exact sub_ne_zero_of_ne hRQ
  rw [e₁, e₂, real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq] at h
  have hr₁0 : r₁ ≠ 0 := by rintro rfl; simp at hne₁
  have hr₂0 : r₂ ≠ 0 := by rintro rfl; simp at hne₂
  have hw0 : w ≠ 0 := by rintro rfl; simp at hne₁
  have hn : ‖w‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hw0)
  simp only [mul_eq_zero] at h
  tauto

/-! ### The nine points -/

variable {A B C : Pt}

/-- The point `A + a • (B - A) + b • (C - A)`. -/
noncomputable def upt (A B C : Pt) (a b : ℝ) : Pt := A + (a • (B - A) + b • (C - A))

lemma upt_sub (A B C : Pt) (a b c d : ℝ) :
    upt A B C a b - upt A B C c d = (a - c) • (B - A) + (b - d) • (C - A) := by
  simp only [upt]
  module

section Equilateral

variable (hABBC : dist A B = dist B C) (hBCCA : dist B C = dist C A)

include hABBC hBCCA

omit hABBC hBCCA in
lemma inner_uu : ⟪B - A, B - A⟫ = dist A B ^ 2 := by
  rw [real_inner_self_eq_norm_sq, dist_eq_norm, norm_sub_rev]

lemma norm_CA : ‖C - A‖ = dist A B := by
  rw [← dist_eq_norm]; exact (hABBC.trans hBCCA).symm

lemma inner_vv : ⟪C - A, C - A⟫ = dist A B ^ 2 := by
  rw [real_inner_self_eq_norm_sq, norm_CA hABBC hBCCA]

lemma inner_uv : ⟪B - A, C - A⟫ = dist A B ^ 2 / 2 := by
  have h1 : ‖B - A‖ = dist A B := by rw [dist_eq_norm, norm_sub_rev]
  have h2 : ‖C - A‖ = dist A B := norm_CA hABBC hBCCA
  have h3 : ‖(B - A) - (C - A)‖ = dist A B := by
    rw [show (B - A) - (C - A) = B - C by abel, ← dist_eq_norm, ← hABBC]
  have := @norm_sub_sq_real _ _ _ (B - A) (C - A)
  rw [h1, h2, h3] at this
  linarith

/-- The key bilinearity computation: inner products of vectors written in the basis
`B - A`, `C - A` are rational multiples of the square of the side length. -/
lemma inner_key (a b c d : ℝ) :
    ⟪a • (B - A) + b • (C - A), c • (B - A) + d • (C - A)⟫
      = dist A B ^ 2 * (a * c + b * d + (a * d + b * c) / 2) := by
  have huv := inner_uv hABBC hBCCA
  have hvu : ⟪C - A, B - A⟫ = dist A B ^ 2 / 2 := by
    rw [real_inner_comm]; exact huv
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    inner_uu, inner_vv hABBC hBCCA, huv, hvu]
  ring

lemma upt_inner (a b c d a' b' c' d' : ℝ) :
    ⟪upt A B C a b - upt A B C c d, upt A B C a' b' - upt A B C c' d'⟫
      = dist A B ^ 2 * ((a - c) * (a' - c') + (b - d) * (b' - d')
          + ((a - c) * (b' - d') + (b - d) * (a' - c')) / 2) := by
  rw [upt_sub, upt_sub, inner_key hABBC hBCCA]

variable (hAB : A ≠ B)
include hAB

omit hABBC hBCCA in
lemma side_sq_pos : (0:ℝ) < dist A B ^ 2 := by
  have : dist A B ≠ 0 := by simpa using hAB
  positivity

/-- Two points of the parametrization coincide only if their parameters do. -/
lemma upt_ne {a b c d : ℝ} (h : (a - c) ^ 2 + (a - c) * (b - d) + (b - d) ^ 2 ≠ 0) :
    upt A B C a b ≠ upt A B C c d := by
  intro heq
  have hz : upt A B C a b - upt A B C c d = 0 := by rw [heq]; simp
  have h0 : ⟪upt A B C a b - upt A B C c d, upt A B C a b - upt A B C c d⟫ = 0 := by
    rw [hz]; simp
  rw [upt_inner hABBC hBCCA] at h0
  have hs := side_sq_pos (A := A) (B := B) hAB
  have : (a - c) * (a - c) + (b - d) * (b - d) + ((a - c) * (b - d) + (b - d) * (a - c)) / 2 = 0 := by
    rcases mul_eq_zero.mp h0 with h' | h'
    · exact absurd h' (ne_of_gt hs)
    · exact h'
  exact h (by linear_combination this)

end Equilateral

/-! ### Membership of the nine points in `E` -/

/-- A point with parameters `(a, 0)`, `0 ≤ a ≤ 1`, lies on the side `AB`. -/
lemma upt_mem_AB (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) : upt A B C a 0 ∈ sides A B C := by
  left; left
  refine ⟨1 - a, a, by linarith, ha0, by ring, ?_⟩
  simp only [upt]
  match_scalars <;> linarith

/-- A point with parameters `(a, b)`, `a, b ≥ 0` and `a + b = 1`, lies on the side `BC`. -/
lemma upt_mem_BC (a b : ℝ) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hab : a + b = 1) :
    upt A B C a b ∈ sides A B C := by
  left; right
  refine ⟨a, b, ha0, hb0, hab, ?_⟩
  simp only [upt]
  match_scalars <;> linarith

/-- A point with parameters `(0, b)`, `0 ≤ b ≤ 1`, lies on the side `CA`. -/
lemma upt_mem_CA (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) : upt A B C 0 b ∈ sides A B C := by
  right
  refine ⟨b, 1 - b, hb0, by linarith, by ring, ?_⟩
  simp only [upt]
  match_scalars <;> linarith

/-! ### The combinatorial core -/

attribute [-instance] Classical.propDecidable in
set_option synthInstance.maxSize 4000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- The hypergraph of the twelve right-angled triples among our nine points is not
`2`-colourable. -/
lemma bool_ramsey (c0 c1 c2 c3 c4 c5 c6 c7 c8 : Bool) :
    (c0 = c1 ∧ c0 = c7) ∨ (c0 = c2 ∧ c0 = c6) ∨ (c0 = c3 ∧ c0 = c4) ∨ (c0 = c4 ∧ c0 = c5) ∨
    (c1 = c2 ∧ c1 = c8) ∨ (c1 = c3 ∧ c1 = c5) ∨ (c1 = c4 ∧ c1 = c5) ∨ (c2 = c3 ∧ c2 = c4) ∨
    (c2 = c3 ∧ c2 = c5) ∨ (c3 = c4 ∧ c3 = c6) ∨ (c3 = c5 ∧ c3 = c8) ∨
    (c4 = c5 ∧ c4 = c7) := by
  decide +revert

/-- If three points of `E` lying in a right angle configuration receive the same colour,
one of the two classes contains a right-angled triangle. -/
lemma mono_right_triangle {S T : Set Pt} (hcov : sides A B C ⊆ S ∪ T)
    {P Q R : Pt} (hP : P ∈ sides A B C) (hQ : Q ∈ sides A B C) (hR : R ∈ sides A B C)
    (h1 : decide (P ∈ S) = decide (Q ∈ S)) (h2 : decide (P ∈ S) = decide (R ∈ S))
    (hPQ : P ≠ Q) (hRQ : R ≠ Q) (hPR : P ≠ R) (hang : ⟪P - Q, R - Q⟫ = 0) :
    HasRightTriangle S ∨ HasRightTriangle T := by
  have hangle := angle_eq_pi_div_two_of_inner_eq_zero hang
  have hcol := not_collinear_of_inner_eq_zero hPQ hRQ hang
  have i1 : P ∈ S ↔ Q ∈ S := decide_eq_decide.mp h1
  have i2 : P ∈ S ↔ R ∈ S := decide_eq_decide.mp h2
  by_cases hPS : P ∈ S
  · left
    exact ⟨P, hPS, Q, i1.mp hPS, R, i2.mp hPS, hPQ, hRQ, hPR, hcol, hangle⟩
  · right
    have hQS : Q ∉ S := fun h => hPS (i1.mpr h)
    have hRS : R ∉ S := fun h => hPS (i2.mpr h)
    have memT : ∀ X : Pt, X ∈ sides A B C → X ∉ S → X ∈ T := by
      intro X hX hXS
      rcases hcov hX with h | h
      · exact absurd h hXS
      · exact h
    exact ⟨P, memT P hP hPS, Q, memT Q hQ hQS, R, memT R hR hRS, hPQ, hRQ, hPR, hcol, hangle⟩

/-! ### Main theorem -/

/-- **IMO 1983, Problem 4.**  For every partition of the union `E` of the three sides of an
equilateral triangle `ABC` into two disjoint subsets `S` and `T`, at least one of `S`, `T`
contains the three vertices of a right-angled triangle.  (The disjointness hypothesis is not
needed for the conclusion.) -/
theorem imo1983_q4 (A B C : Pt) (hABBC : dist A B = dist B C) (hBCCA : dist B C = dist C A)
    (hAB : A ≠ B) (S T : Set Pt) (hunion : S ∪ T = sides A B C) (hdisj : Disjoint S T) :
    HasRightTriangle S ∨ HasRightTriangle T := by
  have hcov : sides A B C ⊆ S ∪ T := by rw [hunion]
  -- the nine points
  set p0 : Pt := upt A B C (1/3) 0 with hp0
  set p1 : Pt := upt A B C (2/3) (1/3) with hp1
  set p2 : Pt := upt A B C 0 (2/3) with hp2
  set p3 : Pt := upt A B C (2/3) 0 with hp3
  set p4 : Pt := upt A B C (1/3) (2/3) with hp4
  set p5 : Pt := upt A B C 0 (1/3) with hp5
  set p6 : Pt := upt A B C (3/4) 0 with hp6
  set p7 : Pt := upt A B C (1/4) (3/4) with hp7
  set p8 : Pt := upt A B C 0 (1/4) with hp8
  have m0 : p0 ∈ sides A B C := upt_mem_AB _ (by norm_num) (by norm_num)
  have m3 : p3 ∈ sides A B C := upt_mem_AB _ (by norm_num) (by norm_num)
  have m6 : p6 ∈ sides A B C := upt_mem_AB _ (by norm_num) (by norm_num)
  have m1 : p1 ∈ sides A B C := upt_mem_BC _ _ (by norm_num) (by norm_num) (by norm_num)
  have m4 : p4 ∈ sides A B C := upt_mem_BC _ _ (by norm_num) (by norm_num) (by norm_num)
  have m7 : p7 ∈ sides A B C := upt_mem_BC _ _ (by norm_num) (by norm_num) (by norm_num)
  have m2 : p2 ∈ sides A B C := upt_mem_CA _ (by norm_num) (by norm_num)
  have m5 : p5 ∈ sides A B C := upt_mem_CA _ (by norm_num) (by norm_num)
  have m8 : p8 ∈ sides A B C := upt_mem_CA _ (by norm_num) (by norm_num)
  -- distinctness
  have ne : ∀ {a b c d : ℝ}, (a - c) ^ 2 + (a - c) * (b - d) + (b - d) ^ 2 ≠ 0 →
      upt A B C a b ≠ upt A B C c d := fun h => upt_ne hABBC hBCCA hAB h
  -- right angles
  have ang : ∀ a b c d a' b' : ℝ,
      (a - c) * (a' - c) + (b - d) * (b' - d) + ((a - c) * (b' - d) + (b - d) * (a' - c)) / 2 = 0 →
      ⟪upt A B C a b - upt A B C c d, upt A B C a' b' - upt A B C c d⟫ = 0 := by
    intro a b c d a' b' h
    rw [upt_inner hABBC hBCCA, h, mul_zero]
  rcases bool_ramsey (decide (p0 ∈ S)) (decide (p1 ∈ S)) (decide (p2 ∈ S)) (decide (p3 ∈ S))
      (decide (p4 ∈ S)) (decide (p5 ∈ S)) (decide (p6 ∈ S)) (decide (p7 ∈ S))
      (decide (p8 ∈ S)) with
    h | h | h | h | h | h | h | h | h | h | h | h
  -- (0,1,7), right angle at 1
  · exact mono_right_triangle hcov m0 m1 m7 h.1 h.2
      (ne (by norm_num)) (ne (by norm_num)) (ne (by norm_num)) (ang _ _ _ _ _ _ (by norm_num))
  -- (0,2,6), right angle at 0 : (P,Q,R) = (p2,p0,p6)
  · exact mono_right_triangle hcov m2 m0 m6 h.1.symm (h.1.symm.trans h.2)
      (ne (by norm_num)) (ne (by norm_num)) (ne (by norm_num)) (ang _ _ _ _ _ _ (by norm_num))
  -- (0,3,4), right angle at 3 : (p0,p3,p4)
  · exact mono_right_triangle hcov m0 m3 m4 h.1 h.2
      (ne (by norm_num)) (ne (by norm_num)) (ne (by norm_num)) (ang _ _ _ _ _ _ (by norm_num))
  -- (0,4,5), right angle at 5 : (p0,p5,p4)
  · exact mono_right_triangle hcov m0 m5 m4 h.2 h.1
      (ne (by norm_num)) (ne (by norm_num)) (ne (by norm_num)) (ang _ _ _ _ _ _ (by norm_num))
  -- (1,2,8), right angle at 2 : (p1,p2,p8)
  · exact mono_right_triangle hcov m1 m2 m8 h.1 h.2
      (ne (by norm_num)) (ne (by norm_num)) (ne (by norm_num)) (ang _ _ _ _ _ _ (by norm_num))
  -- (1,3,5), right angle at 3 : (p1,p3,p5)
  · exact mono_right_triangle hcov m1 m3 m5 h.1 h.2
      (ne (by norm_num)) (ne (by norm_num)) (ne (by norm_num)) (ang _ _ _ _ _ _ (by norm_num))
  -- (1,4,5), right angle at 4 : (p1,p4,p5)
  · exact mono_right_triangle hcov m1 m4 m5 h.1 h.2
      (ne (by norm_num)) (ne (by norm_num)) (ne (by norm_num)) (ang _ _ _ _ _ _ (by norm_num))
  -- (2,3,4), right angle at 4 : (p2,p4,p3)
  · exact mono_right_triangle hcov m2 m4 m3 h.2 h.1
      (ne (by norm_num)) (ne (by norm_num)) (ne (by norm_num)) (ang _ _ _ _ _ _ (by norm_num))
  -- (2,3,5), right angle at 5 : (p2,p5,p3)
  · exact mono_right_triangle hcov m2 m5 m3 h.2 h.1
      (ne (by norm_num)) (ne (by norm_num)) (ne (by norm_num)) (ang _ _ _ _ _ _ (by norm_num))
  -- (3,4,6), right angle at 3 : (p4,p3,p6)
  · exact mono_right_triangle hcov m4 m3 m6 h.1.symm (h.1.symm.trans h.2)
      (ne (by norm_num)) (ne (by norm_num)) (ne (by norm_num)) (ang _ _ _ _ _ _ (by norm_num))
  -- (3,5,8), right angle at 5 : (p3,p5,p8)
  · exact mono_right_triangle hcov m3 m5 m8 h.1 h.2
      (ne (by norm_num)) (ne (by norm_num)) (ne (by norm_num)) (ang _ _ _ _ _ _ (by norm_num))
  -- (4,5,7), right angle at 4 : (p5,p4,p7)
  · exact mono_right_triangle hcov m5 m4 m7 h.1.symm (h.1.symm.trans h.2)
      (ne (by norm_num)) (ne (by norm_num)) (ne (by norm_num)) (ang _ _ _ _ _ _ (by norm_num))

/-- Non-vacuity check: the hypotheses of `imo1983_q4` are satisfiable, i.e. there really is an
equilateral triangle in the plane. -/
lemma exists_equilateral :
    ∃ A B C : Pt, dist A B = dist B C ∧ dist B C = dist C A ∧ A ≠ B := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  refine ⟨!₂[0, 0], !₂[1, 0], !₂[1 / 2, Real.sqrt 3 / 2], ?_, ?_, ?_⟩
  · rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq]
    simp only [Fin.sum_univ_two, Real.dist_eq]
    norm_num [sq_abs, div_pow, h3]
  · rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq]
    simp only [Fin.sum_univ_two, Real.dist_eq]
    norm_num [sq_abs, div_pow, h3]
  · intro h
    have : (!₂[(0 : ℝ), 0] : Pt) 0 = (!₂[(1 : ℝ), 0] : Pt) 0 := by rw [h]
    norm_num at this

end IMO1983Q4

s
