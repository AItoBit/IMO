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
# IMO 1995, Problem 5

Let `ABCDEF` be a convex hexagon with `AB = BC = CD` and `DE = EF = FA`, such that
`∠BCD = ∠EFA = π/3`.  Suppose `G` and `H` are points in the interior of the hexagon such
that `∠AGB = ∠DHE = 2π/3`.  Prove that `AG + GB + GH + DH + HE ≥ CF`.

The plane is modelled by `ℂ`, distances are the usual `dist`, and angles are
`EuclideanGeometry.angle`.

The proof follows the classical solution.  The hypotheses `AB = BC = CD` and `∠BCD = π/3`
force the triangle `BCD` to be equilateral, and similarly for `EFA`; moreover `B` and `E`
are then both equidistant from `A` and `D`, so that `BE` is the perpendicular bisector
of `AD`.  Erecting equilateral triangles `AIB` and `DJE` outwards, Ptolemy's inequality
gives `GI ≤ GA + GB` and `HJ ≤ HD + HE`, while the perpendicularity gives `IJ = CF`; the
triangle inequality `IJ ≤ IG + GH + HJ` finishes the proof.
-/

namespace IMO1995P5

/-- The rotation by `-π/3`, as a complex number of modulus one. -/
noncomputable def wb : ℂ := ⟨1 / 2, -Real.sqrt 3 / 2⟩

/-- `ccw p q r` says that the triple `(p, q, r)` makes a strict left turn, i.e. `r` lies
strictly to the left of the directed line from `p` to `q`. -/
def ccw (p q r : ℂ) : Prop := 0 < ((starRingEnd ℂ) (q - p) * (r - p)).im

/-- A hexagon `ABCDEF` traversed counterclockwise, all of whose vertices are strictly
convex. -/
def CCWHexagon (A B C D E F : ℂ) : Prop :=
  ccw A B C ∧ ccw B C D ∧ ccw C D E ∧ ccw D E F ∧ ccw E F A ∧ ccw F A B

/-- `ABCDEF` is a convex hexagon: traversing its vertices in the given order (or in the
reversed order), every vertex is a strict turn in the same direction. -/
def ConvexHexagon (A B C D E F : ℂ) : Prop :=
  CCWHexagon A B C D E F ∨ CCWHexagon F E D C B A

/-- Sanity check: a concrete counterclockwise convex hexagon. -/
example : CCWHexagon ⟨0, 0⟩ ⟨2, 0⟩ ⟨3, 1⟩ ⟨3, 3⟩ ⟨2, 4⟩ ⟨0, 3⟩ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · simp only [ccw, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.conj_re,
        Complex.conj_im]
      norm_num

/-! ### Basic facts -/

lemma sqrt3_sq : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)

lemma normSq_wb : Complex.normSq wb = 1 := by
  simp only [Complex.normSq_apply, wb]
  nlinarith [sqrt3_sq]

lemma normSq_one_sub_wb : Complex.normSq (1 - wb) = 1 := by
  simp only [Complex.normSq_apply, wb, Complex.sub_re, Complex.sub_im, Complex.one_re,
    Complex.one_im]
  nlinarith [sqrt3_sq]

lemma norm_of_normSq {z : ℂ} (h : Complex.normSq z = 1) : ‖z‖ = 1 := by
  have h2 : ‖z‖ ^ 2 = 1 := by rw [Complex.sq_norm, h]
  nlinarith [norm_nonneg z]

lemma norm_eq_of_normSq_eq {z w : ℂ} (h : Complex.normSq z = Complex.normSq w) : ‖z‖ = ‖w‖ := by
  nlinarith [Complex.sq_norm z, Complex.sq_norm w, norm_nonneg z, norm_nonneg w]

lemma normSq_of_dist {z w u v : ℂ} (h : dist z w = dist u v) :
    Complex.normSq (z - w) = Complex.normSq (u - v) := by
  rw [← Complex.sq_norm, ← Complex.sq_norm, ← Complex.dist_eq, ← Complex.dist_eq, h]

/-! ### Ptolemy's inequality and the apex of an erected equilateral triangle -/

/-- Ptolemy's inequality in the complex plane. -/
lemma ptolemy (a b g i : ℂ) :
    dist g i * dist a b ≤ dist g a * dist b i + dist g b * dist i a := by
  have key : (g - i) * (b - a) = (g - a) * (b - i) + (g - b) * (i - a) := by ring
  simp only [Complex.dist_eq]
  calc ‖g - i‖ * ‖a - b‖ = ‖(g - i) * (b - a)‖ := by rw [norm_mul, norm_sub_rev a b]
    _ = ‖(g - a) * (b - i) + (g - b) * (i - a)‖ := by rw [key]
    _ ≤ ‖(g - a) * (b - i)‖ + ‖(g - b) * (i - a)‖ := norm_add_le _ _
    _ = ‖g - a‖ * ‖b - i‖ + ‖g - b‖ * ‖i - a‖ := by rw [norm_mul, norm_mul]

/-- If `i` is the apex of the equilateral triangle erected on the segment `ab`, then
`gi ≤ ga + gb` for every point `g`; this is a consequence of Ptolemy's inequality. -/
lemma dist_apex_le (a b g : ℂ) (hab : a ≠ b) :
    dist g (a + wb * (b - a)) ≤ dist g a + dist g b := by
  set i : ℂ := a + wb * (b - a) with hi
  have hia : dist i a = dist a b := by
    rw [Complex.dist_eq, Complex.dist_eq, hi, add_sub_cancel_left, norm_mul,
      norm_of_normSq normSq_wb, one_mul, norm_sub_rev]
  have hib : dist b i = dist a b := by
    have h : b - i = (1 - wb) * (b - a) := by rw [hi]; ring
    rw [Complex.dist_eq, h, norm_mul, norm_of_normSq normSq_one_sub_wb, one_mul,
      Complex.dist_eq, norm_sub_rev]
  have hd : (0:ℝ) < dist a b := dist_pos.mpr hab
  have hp := ptolemy a b g i
  rw [hia, hib] at hp
  have h2 : dist g i * dist a b ≤ (dist g a + dist g b) * dist a b := by nlinarith [hp]
  exact le_of_mul_le_mul_right h2 hd

/-! ### Recognising the erected equilateral triangles -/

lemma rot_real (x y p q : ℝ) (E1 : x * x + y * y = p * p + q * q)
    (E2 : (x - p) * (x - p) + (y - q) * (y - q) = p * p + q * q) (hor : 0 < x * q - y * p) :
    x = (p + Real.sqrt 3 * q) / 2 ∧ y = (q - Real.sqrt 3 * p) / 2 := by
  have hCS : (x * q - y * p) ^ 2 ≤ (x * x + y * y) * (p * p + q * q) := by
    nlinarith [sq_nonneg (x * p + y * q)]
  have hRpos : 0 < p * p + q * q := by nlinarith [hCS, hor, E1]
  have hlin : x * p + y * q = (p * p + q * q) / 2 := by linarith [E1, E2, sq_nonneg (x - p)]
  have h3 : Real.sqrt 3 ^ 2 = 3 := by nlinarith [sqrt3_sq]
  have hsq : (x * q - y * p) ^ 2 = (Real.sqrt 3 * (p * p + q * q) / 2) ^ 2 := by
    linear_combination (p * p + q * q) * E1 - (x * p + y * q + (p * p + q * q) / 2) * hlin -
      ((p * p + q * q) ^ 2 / 4) * h3
  have hnn : 0 ≤ Real.sqrt 3 * (p * p + q * q) / 2 := by positivity
  have hcross : x * q - y * p = Real.sqrt 3 * (p * p + q * q) / 2 := by
    nlinarith [hsq, hor, hnn]
  refine ⟨mul_right_cancel₀ (ne_of_gt hRpos) ?_, mul_right_cancel₀ (ne_of_gt hRpos) ?_⟩
  · show x * (p * p + q * q) = ((p + Real.sqrt 3 * q) / 2) * (p * p + q * q)
    linear_combination p * hlin + q * hcross
  · show y * (p * p + q * q) = ((q - Real.sqrt 3 * p) / 2) * (p * p + q * q)
    linear_combination q * hlin - p * hcross

/-- In an equilateral triangle `bcd` with `c` to the right of the directed line `b → d`,
the vertex `c` is obtained from `d` by the rotation of angle `-π/3` about `b`. -/
lemma rot_of_equilateral (b c d : ℂ) (h1 : dist c b = dist b d) (h2 : dist c d = dist b d)
    (hccw : ccw b c d) : c - b = wb * (d - b) := by
  have e1 := normSq_of_dist h1
  have e2 := normSq_of_dist h2
  have hor := hccw
  simp only [ccw, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_im,
    map_sub, Complex.conj_re, Complex.conj_im] at e1 e2 hor
  obtain ⟨hX, hY⟩ := rot_real (c.re - b.re) (c.im - b.im) (d.re - b.re) (d.im - b.im)
    (by linear_combination e1) (by linear_combination e2) (by nlinarith [hor])
  apply Complex.ext
  · simp only [Complex.sub_re, Complex.mul_re, Complex.sub_im, wb]
    rw [hX]; ring
  · simp only [Complex.sub_im, Complex.mul_im, Complex.sub_re, wb]
    rw [hY]; ring

/-! ### The perpendicularity and the length equality `IJ = CF` -/

/-- Two points `b`, `e` equidistant from `a` and from `d` lie on the perpendicular
bisector of `ad`; hence `d - a` and `e - b` are orthogonal. -/
lemma hz_of_equidistant {a d b e : ℂ} (hb : dist b a = dist b d) (he : dist e a = dist e d) :
    ((d - a) * (starRingEnd ℂ) (e - b)).re = 0 := by
  have e1 := normSq_of_dist hb
  have e2 := normSq_of_dist he
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    map_sub, Complex.conj_re, Complex.conj_im] at *
  linear_combination (-1 / 2) * e1 + (1 / 2) * e2

lemma cross_zero (u v : ℂ) (hz : (u * (starRingEnd ℂ) v).re = 0) :
    (((1 - wb) * u) * (starRingEnd ℂ) (wb * v)).re
      + ((wb * u) * (starRingEnd ℂ) ((1 - wb) * v)).re = 0 := by
  simp only [Complex.mul_re, Complex.mul_im, map_mul, map_sub, map_one, Complex.conj_re,
    Complex.conj_im, wb, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im] at *
  linear_combination ((1 - Real.sqrt 3 * Real.sqrt 3) / 2) * hz

lemma normSq_key (u v : ℂ) (hz : (u * (starRingEnd ℂ) v).re = 0) :
    Complex.normSq ((1 - wb) * u + wb * v) = Complex.normSq (wb * u - (1 - wb) * v) := by
  rw [Complex.normSq_add, Complex.normSq_sub, Complex.normSq_mul, Complex.normSq_mul,
    Complex.normSq_mul, Complex.normSq_mul, normSq_wb, normSq_one_sub_wb]
  linarith [cross_zero u v hz]

/-! ### The key geometric lemma -/

lemma key_ccw (A B C D E F G H : ℂ)
    (hccwC : ccw B C D) (hccwF : ccw E F A)
    (hCB : dist C B = dist B D) (hCD : dist C D = dist B D)
    (hFE : dist F E = dist E A) (hFA : dist F A = dist E A)
    (hB : dist B A = dist B D) (hE : dist E A = dist E D) :
    dist C F ≤ dist A G + dist G B + dist G H + dist D H + dist H E := by
  -- nondegeneracy
  have hBD : B ≠ D := by
    intro h
    have hc := hccwC
    rw [ccw, ← h] at hc
    simp at hc
  have hEA : E ≠ A := by
    intro h
    have hc := hccwF
    rw [ccw, ← h] at hc
    simp at hc
  have hABne : A ≠ B := by
    intro h
    apply hBD
    have h0 : dist B D = 0 := by rw [← hB, ← h, dist_self]
    have := dist_eq_zero.mp h0
    exact this
  have hDEne : D ≠ E := by
    intro h
    apply hEA
    have h0 : dist E A = 0 := by rw [hE, ← h, dist_self]
    exact (dist_eq_zero.mp h0).symm ▸ rfl
  -- the two erected equilateral triangles
  have hCrot : C - B = wb * (D - B) := rot_of_equilateral B C D hCB hCD hccwC
  have hFrot : F - E = wb * (A - E) := rot_of_equilateral E F A hFE hFA hccwF
  -- the apexes of the equilateral triangles on `AB` and on `DE`
  set I : ℂ := A + wb * (B - A) with hI
  set J : ℂ := D + wb * (E - D) with hJ
  have hz : ((D - A) * (starRingEnd ℂ) (E - B)).re = 0 := hz_of_equidistant hB hE
  -- the crucial length equality `IJ = CF`
  have hIJ : dist I J = dist C F := by
    have hJI : J - I = (1 - wb) * (D - A) + wb * (E - B) := by rw [hI, hJ]; ring
    have hCF : C - F = wb * (D - A) - (1 - wb) * (E - B) := by linear_combination hCrot - hFrot
    have hns : Complex.normSq (J - I) = Complex.normSq (C - F) := by
      rw [hJI, hCF]; exact normSq_key _ _ hz
    rw [Complex.dist_eq, Complex.dist_eq, norm_sub_rev I J]
    exact norm_eq_of_normSq_eq hns
  -- assemble
  have h1 : dist G I ≤ dist G A + dist G B := dist_apex_le A B G hABne
  have h2 : dist H J ≤ dist H D + dist H E := dist_apex_le D E H hDEne
  have h3 : dist I J ≤ dist I G + dist G H + dist H J := by
    calc dist I J ≤ dist I H + dist H J := dist_triangle _ _ _
      _ ≤ dist I G + dist G H + dist H J := by
          have := dist_triangle I G H
          linarith
  rw [← hIJ]
  have e1 : dist I G = dist G I := dist_comm _ _
  have e2 : dist G A = dist A G := dist_comm _ _
  have e3 : dist H D = dist D H := dist_comm _ _
  linarith [h1, h2, h3]

/-! ### Reduction of the reversed orientation by conjugation -/

lemma dist_conj (z w : ℂ) : dist ((starRingEnd ℂ) z) ((starRingEnd ℂ) w) = dist z w := by
  simp only [Complex.dist_eq, ← map_sub, RCLike.norm_conj]

lemma ccw_conj {p q r : ℂ} (h : ccw r q p) :
    ccw ((starRingEnd ℂ) p) ((starRingEnd ℂ) q) ((starRingEnd ℂ) r) := by
  simp only [ccw, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.conj_re,
    Complex.conj_im] at *
  nlinarith [h]

/-! ### The main theorem -/

/-- **IMO 1995, Problem 5.**  Let `ABCDEF` be a convex hexagon with `AB = BC = CD` and
`DE = EF = FA`, such that `∠BCD = ∠EFA = π/3`.  If `G` and `H` are points in the interior
of the hexagon with `∠AGB = ∠DHE = 2π/3`, then `AG + GB + GH + DH + HE ≥ CF`.

The hypotheses `hG`, `hH`, `hGmem`, `hHmem` concerning the two points `G` and `H` are part
of the original statement and are kept here, but the inequality in fact holds for arbitrary
points `G` and `H`, so they are not used in the proof. -/
theorem imo1995_p5 (A B C D E F G H : ℂ)
    (hconv : ConvexHexagon A B C D E F)
    (hAB : dist A B = dist B C) (hBC : dist B C = dist C D)
    (hDE : dist D E = dist E F) (hEF : dist E F = dist F A)
    (hangC : EuclideanGeometry.angle B C D = π / 3)
    (hangF : EuclideanGeometry.angle E F A = π / 3)
    (hG : EuclideanGeometry.angle A G B = 2 * π / 3)
    (hH : EuclideanGeometry.angle D H E = 2 * π / 3)
    (hGmem : G ∈ interior (convexHull ℝ ({A, B, C, D, E, F} : Set ℂ)))
    (hHmem : H ∈ interior (convexHull ℝ ({A, B, C, D, E, F} : Set ℂ))) :
    dist C F ≤ dist A G + dist G B + dist G H + dist D H + dist H E := by
  -- the triangles `BCD` and `EFA` are equilateral
  have hBD : dist B D = dist B C := by
    have hlaw := EuclideanGeometry.law_cos B C D
    rw [hangC, Real.cos_pi_div_three] at hlaw
    have hDC : dist D C = dist B C := by rw [dist_comm D C, ← hBC]
    rw [hDC] at hlaw
    nlinarith [hlaw, dist_nonneg (x := B) (y := D), dist_nonneg (x := B) (y := C)]
  have hEAeq : dist E A = dist E F := by
    have hlaw := EuclideanGeometry.law_cos E F A
    rw [hangF, Real.cos_pi_div_three] at hlaw
    have hAF : dist A F = dist E F := by rw [dist_comm A F, ← hEF]
    rw [hAF] at hlaw
    nlinarith [hlaw, dist_nonneg (x := E) (y := A), dist_nonneg (x := E) (y := F)]
  -- distance bookkeeping
  have hCB : dist C B = dist B D := by rw [hBD, dist_comm C B]
  have hCD : dist C D = dist B D := by rw [hBD, ← hBC]
  have hFE : dist F E = dist E A := by rw [hEAeq, dist_comm F E]
  have hFA : dist F A = dist E A := by rw [hEAeq, ← hEF]
  have hBA : dist B A = dist B D := by rw [hBD, dist_comm B A, hAB]
  have hED : dist E A = dist E D := by rw [hEAeq, dist_comm E D, hDE]
  rcases hconv with hccw | hcw
  · exact key_ccw A B C D E F G H hccw.2.1 hccw.2.2.2.2.1 hCB hCD hFE hFA hBA hED
  · -- reversed orientation: conjugate everything
    obtain ⟨-, -, hDCB, -, -, hAFE⟩ := hcw
    have hkey := key_ccw ((starRingEnd ℂ) A) ((starRingEnd ℂ) B) ((starRingEnd ℂ) C)
      ((starRingEnd ℂ) D) ((starRingEnd ℂ) E) ((starRingEnd ℂ) F) ((starRingEnd ℂ) G)
      ((starRingEnd ℂ) H)
      (ccw_conj hDCB) (ccw_conj hAFE)
      (by rw [dist_conj, dist_conj]; exact hCB) (by rw [dist_conj, dist_conj]; exact hCD)
      (by rw [dist_conj, dist_conj]; exact hFE) (by rw [dist_conj, dist_conj]; exact hFA)
      (by rw [dist_conj, dist_conj]; exact hBA) (by rw [dist_conj, dist_conj]; exact hED)
    simpa only [dist_conj] using hkey

end IMO1995P5
