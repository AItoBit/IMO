import Mathlib

/-!
# IMO 1969, Problem 5

Given `n > 4` points in the plane, no three collinear, there are at least
`(n - 3).choose 2 = (n-3)(n-4)/2` convex quadrilaterals whose vertices are four of the
given points.

A *convex quadrilateral* is formalised as a 4-element set of points in convex position:
no one of the four points lies in the convex hull of the other three.
-/

namespace Imo1969P5

open Finset

/-- Twice the signed area of the triangle `a b c` in the plane. -/
def det (a b c : ℝ × ℝ) : ℝ := (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)

/-- A finite set of points is in general position if no three distinct points are collinear. -/
def GenPos (S : Finset (ℝ × ℝ)) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → a ≠ c → b ≠ c → det a b c ≠ 0

/-- A four-element set of points in convex position: no point lies in the convex hull of
the other three.  These are exactly the vertex sets of convex quadrilaterals. -/
def ConvexQuad (s : Finset (ℝ × ℝ)) : Prop :=
  s.card = 4 ∧ ∀ x ∈ s, x ∉ convexHull ℝ (↑(s.erase x) : Set (ℝ × ℝ))

/-! ### Basic determinant identities -/

lemma det_cycl (a b c : ℝ × ℝ) : det a b c = det b c a := by simp only [det]; ring

lemma det_self_left (a b : ℝ × ℝ) : det a a b = 0 := by simp only [det]; ring

lemma det_self_mid (a b : ℝ × ℝ) : det a b a = 0 := by simp only [det]; ring

/-- The three (unnormalised) barycentric coordinates of `y` with respect to `a, b, c`
sum to `det a b c`. -/
lemma det_bary_sum (a b c y : ℝ × ℝ) :
    det y b c + det y c a + det y a b = det a b c := by simp only [det]; ring

/-- `x ↦ D * det x q r` is an affine function of `x`. -/
lemma det_affine (q r : ℝ × ℝ) (D : ℝ) (z : ℝ × ℝ) :
    D * det z q r =
      (D * (q.2 - r.2)) * z.1 + (D * (r.1 - q.1)) * z.2 + D * (q.1 * r.2 - q.2 * r.1) := by
  simp only [det]; ring

/-! ### Separation lemmas -/

/-- If an affine functional of the form `x ↦ D * det x q r` is strictly smaller on `s` than
at `y`, then `y` is not in the convex hull of `s`. -/
lemma notMem_convexHull_of_det_lt {s : Set (ℝ × ℝ)} {y q r : ℝ × ℝ} {D : ℝ}
    (hs : ∀ x ∈ s, D * det x q r < D * det y q r) : y ∉ convexHull ℝ s := by
  intro hy
  have hconv : Convex ℝ {z : ℝ × ℝ |
      (D * (q.2 - r.2)) * z.1 + (D * (r.1 - q.1)) * z.2 <
        (D * (q.2 - r.2)) * y.1 + (D * (r.1 - q.1)) * y.2} := by
    apply convex_halfSpace_lt
    constructor
    · intro z w; simp; ring
    · intro c z; simp; ring
  have hsub : s ⊆ {z : ℝ × ℝ |
      (D * (q.2 - r.2)) * z.1 + (D * (r.1 - q.1)) * z.2 <
        (D * (q.2 - r.2)) * y.1 + (D * (r.1 - q.1)) * y.2} := by
    intro x hx
    have h := hs x hx
    rw [det_affine q r D x, det_affine q r D y] at h
    simpa using by linarith
  have := convexHull_min hsub hconv hy
  simp only [Set.mem_setOf_eq] at this
  linarith

/-- A lower bound on an affine functional `x ↦ D * det x q r` valid on `s` propagates to the
convex hull of `s`. -/
lemma le_det_of_mem_convexHull {s : Set (ℝ × ℝ)} {y q r : ℝ × ℝ} {D t : ℝ}
    (hs : ∀ x ∈ s, t ≤ D * det x q r) (hy : y ∈ convexHull ℝ s) : t ≤ D * det y q r := by
  by_contra hlt
  push_neg at hlt
  exact notMem_convexHull_of_det_lt (D := -D) (q := q) (r := r)
    (fun x hx => by have := hs x hx; nlinarith) hy

private lemma mul_nonneg_of_eq {u v : ℝ} (h : u = v) : 0 ≤ u * v := by subst h; exact mul_self_nonneg u

/-- The unnormalised barycentric coordinates of a point of the triangle `a b c` have the same
sign as `det a b c`. -/
lemma bary_nonneg {a b c y : ℝ × ℝ} (hy : y ∈ convexHull ℝ ({a, b, c} : Set (ℝ × ℝ))) :
    0 ≤ det a b c * det y b c ∧ 0 ≤ det a b c * det y c a ∧ 0 ≤ det a b c * det y a b := by
  refine ⟨?_, ?_, ?_⟩
  · refine le_det_of_mem_convexHull (q := b) (r := c) ?_ hy
    rintro x (rfl | rfl | rfl)
    · exact mul_self_nonneg _
    · rw [det_self_left]; simp
    · rw [det_self_mid]; simp
  · refine le_det_of_mem_convexHull (q := c) (r := a) ?_ hy
    rintro x (rfl | rfl | rfl)
    · rw [det_self_mid]; simp
    · exact mul_nonneg_of_eq (by simp only [det]; ring)
    · rw [det_self_left]; simp
  · refine le_det_of_mem_convexHull (q := a) (r := b) ?_ hy
    rintro x (rfl | rfl | rfl)
    · rw [det_self_left]; simp
    · rw [det_self_mid]; simp
    · exact mul_nonneg_of_eq (by simp only [det]; ring)

/-- Sign bookkeeping: if `0 ≤ F * B`, `0 ≤ F * (-A)` and `0 < A * B`, then `F = 0`. -/
private lemma eq_zero_of_side {F A B : ℝ} (k1 : 0 ≤ F * B) (k2 : 0 ≤ F * (-A))
    (h : 0 < A * B) : F = 0 := by
  rcases lt_trichotomy F 0 with hF | hF | hF
  · have hB : B ≤ 0 := by nlinarith
    have hA : 0 ≤ A := by nlinarith
    nlinarith
  · exact hF
  · have hB : 0 ≤ B := by nlinarith
    have hA : A ≤ 0 := by nlinarith
    nlinarith

/-! ### Building convex quadrilaterals -/

lemma convexQuad_mk {a b c d : ℝ × ℝ} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (h1 : a ∉ convexHull ℝ ({b, c, d} : Set (ℝ × ℝ)))
    (h2 : b ∉ convexHull ℝ ({a, c, d} : Set (ℝ × ℝ)))
    (h3 : c ∉ convexHull ℝ ({a, b, d} : Set (ℝ × ℝ)))
    (h4 : d ∉ convexHull ℝ ({a, b, c} : Set (ℝ × ℝ))) :
    ConvexQuad {a, b, c, d} := by
  have ea : ({a, b, c, d} : Finset (ℝ × ℝ)).erase a = {b, c, d} := by
    ext y; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h, h'⟩; tauto
    · rintro (rfl | rfl | rfl) <;> aesop
  have eb : ({a, b, c, d} : Finset (ℝ × ℝ)).erase b = {a, c, d} := by
    ext y; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h, h'⟩; tauto
    · rintro (rfl | rfl | rfl) <;> aesop
  have ec : ({a, b, c, d} : Finset (ℝ × ℝ)).erase c = {a, b, d} := by
    ext y; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h, h'⟩; tauto
    · rintro (rfl | rfl | rfl) <;> aesop
  have ed : ({a, b, c, d} : Finset (ℝ × ℝ)).erase d = {a, b, c} := by
    ext y; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h, h'⟩; tauto
    · rintro (rfl | rfl | rfl) <;> aesop
  refine ⟨by rw [Finset.card_eq_four]; exact ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, rfl⟩, ?_⟩
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · rw [ea]; simpa using h1
  · rw [eb]; simpa using h2
  · rw [ec]; simpa using h3
  · rw [ed]; simpa using h4

/-! ### Two points inside a triangle -/

/-- The main geometric step: if `u` and `v` lie in the triangle `p q r`, with `p` and `q`
strictly on the same side of the line `uv`, then `p, q, u, v` are in convex position. -/
lemma convexQuad_of_same_side {p q r u v : ℝ × ℝ}
    (hpu : p ≠ u) (hpv : p ≠ v) (hqu : q ≠ u) (hqv : q ≠ v) (hpq : p ≠ q) (huv : u ≠ v)
    (hD : det p q r ≠ 0) (hpqu : det p q u ≠ 0) (hpqv : det p q v ≠ 0)
    (hpur : det p u r ≠ 0) (hpvr : det p v r ≠ 0)
    (huqr : det u q r ≠ 0) (hvqr : det v q r ≠ 0)
    (hu : u ∈ convexHull ℝ ({p, q, r} : Set (ℝ × ℝ)))
    (hv : v ∈ convexHull ℝ ({p, q, r} : Set (ℝ × ℝ)))
    (hside : 0 < det u v p * det u v q) :
    ConvexQuad {p, q, u, v} := by
  obtain ⟨hu1, hu2, hu3⟩ := bary_nonneg hu
  obtain ⟨hv1, hv2, hv3⟩ := bary_nonneg hv
  set D := det p q r with hDdef
  have hDD : 0 < D * D := mul_self_pos.mpr hD
  have hurp : det u r p ≠ 0 := by rw [← det_cycl]; exact hpur
  have hvrp : det v r p ≠ 0 := by rw [← det_cycl]; exact hpvr
  have hu2' : 0 < D * det u r p := hu2.lt_of_ne' (mul_ne_zero hD hurp)
  have hv2' : 0 < D * det v r p := hv2.lt_of_ne' (mul_ne_zero hD hvrp)
  have hu1' : 0 < D * det u q r := hu1.lt_of_ne' (mul_ne_zero hD huqr)
  have hv1' : 0 < D * det v q r := hv1.lt_of_ne' (mul_ne_zero hD hvqr)
  have hsumu : D * det u q r + D * det u r p + D * det u p q = D * D := by
    calc D * det u q r + D * det u r p + D * det u p q
        = D * (det u q r + det u r p + det u p q) := by ring
      _ = D * D := by rw [det_bary_sum]
  have hsumv : D * det v q r + D * det v r p + D * det v p q = D * D := by
    calc D * det v q r + D * det v r p + D * det v p q
        = D * (det v q r + det v r p + det v p q) := by ring
      _ = D * D := by rw [det_bary_sum]
  have h1 : p ∉ convexHull ℝ ({q, u, v} : Set (ℝ × ℝ)) := by
    refine notMem_convexHull_of_det_lt (D := D) (q := q) (r := r) ?_
    rintro x (rfl | rfl | rfl)
    · rw [det_self_left]; rw [← hDdef]; linarith
    · rw [← hDdef]; linarith
    · rw [← hDdef]; linarith
  have h2 : q ∉ convexHull ℝ ({p, u, v} : Set (ℝ × ℝ)) := by
    have hqrp : det q r p = D := by rw [hDdef]; simp only [det]; ring
    refine notMem_convexHull_of_det_lt (D := D) (q := r) (r := p) ?_
    rintro x (rfl | rfl | rfl)
    · rw [det_self_mid, hqrp]; linarith
    · rw [hqrp]; linarith
    · rw [hqrp]; linarith
  have h3 : u ∉ convexHull ℝ ({p, q, v} : Set (ℝ × ℝ)) := by
    intro hmem
    obtain ⟨k1, k2, _⟩ := bary_nonneg hmem
    have e1 : det u q v = -det u v q := by simp only [det]; ring
    rw [e1] at k1
    exact hpqv (eq_zero_of_side k2 k1 (by linarith [mul_comm (det u v p) (det u v q)]))
  have h4 : v ∉ convexHull ℝ ({p, q, u} : Set (ℝ × ℝ)) := by
    intro hmem
    obtain ⟨k1, k2, _⟩ := bary_nonneg hmem
    have e1 : det v q u = det u v q := by simp only [det]; ring
    have e2 : det v u p = -det u v p := by simp only [det]; ring
    rw [e1] at k1; rw [e2] at k2
    exact hpqu (eq_zero_of_side k1 k2 hside)
  exact convexQuad_mk hpq hpu hpv hqu hqv huv h1 h2 h3 h4

/-- Among three nonzero reals, two have the same sign. -/
private lemma exists_same_sign {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    0 < a * b ∨ 0 < b * c ∨ 0 < a * c := by
  rcases lt_or_gt_of_ne ha with h | h <;> rcases lt_or_gt_of_ne hb with h' | h' <;>
    rcases lt_or_gt_of_ne hc with h'' | h'' <;>
    first
      | (left; nlinarith)
      | (right; left; nlinarith)
      | (right; right; nlinarith)

/-- Given a triangle `p q r` containing `u` and `v`, with `p` and `q` on the same side of the
line `uv`, the four points `p, q, u, v` form a convex quadrilateral inside `S`. -/
private lemma quad_of_pair {S : Finset (ℝ × ℝ)} (hgp : GenPos S) {p q r u v : ℝ × ℝ}
    (hp : p ∈ S) (hq : q ∈ S) (hr : r ∈ S) (hu : u ∈ S) (hv : v ∈ S)
    (hpq : p ≠ q) (hpr : p ≠ r) (hpu : p ≠ u) (hpv : p ≠ v) (hqr : q ≠ r) (hqu : q ≠ u)
    (hqv : q ≠ v) (hru : r ≠ u) (hrv : r ≠ v) (huv : u ≠ v)
    (hmu : u ∈ convexHull ℝ ({p, q, r} : Set (ℝ × ℝ)))
    (hmv : v ∈ convexHull ℝ ({p, q, r} : Set (ℝ × ℝ)))
    (hside : 0 < det u v p * det u v q) : ∃ w ⊆ S, ConvexQuad w := by
  refine ⟨{p, q, u, v}, ?_, convexQuad_of_same_side hpu hpv hqu hqv hpq huv
    (hgp p hp q hq r hr hpq hpr hqr) (hgp p hp q hq u hu hpq hpu hqu)
    (hgp p hp q hq v hv hpq hpv hqv) (hgp p hp u hu r hr hpu hpr hru.symm)
    (hgp p hp v hv r hr hpv hpr hrv.symm) (hgp u hu q hq r hr hqu.symm hru.symm hqr)
    (hgp v hv q hq r hr hqv.symm hrv.symm hqr) hmu hmv hside⟩
  intro w hw
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> assumption

/-- If two of the five points lie in the triangle spanned by the other three, then some four
of the five are in convex position. -/
lemma exists_convexQuad_of_two_in_triangle {S : Finset (ℝ × ℝ)} (hgp : GenPos S)
    {x y z u v : ℝ × ℝ} (hx : x ∈ S) (hy : y ∈ S) (hz : z ∈ S) (hu : u ∈ S) (hv : v ∈ S)
    (hxy : x ≠ y) (hxz : x ≠ z) (hxu : x ≠ u) (hxv : x ≠ v) (hyz : y ≠ z) (hyu : y ≠ u)
    (hyv : y ≠ v) (hzu : z ≠ u) (hzv : z ≠ v) (huv : u ≠ v)
    (hmu : u ∈ convexHull ℝ ({x, y, z} : Set (ℝ × ℝ)))
    (hmv : v ∈ convexHull ℝ ({x, y, z} : Set (ℝ × ℝ))) :
    ∃ q ⊆ S, ConvexQuad q := by
  have huvx : det u v x ≠ 0 := hgp u hu v hv x hx huv hxu.symm hxv.symm
  have huvy : det u v y ≠ 0 := hgp u hu v hv y hy huv hyu.symm hyv.symm
  have huvz : det u v z ≠ 0 := hgp u hu v hv z hz huv hzu.symm hzv.symm
  have exy : ({y, z, x} : Set (ℝ × ℝ)) = {x, y, z} := by ext w; simp; tauto
  have exz : ({x, z, y} : Set (ℝ × ℝ)) = {x, y, z} := by ext w; simp; tauto
  rcases exists_same_sign huvx huvy huvz with h | h | h
  · exact quad_of_pair hgp hx hy hz hu hv hxy hxz hxu hxv hyz hyu hyv hzu hzv huv hmu hmv h
  · exact quad_of_pair hgp hy hz hx hu hv hyz hxy.symm hyu hyv hxz.symm hzu hzv hxu hxv huv
      (by rw [exy]; exact hmu) (by rw [exy]; exact hmv) h
  · exact quad_of_pair hgp hx hz hy hu hv hxz hxy hxu hxv hyz.symm hzu hzv hyu hyv huv
      (by rw [exz]; exact hmu) (by rw [exz]; exact hmv) h

/-! ### The Happy Ending theorem for five points -/

/-- If four distinct points are not in convex position, one of them lies in the convex hull of
the other three. -/
lemma exists_mem_hull_of_not_convexQuad {a b c d : ℝ × ℝ} (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) (h : ¬ ConvexQuad {a, b, c, d}) :
    a ∈ convexHull ℝ ({b, c, d} : Set (ℝ × ℝ)) ∨ b ∈ convexHull ℝ ({a, c, d} : Set (ℝ × ℝ)) ∨
      c ∈ convexHull ℝ ({a, b, d} : Set (ℝ × ℝ)) ∨
      d ∈ convexHull ℝ ({a, b, c} : Set (ℝ × ℝ)) := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2, h3, h4⟩ := hcon
  exact h (convexQuad_mk hab hac had hbc hbd hcd h1 h2 h3 h4)

/-- Convex hulls of triangles: if `x` lies in the triangle `y z e`, the triangle `x y z` is
contained in the triangle `y z e`. -/
lemma hull_triple_subset {x y z e : ℝ × ℝ} (hx : x ∈ convexHull ℝ ({y, z, e} : Set (ℝ × ℝ))) :
    convexHull ℝ ({x, y, z} : Set (ℝ × ℝ)) ⊆ convexHull ℝ ({y, z, e} : Set (ℝ × ℝ)) := by
  refine convexHull_min ?_ (convex_convexHull ℝ _)
  rintro w (rfl | rfl | rfl)
  · exact hx
  · exact subset_convexHull ℝ _ (by simp)
  · exact subset_convexHull ℝ _ (by simp)

/-- Second stage of the five point argument: a triangle `x y z` with a further point `w`
inside it, plus a fifth point `e`, always yields a convex quadrilateral. -/
private lemma stage_two {S : Finset (ℝ × ℝ)} (hgp : GenPos S) {x y z w e : ℝ × ℝ}
    (mx : x ∈ S) (my : y ∈ S) (mz : z ∈ S) (mw : w ∈ S) (me : e ∈ S)
    (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w) (hxe : x ≠ e) (hyz : y ≠ z) (hyw : y ≠ w)
    (hye : y ≠ e) (hzw : z ≠ w) (hze : z ≠ e) (hwe : w ≠ e)
    (hw : w ∈ convexHull ℝ ({x, y, z} : Set (ℝ × ℝ))) : ∃ q ⊆ S, ConvexQuad q := by
  by_cases hq : ConvexQuad {x, y, z, e}
  · refine ⟨{x, y, z, e}, ?_, hq⟩
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl <;> assumption
  · have e1 : ({x, y, z} : Set (ℝ × ℝ)) = {y, x, z} := by ext t; simp; tauto
    have e2 : ({x, y, z} : Set (ℝ × ℝ)) = {z, x, y} := by ext t; simp; tauto
    rcases exists_mem_hull_of_not_convexQuad hxy hxz hxe hyz hye hze hq with h | h | h | h
    · exact exists_convexQuad_of_two_in_triangle hgp my mz me mx mw hyz hye hxy.symm hyw hze
        hxz.symm hzw hxe.symm hwe.symm hxw h (hull_triple_subset h hw)
    · exact exists_convexQuad_of_two_in_triangle hgp mx mz me my mw hxz hxe hxy hxw hze
        hyz.symm hzw hye.symm hwe.symm hyw h (hull_triple_subset h (by rw [← e1]; exact hw))
    · exact exists_convexQuad_of_two_in_triangle hgp mx my me mz mw hxy hxe hxz hxw hye
        hyz hyw hze.symm hwe.symm hzw h (hull_triple_subset h (by rw [← e2]; exact hw))
    · exact exists_convexQuad_of_two_in_triangle hgp mx my mz mw me hxy hxz hxw hxe hyz hyw
        hye hzw hze hwe hw h

lemma exists_convexQuad_of_card_five {S : Finset (ℝ × ℝ)} (hcard : S.card = 5)
    (hgp : GenPos S) : ∃ q ⊆ S, ConvexQuad q := by
  classical
  obtain ⟨a, T, haT, rfl, hT⟩ := Finset.card_eq_succ.mp hcard
  obtain ⟨b, c, d, e, hbc, hbd, hbe, hcd, hce, hde, rfl⟩ := Finset.card_eq_four.mp hT
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at haT
  obtain ⟨hab, hac, had, hae⟩ := haT
  replace hab : a ≠ b := hab
  replace hac : a ≠ c := hac
  replace had : a ≠ d := had
  replace hae : a ≠ e := hae
  have ma : a ∈ insert a ({b, c, d, e} : Finset (ℝ × ℝ)) := by simp
  have mb : b ∈ insert a ({b, c, d, e} : Finset (ℝ × ℝ)) := by simp
  have mc : c ∈ insert a ({b, c, d, e} : Finset (ℝ × ℝ)) := by simp
  have md : d ∈ insert a ({b, c, d, e} : Finset (ℝ × ℝ)) := by simp
  have me : e ∈ insert a ({b, c, d, e} : Finset (ℝ × ℝ)) := by simp
  by_cases hq : ConvexQuad {a, b, c, d}
  · refine ⟨{a, b, c, d}, ?_, hq⟩
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht ⊢
    tauto
  · rcases exists_mem_hull_of_not_convexQuad hab hac had hbc hbd hcd hq with h | h | h | h
    · exact stage_two hgp mb mc md ma me hbc hbd hab.symm hbe hcd hac.symm hce had.symm hde
        hae h
    · exact stage_two hgp ma mc md mb me hac had hab hae hcd hbc.symm hce hbd.symm hde hbe h
    · exact stage_two hgp ma mb md mc me hab had hac hae hbd hbc hbe hcd.symm hde hce h
    · exact stage_two hgp ma mb mc md me hab hac had hae hbc hbd hbe hcd hce hde h

/-! ### Counting -/

lemma collinear_of_det_eq_zero {a b c : ℝ × ℝ} (h : det a b c = 0) :
    Collinear ℝ ({a, b, c} : Set (ℝ × ℝ)) := by
  rw [collinear_iff_of_mem (Set.mem_insert a {b, c})]
  have hd : (b.1 - a.1) * (c.2 - a.2) = (b.2 - a.2) * (c.1 - a.1) := by
    simp only [det] at h; linarith
  by_cases hba : b = a
  · refine ⟨c - a, ?_⟩
    rintro p (rfl | rfl | rfl)
    · exact ⟨0, by simp⟩
    · exact ⟨0, by simp [hba]⟩
    · exact ⟨1, by simp⟩
  · have hne : b.1 - a.1 ≠ 0 ∨ b.2 - a.2 ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hba (Prod.ext (by linarith [hc.1]) (by linarith [hc.2]))
    refine ⟨b - a, ?_⟩
    rintro p (rfl | rfl | rfl)
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
    · rcases hne with h1 | h1
      · refine ⟨(p.1 - a.1) / (b.1 - a.1), Prod.ext ?_ ?_⟩ <;>
          simp only [vadd_eq_add, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
            Prod.fst_sub, Prod.snd_sub, smul_eq_mul] <;> field_simp <;> nlinarith [hd]
      · refine ⟨(p.2 - a.2) / (b.2 - a.2), Prod.ext ?_ ?_⟩ <;>
          simp only [vadd_eq_add, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
            Prod.fst_sub, Prod.snd_sub, smul_eq_mul] <;> field_simp <;> nlinarith [hd]

lemma genPos_of_not_collinear {S : Finset (ℝ × ℝ)}
    (h : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → a ≠ c → b ≠ c →
      ¬ Collinear ℝ ({a, b, c} : Set (ℝ × ℝ))) : GenPos S := by
  intro a ha b hb c hc hab hac hbc hd
  exact h a ha b hb c hc hab hac hbc (collinear_of_det_eq_zero hd)

lemma choose_bound (m : ℕ) : (m + 2).choose 2 * (m + 1) ≤ (m + 5).choose 5 := by
  have hdf5 : (m + 5).descFactorial 5 = (m + 5) * (m + 4) * (m + 3) * (m + 2) * (m + 1) := by
    simp [Nat.descFactorial]; ring
  have hdf2 : (m + 2).descFactorial 2 = (m + 2) * (m + 1) := by
    simp [Nat.descFactorial]; ring
  have h5 := Nat.descFactorial_eq_factorial_mul_choose (m + 5) 5
  have h2 := Nat.descFactorial_eq_factorial_mul_choose (m + 2) 2
  rw [hdf5] at h5
  rw [hdf2] at h2
  norm_num [Nat.factorial] at h5 h2
  have hcube : 60 * (m + 1) ≤ (m + 5) * (m + 4) * (m + 3) := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · norm_num
    · have h1 : m * m ≥ m := Nat.le_mul_of_pos_left m hm
      nlinarith
  have key : 120 * ((m + 2).choose 2 * (m + 1)) ≤ 120 * ((m + 5).choose 5) := by
    calc 120 * ((m + 2).choose 2 * (m + 1))
        = (2 * (m + 2).choose 2) * (60 * (m + 1)) := by ring
      _ = ((m + 2) * (m + 1)) * (60 * (m + 1)) := by rw [← h2]
      _ ≤ ((m + 2) * (m + 1)) * ((m + 5) * (m + 4) * (m + 3)) := Nat.mul_le_mul_left _ hcube
      _ = (m + 5) * (m + 4) * (m + 3) * (m + 2) * (m + 1) := by ring
      _ = 120 * ((m + 5).choose 5) := h5
  omega

open scoped Classical in
/-- **IMO 1969, Problem 5.**  Given `n > 4` points in the plane, no three of them collinear,
there are at least `(n-3).choose 2 = (n-3)(n-4)/2` convex quadrilaterals whose vertices are
four of the given points. -/
theorem imo1969_p5 (S : Finset (ℝ × ℝ)) (hcard : 4 < S.card)
    (hgen : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → a ≠ c → b ≠ c →
      ¬ Collinear ℝ ({a, b, c} : Set (ℝ × ℝ))) :
    (S.card - 3).choose 2 ≤ #{q ∈ S.powersetCard 4 | ConvexQuad q} := by
  classical
  have hgp : GenPos S := genPos_of_not_collinear hgen
  obtain ⟨m, hm⟩ : ∃ m, S.card = m + 5 := ⟨S.card - 5, by omega⟩
  -- every 5-element subset contains four points in convex position
  have hex : ∀ T ∈ S.powersetCard 5, ∃ q, q ⊆ T ∧ ConvexQuad q := by
    intro T hT
    rw [Finset.mem_powersetCard] at hT
    obtain ⟨hTS, hT5⟩ := hT
    exact exists_convexQuad_of_card_five hT5
      (fun a ha b hb c hc => hgp a (hTS ha) b (hTS hb) c (hTS hc))
  choose! f hf1 hf2 using hex
  -- the chosen quadrilaterals are counted by the right-hand side
  have himg : (S.powersetCard 5).image f ⊆ {q ∈ S.powersetCard 4 | ConvexQuad q} := by
    intro q hq
    simp only [Finset.mem_image] at hq
    obtain ⟨T, hT, rfl⟩ := hq
    have hTS := (Finset.mem_powersetCard.mp hT).1
    simp only [Finset.mem_filter, Finset.mem_powersetCard]
    exact ⟨⟨(hf1 T hT).trans hTS, (hf2 T hT).1⟩, hf2 T hT⟩
  -- each quadrilateral is chosen by at most `n - 4` five-element subsets
  have hfib : ∀ q ∈ (S.powersetCard 5).image f, #{T ∈ S.powersetCard 5 | f T = q} ≤ m + 1 := by
    intro q hq
    have hsub : {T ∈ S.powersetCard 5 | f T = q} ⊆ (S \ q).image (fun x => insert x q) := by
      intro T hT
      simp only [Finset.mem_filter] at hT
      obtain ⟨hT5, hfq⟩ := hT
      have hqT : q ⊆ T := hfq ▸ hf1 T hT5
      have hq4 : q.card = 4 := hfq ▸ (hf2 T hT5).1
      have hTcard : T.card = 5 := (Finset.mem_powersetCard.mp hT5).2
      obtain ⟨x, hx, hxq⟩ := Finset.exists_eq_insert_iff.mpr ⟨hqT, by omega⟩
      refine Finset.mem_image.mpr ⟨x, ?_, hxq⟩
      have hxT : x ∈ T := hxq ▸ Finset.mem_insert_self x q
      exact Finset.mem_sdiff.mpr ⟨(Finset.mem_powersetCard.mp hT5).1 hxT, hx⟩
    refine le_trans (Finset.card_le_card hsub) (le_trans (Finset.card_image_le) ?_)
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hq
    have hqS : f T ⊆ S := (hf1 T hT).trans (Finset.mem_powersetCard.mp hT).1
    have hq4 : (f T).card = 4 := (hf2 T hT).1
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hqS, hq4, hm]
    omega
  have hle := Finset.card_le_mul_card_image (S.powersetCard 5) (m + 1) hfib
  rw [Finset.card_powersetCard, hm] at hle
  have h2 : #((S.powersetCard 5).image f) ≤ #{q ∈ S.powersetCard 4 | ConvexQuad q} :=
    Finset.card_le_card himg
  have hfinal : (m + 2).choose 2 * (m + 1) ≤ #{q ∈ S.powersetCard 4 | ConvexQuad q} * (m + 1) := by
    calc (m + 2).choose 2 * (m + 1) ≤ (m + 5).choose 5 := choose_bound m
      _ ≤ (m + 1) * #((S.powersetCard 5).image f) := hle
      _ ≤ (m + 1) * #{q ∈ S.powersetCard 4 | ConvexQuad q} := Nat.mul_le_mul_left _ h2
      _ = #{q ∈ S.powersetCard 4 | ConvexQuad q} * (m + 1) := by ring
  have := Nat.le_of_mul_le_mul_right hfinal (by omega)
  rwa [hm, show m + 5 - 3 = m + 2 from by omega]

open scoped Classical in
/-- The same statement with the count written as `(n-3)(n-4)/2`, as in the original problem. -/
theorem imo1969_p5' (S : Finset (ℝ × ℝ)) (hcard : 4 < S.card)
    (hgen : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → a ≠ c → b ≠ c →
      ¬ Collinear ℝ ({a, b, c} : Set (ℝ × ℝ))) :
    (S.card - 3) * (S.card - 4) / 2 ≤ #{q ∈ S.powersetCard 4 | ConvexQuad q} := by
  have h := imo1969_p5 S hcard hgen
  rwa [Nat.choose_two_right, show S.card - 3 - 1 = S.card - 4 from by omega] at h

/-! ### Sanity checks on the formalisation of "convex quadrilateral" -/

/-- The vertices of a unit square do form a convex quadrilateral. -/
example : ConvexQuad {((0 : ℝ), (0 : ℝ)), (1, 0), (1, 1), (0, 1)} := by
  refine convexQuad_mk (by norm_num [Prod.ext_iff]) (by norm_num [Prod.ext_iff])
    (by norm_num [Prod.ext_iff]) (by norm_num [Prod.ext_iff]) (by norm_num [Prod.ext_iff])
    (by norm_num [Prod.ext_iff]) ?_ ?_ ?_ ?_
  · exact notMem_convexHull_of_det_lt (D := 1) (q := (1, 0)) (r := (0, 1))
      (by rintro x (rfl | rfl | rfl) <;> norm_num [det])
  · exact notMem_convexHull_of_det_lt (D := 1) (q := (1, 1)) (r := (0, 0))
      (by rintro x (rfl | rfl | rfl) <;> norm_num [det])
  · exact notMem_convexHull_of_det_lt (D := -1) (q := (1, 0)) (r := (0, 1))
      (by rintro x (rfl | rfl | rfl) <;> norm_num [det])
  · exact notMem_convexHull_of_det_lt (D := -1) (q := (1, 1)) (r := (0, 0))
      (by rintro x (rfl | rfl | rfl) <;> norm_num [det])

/-- A triangle with a fourth point inside it is not a convex quadrilateral. -/
example : ¬ ConvexQuad {((0 : ℝ), (0 : ℝ)), (4, 0), (0, 4), (1, 1)} := by
  rintro ⟨-, h⟩
  have hmem : ((1 : ℝ), (1 : ℝ)) ∈
      convexHull ℝ ({((0 : ℝ), (0 : ℝ)), (4, 0), (0, 4)} : Set (ℝ × ℝ)) := by
    have h1 : ((2 : ℝ), (2 : ℝ)) ∈
        convexHull ℝ ({((0 : ℝ), (0 : ℝ)), (4, 0), (0, 4)} : Set (ℝ × ℝ)) :=
      segment_subset_convexHull (x := ((4 : ℝ), (0 : ℝ))) (y := ((0 : ℝ), (4 : ℝ)))
        (by simp) (by simp)
        ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, by norm_num [Prod.ext_iff]⟩
    refine (convex_convexHull ℝ _).segment_subset
      (x := ((0 : ℝ), (0 : ℝ))) (y := ((2 : ℝ), (2 : ℝ))) (subset_convexHull ℝ _ (by simp)) h1 ?_
    exact ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, by norm_num [Prod.ext_iff]⟩
  refine h (1, 1) (by simp) ?_
  have herase : ({((0 : ℝ), (0 : ℝ)), (4, 0), (0, 4), (1, 1)} : Finset (ℝ × ℝ)).erase (1, 1)
      = {((0 : ℝ), (0 : ℝ)), (4, 0), (0, 4)} := by
    ext y
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hy, h'⟩; tauto
    · rintro (rfl | rfl | rfl) <;> norm_num [Prod.ext_iff]
  rw [herase]
  simpa using hmem

end Imo1969P5
