import Mathlib

/-!
# IMO 1969 Problem 5

Given `n > 4` points in the plane, no three of which are collinear, there are at least
`C(n-3, 2) = (n-3)(n-4)/2` convex quadrilaterals whose vertices are four of the given points.

A "convex quadrilateral" with vertices among the points is formalized as a four-element set of
points in *convex position*: none of the four points lies in the convex hull of the other three.

The proof formalized here is the double-counting one: every five points in general position
contain four in convex position (`exists_convex_quadrilateral`, Klein's theorem), each convex
quadrilateral lies in at most `n - 4` five-element subsets, and `C(n,5) ≥ C(n-3,2) * (n-4)`
for `n ≥ 5`.

Remark on the argument accompanying the problem statement (choose a triangle `ABC` and, for each
pair `E, F` of the remaining points, produce a convex quadrilateral using `E`, `F` and two of
`A, B, C`): that step can fail. For the five points `(0,0)`, `(10,0)`, `(4,4)`, `(5,10)`, `(6,4)`
(no three collinear) the only convex quadrilateral is `(0,0), (10,0), (4,4), (6,4)`, so for the
pair `E = (4,4)`, `F = (5,10)` no such quadrilateral exists, whichever triangle is chosen.
-/

open scoped Classical

namespace IMO1969P5

/-- Points of the plane. -/
abbrev Pt := ℝ × ℝ

/-- Twice the signed area of the triangle `a b c`; it vanishes exactly when `a`, `b`, `c` are
collinear. -/
def det3 (a b c : Pt) : ℝ := (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)

/-- No three distinct points of `S` are collinear. -/
def NoThreeCollinear (S : Finset Pt) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → a ≠ c → b ≠ c → det3 a b c ≠ 0

/-- A finite set of points is in *convex position* if none of its points lies in the convex hull
of the remaining ones. -/
def InConvexPosition (T : Finset Pt) : Prop :=
  ∀ p ∈ T, p ∉ convexHull ℝ ((T.erase p : Finset Pt) : Set Pt)

/-! ### Convex hulls of triples -/

theorem mem_convexHull_triple_iff (x y z p : Pt) :
    p ∈ convexHull ℝ ({x, y, z} : Set Pt) ↔
      ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = 1 ∧ a • x + b • y + c • z = p := by
  constructor
  · intro hp
    rw [convexHull_insert (by simp), convexHull_pair, mem_convexJoin] at hp
    obtain ⟨u, hu, v, hv, hseg⟩ := hp
    simp only [Set.mem_singleton_iff] at hu
    subst hu
    rw [segment_eq_image] at hseg hv
    obtain ⟨s, ⟨hs0, hs1⟩, rfl⟩ := hv
    obtain ⟨t, ⟨ht0, ht1⟩, hp⟩ := hseg
    refine ⟨1 - t, t * (1 - s), t * s, by linarith, by nlinarith, by nlinarith, by ring, ?_⟩
    rw [← hp]; module
  · rintro ⟨a, b, c, ha, hb, hc, habc, rfl⟩
    have hx : x ∈ convexHull ℝ ({x, y, z} : Set Pt) := subset_convexHull ℝ _ (by simp)
    have hy : y ∈ convexHull ℝ ({x, y, z} : Set Pt) := subset_convexHull ℝ _ (by simp)
    have hz : z ∈ convexHull ℝ ({x, y, z} : Set Pt) := subset_convexHull ℝ _ (by simp)
    have hcv := convex_convexHull ℝ ({x, y, z} : Set Pt)
    have := hcv.sum_mem (t := (Finset.univ : Finset (Fin 3))) (w := ![a, b, c]) (z := ![x, y, z])
      (by intro i _; fin_cases i <;> simpa) (by simp [Fin.sum_univ_three]; linarith)
      (by intro i _; fin_cases i <;> simpa)
    simpa [Fin.sum_univ_three] using this

/-! ### Basic determinant identities -/

theorem det3_self_left (a b : Pt) : det3 a a b = 0 := by unfold det3; ring

theorem det3_self_right (a b : Pt) : det3 a b b = 0 := by unfold det3; ring

theorem det3_self_outer (a b : Pt) : det3 a b a = 0 := by unfold det3; ring

/-- `det3` is affine in its middle argument. -/
theorem det3_mid_comb (u w p q r : Pt) (a b c : ℝ) (h : a + b + c = 1) :
    det3 u (a • p + b • q + c • r) w =
      a * det3 u p w + b * det3 u q w + c * det3 u r w := by
  have hc : c = 1 - a - b := by linarith
  subst hc
  simp only [det3, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- `det3` is affine in its last argument. -/
theorem det3_last_comb (u w p q r : Pt) (a b c : ℝ) (h : a + b + c = 1) :
    det3 u w (a • p + b • q + c • r) =
      a * det3 u w p + b * det3 u w q + c * det3 u w r := by
  have hc : c = 1 - a - b := by linarith
  subst hc
  simp only [det3, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-! ### The key geometric lemmas -/

/-- If `d` lies in the triangle `x y z` and `d ≠ y`, then the barycentric coordinate of `d`
with respect to `y` is `< 1`. -/
theorem bary_mid_lt_one {x y z d : Pt} (hd : d ∈ convexHull ℝ ({x, y, z} : Set Pt))
    (hdy : d ≠ y) : ∃ b : ℝ, 0 ≤ b ∧ b < 1 ∧ det3 x d z = b * det3 x y z := by
  rw [mem_convexHull_triple_iff] at hd
  obtain ⟨a, b, c, ha, hb, hc, habc, rfl⟩ := hd
  refine ⟨b, hb, ?_, ?_⟩
  · rcases lt_or_eq_of_le (show b ≤ 1 by linarith) with h | h
    · exact h
    · exfalso
      apply hdy
      have ha0 : a = 0 := by linarith
      have hc0 : c = 0 := by linarith
      subst ha0; subst hc0; subst h; simp
  · rw [det3_mid_comb x z x y z a b c habc, det3_self_left, det3_self_right]
    ring

/-- A vertex of a triangle is not in the convex hull of the opposite side together with two
points of the triangle. -/
theorem not_mem_hull_of_bary {x y z d w : Pt} (hxyz : det3 x y z ≠ 0)
    (hd : d ∈ convexHull ℝ ({x, y, z} : Set Pt)) (hw : w ∈ convexHull ℝ ({x, y, z} : Set Pt))
    (hdy : d ≠ y) (hwy : w ≠ y) : y ∉ convexHull ℝ ({z, d, w} : Set Pt) := by
  obtain ⟨b1, hb1, hb1', hb1e⟩ := bary_mid_lt_one hd hdy
  obtain ⟨b2, hb2, hb2', hb2e⟩ := bary_mid_lt_one hw hwy
  intro hmem
  rw [mem_convexHull_triple_iff] at hmem
  obtain ⟨p, q, r, hp, hq, hr, hpqr, heq⟩ := hmem
  have key : det3 x y z = p * det3 x z z + q * det3 x d z + r * det3 x w z := by
    conv_lhs => rw [← heq]
    rw [det3_mid_comb x z z d w p q r hpqr]
  rw [det3_self_right, hb1e, hb2e] at key
  have h0 : det3 x y z * (1 - (q * b1 + r * b2)) = 0 := by linear_combination key
  have key2 : (1 : ℝ) = q * b1 + r * b2 := by
    rcases mul_eq_zero.1 h0 with h | h
    · exact absurd h hxyz
    · linarith
  rcases eq_or_lt_of_le hq with h | h
  · rcases eq_or_lt_of_le hr with h2 | h2
    · rw [← h, ← h2] at key2; simp at key2
    · nlinarith
  · nlinarith

/-- If `y` and `z` are strictly on the same side of the line through `d` and `w`, then no point
`u` of that line lies in the hull of `y`, `z` and another point `v` of the line (unless `u = v`). -/
theorem not_mem_hull_of_side {d w y z u v : Pt} (hside : 0 < det3 d w y * det3 d w z)
    (hu : det3 d w u = 0) (hv : det3 d w v = 0) (huv : u ≠ v) :
    u ∉ convexHull ℝ ({y, z, v} : Set Pt) := by
  intro hmem
  rw [mem_convexHull_triple_iff] at hmem
  obtain ⟨a, b, c, ha, hb, hc, habc, heq⟩ := hmem
  have key : det3 d w u = a * det3 d w y + b * det3 d w z + c * det3 d w v := by
    rw [← heq, det3_last_comb d w y z v a b c habc]
  rw [hu, hv] at key
  have hab : a = 0 ∧ b = 0 := by
    rcases lt_trichotomy (det3 d w y) 0 with h | h | h
    · have hz : det3 d w z < 0 := by nlinarith
      constructor <;> nlinarith
    · exfalso; rw [h] at hside; simp at hside
    · have hz : 0 < det3 d w z := by nlinarith
      constructor <;> nlinarith
  obtain ⟨ha0, hb0⟩ := hab
  apply huv
  rw [← heq, ha0, hb0]
  have hc1 : c = 1 := by linarith
  rw [hc1]; simp

/-- Criterion for four points to be in convex position. -/
theorem inConvexPosition_four {p q r s : Pt} (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s)
    (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s)
    (h1 : p ∉ convexHull ℝ ({q, r, s} : Set Pt)) (h2 : q ∉ convexHull ℝ ({p, r, s} : Set Pt))
    (h3 : r ∉ convexHull ℝ ({p, q, s} : Set Pt)) (h4 : s ∉ convexHull ℝ ({p, q, r} : Set Pt)) :
    InConvexPosition {p, q, r, s} := by
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · convert h1 using 3
    ext t; simp; aesop
  · convert h2 using 3
    ext t; simp; aesop
  · convert h3 using 3
    ext t; simp; aesop
  · convert h4 using 3
    ext t; simp; aesop

/-- Two points inside a triangle, together with two vertices of the triangle lying strictly on
the same side of the line through them, form a convex quadrilateral. -/
theorem convexPosition_of_two_inside {x y z d w : Pt} (hxyz : det3 x y z ≠ 0)
    (hd : d ∈ convexHull ℝ ({x, y, z} : Set Pt)) (hw : w ∈ convexHull ℝ ({x, y, z} : Set Pt))
    (hyz : y ≠ z) (hdw : d ≠ w) (hdy : d ≠ y) (hdz : d ≠ z) (hwy : w ≠ y) (hwz : w ≠ z)
    (hside : 0 < det3 d w y * det3 d w z) :
    InConvexPosition {y, z, d, w} := by
  have hswap : ({x, z, y} : Set Pt) = {x, y, z} := by
    ext t; simp; tauto
  have hxzy : det3 x z y ≠ 0 := by
    intro h; apply hxyz; unfold det3 at h ⊢; linarith
  refine inConvexPosition_four hyz (Ne.symm hdy) (Ne.symm hwy) (Ne.symm hdz) (Ne.symm hwz) hdw
    (not_mem_hull_of_bary hxyz hd hw hdy hwy) ?_
    (not_mem_hull_of_side hside (det3_self_outer d w) (det3_self_right d w) hdw)
    (not_mem_hull_of_side hside (det3_self_right d w) (det3_self_outer d w) (Ne.symm hdw))
  exact not_mem_hull_of_bary hxzy (by rw [hswap]; exact hd) (by rw [hswap]; exact hw) hdz hwz

/-- If `d` and `w` are each in the convex hull of the rest, then each lies in the convex hull of
the common part. -/
theorem mem_hull_of_mutual {s : Set Pt} {d w : Pt} (hs : s.Nonempty)
    (hd : d ∈ convexHull ℝ (insert w s)) (hw : w ∈ convexHull ℝ (insert d s)) (hne : d ≠ w) :
    d ∈ convexHull ℝ s := by
  rw [convexHull_insert hs, mem_convexJoin] at hd hw
  obtain ⟨w', hw', u, hu, hdseg⟩ := hd
  obtain ⟨d', hd', v, hv, hwseg⟩ := hw
  simp only [Set.mem_singleton_iff] at hw' hd'
  rw [hw'] at hdseg
  rw [hd'] at hwseg
  rw [segment_eq_image] at hdseg hwseg
  obtain ⟨α, ⟨hα0, hα1⟩, hdeq⟩ := hdseg
  obtain ⟨β, ⟨hβ0, hβ1⟩, hweq⟩ := hwseg
  simp only at hdeq hweq
  by_cases hab : (1 - α) * (1 - β) = 1
  · exfalso
    apply hne
    have hα : α = 0 := by nlinarith
    have hβ : β = 0 := by nlinarith
    rw [← hdeq, hα]; simp [← hweq, hβ]
  · have h1 : d = (1 - α) • ((1 - β) • d + β • v) + α • u := by rw [hweq, hdeq]
    have key : (1 - (1-α)*(1-β)) • d = ((1-α)*β) • v + α • u := by
      linear_combination (norm := module) h1
    have ht : (1 - (1-α)*(1-β)) ≠ 0 := fun h => hab (by linarith)
    have htpos : 0 < 1 - (1-α)*(1-β) := by
      rcases lt_or_eq_of_le (show (1-α)*(1-β) ≤ 1 by nlinarith) with h | h
      · linarith
      · exact absurd h hab
    have hdeq2 : d = ((1-α)*β / (1 - (1-α)*(1-β))) • v + (α / (1 - (1-α)*(1-β))) • u := by
      have h2 := congrArg (fun p : Pt => (1 - (1-α)*(1-β))⁻¹ • p) key
      simp only [smul_smul, smul_add] at h2
      rw [inv_mul_cancel₀ ht, one_smul] at h2
      rw [h2]
      congr 1 <;> rw [div_eq_inv_mul]
    rw [hdeq2]
    exact convex_convexHull ℝ s hv hu (div_nonneg (by nlinarith) htpos.le)
      (div_nonneg hα0 htpos.le) (by field_simp; ring)

/-! ### Klein's theorem: five points contain a convex quadrilateral -/

/-- Among three nonzero reals, two have the same sign. -/
theorem three_signs {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    0 < a * b ∨ 0 < a * c ∨ 0 < b * c := by
  rcases lt_or_gt_of_ne ha with h | h <;> rcases lt_or_gt_of_ne hb with h' | h' <;>
    rcases lt_or_gt_of_ne hc with h'' | h'' <;>
    first
      | (left; nlinarith)
      | (right; left; nlinarith)
      | (right; right; nlinarith)

theorem exists_convex_quadrilateral {T : Finset Pt} (hT : T.card = 5)
    (hgen : NoThreeCollinear T) : ∃ Q ⊆ T, Q.card = 4 ∧ InConvexPosition Q := by
  set V := T.filter (fun p => p ∉ convexHull ℝ ((T.erase p : Finset Pt) : Set Pt)) with hVdef
  by_cases hV : 4 ≤ V.card
  · obtain ⟨Q, hQV, hQcard⟩ := Finset.exists_subset_card_eq hV
    have hQT : Q ⊆ T := hQV.trans (Finset.filter_subset _ _)
    refine ⟨Q, hQT, hQcard, ?_⟩
    intro p hp hmem
    have hpV := hQV hp
    rw [hVdef, Finset.mem_filter] at hpV
    refine hpV.2 (convexHull_mono ?_ hmem)
    exact_mod_cast Finset.coe_subset.2 (Finset.erase_subset_erase p hQT)
  · push Not at hV
    have hsub : V ⊆ T := Finset.filter_subset _ _
    have h2 : 2 ≤ (T \ V).card := by
      have h := Finset.card_sdiff_of_subset hsub
      omega
    obtain ⟨P, hPsub, hPcard⟩ := Finset.exists_subset_card_eq h2
    obtain ⟨d, w, hdw, rfl⟩ := Finset.card_eq_two.1 hPcard
    have hdmem : d ∈ T \ V := hPsub (by simp)
    have hwmem : w ∈ T \ V := hPsub (by simp)
    rw [Finset.mem_sdiff] at hdmem hwmem
    have hdT : d ∈ T := hdmem.1
    have hwT : w ∈ T := hwmem.1
    have hdwT : ({d, w} : Finset Pt) ⊆ T := by
      intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl <;> assumption
    have hdhull : d ∈ convexHull ℝ ((T.erase d : Finset Pt) : Set Pt) := by
      by_contra h
      exact hdmem.2 (by rw [hVdef, Finset.mem_filter]; exact ⟨hdT, h⟩)
    have hwhull : w ∈ convexHull ℝ ((T.erase w : Finset Pt) : Set Pt) := by
      by_contra h
      exact hwmem.2 (by rw [hVdef, Finset.mem_filter]; exact ⟨hwT, h⟩)
    have hUcard : (T \ ({d, w} : Finset Pt)).card = 3 := by
      rw [Finset.card_sdiff_of_subset hdwT, hT, Finset.card_insert_of_notMem (by simp [hdw]),
        Finset.card_singleton]
    obtain ⟨x, y, z, hxy, hxz, hyz, hUeq⟩ := Finset.card_eq_three.1 hUcard
    have hmemU : ∀ t : Pt, t ∈ ({x, y, z} : Finset Pt) → t ∈ T ∧ t ≠ d ∧ t ≠ w := by
      intro t ht
      rw [← hUeq, Finset.mem_sdiff] at ht
      refine ⟨ht.1, ?_, ?_⟩ <;> (intro h; apply ht.2; simp [h])
    obtain ⟨hxT, hxd, hxw⟩ := hmemU x (by simp)
    obtain ⟨hyT, hyd, hyw⟩ := hmemU y (by simp)
    obtain ⟨hzT, hzd, hzw⟩ := hmemU z (by simp)
    have hTeq : T = ({x, y, z, d, w} : Finset Pt) := by
      have h := Finset.sdiff_union_of_subset hdwT
      rw [hUeq] at h
      rw [← h]
      ext t; simp; tauto
    have hed : ((T.erase d : Finset Pt) : Set Pt) = insert w ({x, y, z} : Set Pt) := by
      rw [hTeq]; ext t
      simp only [Finset.coe_erase, Finset.coe_insert, Finset.coe_singleton, Set.mem_sdiff,
        Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨h, h'⟩; rcases h with rfl | rfl | rfl | rfl | rfl <;> tauto
      · rintro (rfl | rfl | rfl | rfl)
        · exact ⟨by tauto, Ne.symm hdw⟩
        · exact ⟨by tauto, hxd⟩
        · exact ⟨by tauto, hyd⟩
        · exact ⟨by tauto, hzd⟩
    have hew : ((T.erase w : Finset Pt) : Set Pt) = insert d ({x, y, z} : Set Pt) := by
      rw [hTeq]; ext t
      simp only [Finset.coe_erase, Finset.coe_insert, Finset.coe_singleton, Set.mem_sdiff,
        Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨h, h'⟩; rcases h with rfl | rfl | rfl | rfl | rfl <;> tauto
      · rintro (rfl | rfl | rfl | rfl)
        · exact ⟨by tauto, hdw⟩
        · exact ⟨by tauto, hxw⟩
        · exact ⟨by tauto, hyw⟩
        · exact ⟨by tauto, hzw⟩
    rw [hed] at hdhull
    rw [hew] at hwhull
    have hne : ({x, y, z} : Set Pt).Nonempty := ⟨x, by simp⟩
    have hdin : d ∈ convexHull ℝ ({x, y, z} : Set Pt) := mem_hull_of_mutual hne hdhull hwhull hdw
    have hwin : w ∈ convexHull ℝ ({x, y, z} : Set Pt) :=
      mem_hull_of_mutual hne hwhull hdhull (Ne.symm hdw)
    have main : ∀ p q r : Pt, ({p, q, r} : Set Pt) = ({x, y, z} : Set Pt) → p ∈ T → q ∈ T →
        r ∈ T → p ≠ q → p ≠ r → q ≠ r → q ≠ d → q ≠ w → r ≠ d → r ≠ w →
        0 < det3 d w q * det3 d w r → ∃ Q ⊆ T, Q.card = 4 ∧ InConvexPosition Q := by
      intro p q r hset hp hq hr hpq hpr hqr hqd hqw hrd hrw hside
      have hdet : det3 p q r ≠ 0 := hgen p hp q hq r hr hpq hpr hqr
      have hd' : d ∈ convexHull ℝ ({p, q, r} : Set Pt) := by rw [hset]; exact hdin
      have hw' : w ∈ convexHull ℝ ({p, q, r} : Set Pt) := by rw [hset]; exact hwin
      refine ⟨{q, r, d, w}, ?_, ?_, convexPosition_of_two_inside hdet hd' hw' hqr hdw
        (Ne.symm hqd) (Ne.symm hrd) (Ne.symm hqw) (Ne.symm hrw) hside⟩
      · intro t ht
        simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl | rfl <;> assumption
      · rw [Finset.card_insert_of_notMem (by simp [hqr, hqd, hqw]),
          Finset.card_insert_of_notMem (by simp [hrd, hrw]),
          Finset.card_insert_of_notMem (by simp [hdw]), Finset.card_singleton]
    have hsx : det3 d w x ≠ 0 := hgen d hdT w hwT x hxT hdw (Ne.symm hxd) (Ne.symm hxw)
    have hsy : det3 d w y ≠ 0 := hgen d hdT w hwT y hyT hdw (Ne.symm hyd) (Ne.symm hyw)
    have hsz : det3 d w z ≠ 0 := hgen d hdT w hwT z hzT hdw (Ne.symm hzd) (Ne.symm hzw)
    rcases three_signs hsx hsy hsz with h | h | h
    · exact main z x y (by ext t; simp; tauto) hzT hxT hyT (Ne.symm hxz) (Ne.symm hyz) hxy
        hxd hxw hyd hyw h
    · exact main y x z (by ext t; simp; tauto) hyT hxT hzT (Ne.symm hxy) hyz hxz
        hxd hxw hzd hzw h
    · exact main x y z rfl hxT hyT hzT hxy hxz hyz hyd hyw hzd hzw h

/-! ### Counting -/

theorem choose_bound (n : ℕ) (hn : 5 ≤ n) : (n - 3).choose 2 * (n - 4) ≤ n.choose 5 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  have e1 : 5 + m - 3 = m + 2 := by omega
  have e2 : 5 + m - 4 = m + 1 := by omega
  have e3 : 5 + m = m + 5 := by omega
  rw [e1, e2, e3]
  have h1 : (m + 5).descFactorial 5 = Nat.factorial 5 * (m + 5).choose 5 :=
    Nat.descFactorial_eq_factorial_mul_choose _ _
  have h2 : (m + 2).descFactorial 2 = Nat.factorial 2 * (m + 2).choose 2 :=
    Nat.descFactorial_eq_factorial_mul_choose _ _
  simp [Nat.descFactorial, Nat.factorial] at h1 h2
  have base : 60 * (m + 1) ≤ (m + 5) * (m + 4) * (m + 3) := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · norm_num
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
      ring_nf
      nlinarith [Nat.zero_le k]
  have key := Nat.mul_le_mul_right ((m + 2) * (m + 1)) base
  nlinarith [h1, h2, key]

/-- **IMO 1969, Problem 5.** Given `n > 4` points in the plane, no three collinear, there are at
least `(n-3).choose 2 = (n-3)(n-4)/2` four-element subsets in convex position, i.e. convex
quadrilaterals with vertices among the given points. -/
theorem imo1969_p5 (S : Finset Pt) (hcard : 4 < S.card) (hgen : NoThreeCollinear S) :
    (S.card - 3).choose 2 ≤ ((S.powersetCard 4).filter InConvexPosition).card := by
  set quads := (S.powersetCard 4).filter InConvexPosition with hquads
  have hdc : (S.powersetCard 5).card * 1 ≤ quads.card * (S.card - 4) := by
    refine Finset.card_mul_le_card_mul (fun T Q => Q ⊆ T) ?_ ?_
    · intro T hT
      rw [Finset.mem_powersetCard] at hT
      have hgenT : NoThreeCollinear T := by
        intro a ha b hb c hc hab hac hbc
        exact hgen a (hT.1 ha) b (hT.1 hb) c (hT.1 hc) hab hac hbc
      obtain ⟨Q, hQT, hQcard, hQconv⟩ := exists_convex_quadrilateral hT.2 hgenT
      rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, Finset.card_pos]
      refine ⟨Q, ?_⟩
      rw [Finset.mem_bipartiteAbove]
      refine ⟨?_, hQT⟩
      rw [hquads, Finset.mem_filter, Finset.mem_powersetCard]
      exact ⟨⟨hQT.trans hT.1, hQcard⟩, hQconv⟩
    · intro Q hQ
      rw [hquads, Finset.mem_filter, Finset.mem_powersetCard] at hQ
      obtain ⟨⟨hQS, hQcard⟩, -⟩ := hQ
      have hle : (Finset.bipartiteBelow (fun T Q => Q ⊆ T) (S.powersetCard 5) Q).card ≤
          ((S \ Q).powersetCard 1).card := by
        refine Finset.card_le_card_of_injOn (fun T => T \ Q) ?_ ?_
        · intro T hT
          simp only [Finset.mem_coe] at hT
          rw [Finset.mem_bipartiteBelow, Finset.mem_powersetCard] at hT
          obtain ⟨⟨hTS, hTcard⟩, hQT⟩ := hT
          simp only [Finset.mem_coe, Finset.mem_powersetCard]
          refine ⟨Finset.sdiff_subset_sdiff hTS (le_refl Q), ?_⟩
          rw [Finset.card_sdiff_of_subset hQT, hTcard, hQcard]
        · intro T1 h1 T2 h2 heq
          simp only [Finset.mem_coe] at h1 h2
          rw [Finset.mem_bipartiteBelow] at h1 h2
          have e1 := Finset.union_sdiff_of_subset h1.2
          have e2 := Finset.union_sdiff_of_subset h2.2
          simp only at heq
          rw [← e1, ← e2, heq]
      calc (Finset.bipartiteBelow (fun T Q => Q ⊆ T) (S.powersetCard 5) Q).card
          ≤ ((S \ Q).powersetCard 1).card := hle
        _ = S.card - 4 := by
            rw [Finset.card_powersetCard, Finset.card_sdiff_of_subset hQS, hQcard,
              Nat.choose_one_right]
  rw [Finset.card_powersetCard, mul_one] at hdc
  have hb := choose_bound S.card hcard
  have hpos : 0 < S.card - 4 := by omega
  exact Nat.le_of_mul_le_mul_right (le_trans hb hdc) hpos

/-! ### Sanity checks on the notion of convex position -/

/-- The four vertices of a unit square are in convex position. -/
theorem square_inConvexPosition :
    InConvexPosition {((0 : ℝ), (0 : ℝ)), (1, 0), (1, 1), (0, 1)} := by
  refine inConvexPosition_four (by norm_num [Prod.ext_iff]) (by norm_num [Prod.ext_iff])
    (by norm_num [Prod.ext_iff]) (by norm_num [Prod.ext_iff]) (by norm_num [Prod.ext_iff])
    (by norm_num [Prod.ext_iff]) ?_ ?_ ?_ ?_ <;>
  · intro h
    rw [mem_convexHull_triple_iff] at h
    obtain ⟨a, b, c, ha, hb, hc, habc, heq⟩ := h
    rw [Prod.ext_iff] at heq
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at heq
    obtain ⟨h1, h2⟩ := heq
    norm_num at h1 h2
    linarith

/-- A triangle together with an interior point is not in convex position. -/
theorem not_inConvexPosition_triangle_with_interior_point :
    ¬ InConvexPosition {((0 : ℝ), (0 : ℝ)), (4, 0), (0, 4), (1, 1)} := by
  intro h
  refine h (1, 1) (by simp) ?_
  have herase : ((({((0 : ℝ), (0 : ℝ)), (4, 0), (0, 4), (1, 1)} : Finset Pt).erase (1, 1) :
      Finset Pt) : Set Pt) = {((0 : ℝ), (0 : ℝ)), (4, 0), (0, 4)} := by
    ext t
    simp only [Finset.coe_erase, Finset.coe_insert, Finset.coe_singleton, Set.mem_sdiff,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨ht, ht'⟩; rcases ht with rfl | rfl | rfl | rfl <;> tauto
    · rintro (rfl | rfl | rfl) <;> exact ⟨by tauto, by norm_num [Prod.ext_iff]⟩
  rw [herase, mem_convexHull_triple_iff]
  exact ⟨1 / 2, 1 / 4, 1 / 4, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num [Prod.ext_iff]⟩

end IMO1969P5
