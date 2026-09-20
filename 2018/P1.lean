import Mathlib

/-!
# IMO 2018, Problem 1

Let `Γ` be the circumcircle of acute triangle `ABC`. Points `D` and `E` are on segments `AB`
and `AC` respectively such that `AD = AE`. The perpendicular bisectors of `BD` and `CE`
intersect the minor arcs `AB` and `AC` of `Γ` at points `F` and `G` respectively.
Prove that lines `DE` and `FG` are either parallel or they are the same line.

## Formalization

The plane is `ℝ × ℝ` with the standard inner product `dotp` and the scalar cross product
`crossp`. "`DE` and `FG` are parallel or equal" is exactly `crossp (E - D) (G - F) = 0`: the
direction vectors are proportional, which covers both alternatives of the conclusion and is
the standard way to state "parallel or the same line" without a case split.

Hypotheses, in order:

* `O` is the centre and `R` the radius of `Γ`, and `A, B, C, F, G` all lie on `Γ`.
* `crossp (B - A) (C - A) ≠ 0` says `A, B, C` are not collinear, i.e. `ABC` is a genuine
  triangle (so `Γ` really is its circumcircle).
* `D = A + l • (B - A)` with `0 < l < 1`, and `E = A + m • (C - A)` with `0 < m < 1`, say that
  `D` is interior to segment `AB` and `E` is interior to segment `AC`.
* `dotp (D - A) (D - A) = dotp (E - A) (E - A)` is `AD = AE` (equal squared lengths; both
  lengths are nonnegative, so this is equivalent).
* `dotp (F - B) (F - B) = dotp (F - D) (F - D)` says `FB = FD`, i.e. `F` lies on the
  perpendicular bisector of `BD`; likewise `GC = GE` for `CE`.
* `crossp (B - A) (F - A) * crossp (B - A) (C - A) < 0` says `F` and `C` are strictly on
  opposite sides of line `AB`, i.e. `F` lies on the open arc `AB` not containing `C`.
  Likewise `G` lies on the arc `AC` not containing `B`.

The last pair is how "minor arc" is encoded. For an *acute* triangle the arc `AB` not
containing `C` subtends the central angle `2∠C < 180°`, so it is precisely the minor arc; the
two readings agree exactly under the problem's acuteness assumption. Stated this way the proof
needs no further use of acuteness, which matches the remark on the AoPS page that the argument
survives for an obtuse triangle.

## Proof

Place the circumcentre at the origin and write `P = B - A`, `Q = C - A`, `p = |P|²`, `q = |Q|²`.

1. Since `|A| = |B| = R` one gets `2 A·P + p = 0`. Feeding this into `FB = FD` and cancelling
   the factor `l - 1 ≠ 0` gives `2 F·P = l·p`, and symmetrically `2 G·Q = m·q`. (Geometrically:
   the perpendicular bisector of `BD` is the perpendicular to `AB` through the midpoint of `BD`.)
2. `AD = AE` is `l²p = m²q`.
3. Write `X = crossp P F`, `Y = crossp Q G`, `k = crossp P A`, `k' = crossp Q A`. The
   two-dimensional Lagrange identity turns `|F| = |A| = R` into
   `X² = pR² - l²p²/4` and `k² = pR² - p²/4`, and similarly for `Y, k'`. Since `l, m < 1` this
   gives `X² > k²` and `Y² > k'²`.
4. The arc hypotheses say `(X - k)·cr < 0` and `(Y - k')·cr > 0` where `cr = crossp P Q`.
   Combined with step 3 — writing `2X = (X - k) + (X + k)` and noting both summands have the
   same sign — they force `X·cr < 0 < Y·cr`, so `X` and `Y` have opposite signs.
5. Steps 2 and 3 give `m²Y² = l²X²` outright, and the sign information of step 4 then upgrades
   this to `mY + lX = 0`; together with `l²p = m²q` this yields `mqX + lpY = 0`.
6. Resolving `F` along the basis `(P, Pᗮ)` and `G` along `(Q, Qᗮ)` expresses `crossp Q F` and
   `crossp P G`, and expanding `crossp (E - D) (G - F)` multiplied by `pq` leaves exactly
   `pq(mY + lX) - (P·Q)(mqX + lpY)`, which vanishes by step 5.

No square roots are needed anywhere: every intermediate quantity is a polynomial in the
coordinates, `l`, `m` and `R`.
-/

namespace Imo2018P1

/-- The Euclidean plane. -/
abbrev Pt := ℝ × ℝ

/-- The standard inner product. -/
def dotp (x y : Pt) : ℝ := x.1 * y.1 + x.2 * y.2

/-- The scalar cross product. `crossp x y = 0` exactly when `x` and `y` are parallel. -/
def crossp (x y : Pt) : ℝ := x.1 * y.2 - x.2 * y.1

/-- Lagrange's identity in the plane: `|y|²|x|² = (x·y)² + (y × x)²`. -/
lemma lagrange (x y : Pt) : dotp y y * dotp x x = dotp x y ^ 2 + crossp y x ^ 2 := by
  simp only [dotp, crossp]; ring

/-- Resolving `x` along the orthogonal basis `(y, yᗮ)` and taking `crossp z ·`. -/
lemma cross_decomp (x y z : Pt) :
    dotp y y * crossp z x = dotp x y * crossp z y + crossp y x * dotp z y := by
  simp only [dotp, crossp]; ring

/-- The scalar heart of the problem. -/
lemma core {p q l m X Y cr k k' R : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hl0 : 0 < l) (hl1 : l < 1) (hm0 : 0 < m) (hm1 : m < 1)
    (hS : l ^ 2 * p = m ^ 2 * q)
    (hX2 : X ^ 2 = p * R ^ 2 - l ^ 2 * p ^ 2 / 4)
    (hY2 : Y ^ 2 = q * R ^ 2 - m ^ 2 * q ^ 2 / 4)
    (hk2 : k ^ 2 = p * R ^ 2 - p ^ 2 / 4)
    (hk'2 : k' ^ 2 = q * R ^ 2 - q ^ 2 / 4)
    (hcr : cr ≠ 0)
    (hAF : (X - k) * cr < 0)
    (hAG : 0 < (Y - k') * cr) :
    m * Y + l * X = 0 ∧ m * q * X + l * p * Y = 0 := by
  -- `X² > k²` and `Y² > k'²`, because `l, m < 1`.
  have hXk : 0 < (X - k) * (X + k) := by
    have hfac : (X - k) * (X + k) = p ^ 2 * (1 - l ^ 2) / 4 := by
      linear_combination hX2 - hk2
    have h1 : 0 < 1 - l ^ 2 := by nlinarith
    have h2 : 0 < p * p := mul_pos hp hp
    rw [hfac]
    nlinarith [mul_pos h2 h1]
  have hYk : 0 < (Y - k') * (Y + k') := by
    have hfac : (Y - k') * (Y + k') = q ^ 2 * (1 - m ^ 2) / 4 := by
      linear_combination hY2 - hk'2
    have h1 : 0 < 1 - m ^ 2 := by nlinarith
    have h2 : 0 < q * q := mul_pos hq hq
    rw [hfac]
    nlinarith [mul_pos h2 h1]
  -- Hence `X` and `Y` sit on opposite sides.
  have hXcr : X * cr < 0 := by
    rcases lt_or_gt_of_ne hcr with h | h
    · have h1 : 0 < X - k := by nlinarith
      have h2 : 0 < X + k := by
        by_contra hcon
        have hc : X + k ≤ 0 := not_lt.mp hcon
        nlinarith
      exact mul_neg_of_pos_of_neg (by linarith) h
    · have h1 : X - k < 0 := by nlinarith
      have h2 : X + k < 0 := by
        by_contra hcon
        have hc : 0 ≤ X + k := not_lt.mp hcon
        nlinarith
      exact mul_neg_of_neg_of_pos (by linarith) h
  have hYcr : 0 < Y * cr := by
    rcases lt_or_gt_of_ne hcr with h | h
    · have h1 : Y - k' < 0 := by nlinarith
      have h2 : Y + k' < 0 := by
        by_contra hcon
        have hc : 0 ≤ Y + k' := not_lt.mp hcon
        nlinarith
      exact mul_pos_of_neg_of_neg (by linarith) h
    · have h1 : 0 < Y - k' := by nlinarith
      have h2 : 0 < Y + k' := by
        by_contra hcon
        have hc : Y + k' ≤ 0 := not_lt.mp hcon
        nlinarith
      exact mul_pos (by linarith) h
  have hcr2 : 0 < cr ^ 2 := by positivity
  have hXY : X * Y < 0 := by
    have h3 : X * cr * (Y * cr) < 0 := mul_neg_of_neg_of_pos hXcr hYcr
    nlinarith
  -- `m²Y² = l²X²` is pure algebra.
  have hmsq : m ^ 2 * Y ^ 2 = l ^ 2 * X ^ 2 := by
    rw [hX2, hY2]
    linear_combination (-(R ^ 2) + (m ^ 2 * q + l ^ 2 * p) / 4) * hS
  have hMY : m * Y + l * X = 0 := by
    have hfac : (m * Y + l * X) * (m * Y - l * X) = 0 := by linear_combination hmsq
    rcases mul_eq_zero.mp hfac with h | h
    · exact h
    · exfalso
      have hlm : 0 < l * m := mul_pos hl0 hm0
      nlinarith [sq_nonneg (l * X)]
  refine ⟨hMY, ?_⟩
  have h4 : m * (m * q * X + l * p * Y) = 0 := by
    linear_combination (l * p) * hMY - X * hS
  rcases mul_eq_zero.mp h4 with h | h
  · exact absurd h (ne_of_gt hm0)
  · exact h

/-- **IMO 2018 P1.** `DE` and `FG` are parallel (possibly equal). -/
theorem imo2018_p1
    (O A B C D E F G : Pt) (R l m : ℝ)
    -- `A`, `B`, `C`, `F`, `G` lie on the circle `Γ` of centre `O` and radius `R`
    (hA : dotp (A - O) (A - O) = R ^ 2)
    (hB : dotp (B - O) (B - O) = R ^ 2)
    (hC : dotp (C - O) (C - O) = R ^ 2)
    (hFc : dotp (F - O) (F - O) = R ^ 2)
    (hGc : dotp (G - O) (G - O) = R ^ 2)
    -- `ABC` is a genuine triangle
    (hABC : crossp (B - A) (C - A) ≠ 0)
    -- `D` is interior to `AB`, `E` is interior to `AC`
    (hl0 : 0 < l) (hl1 : l < 1) (hm0 : 0 < m) (hm1 : m < 1)
    (hD : D = A + l • (B - A)) (hE : E = A + m • (C - A))
    -- `AD = AE`
    (hDE : dotp (D - A) (D - A) = dotp (E - A) (E - A))
    -- `F` on the perpendicular bisector of `BD`, `G` on that of `CE`
    (hFbd : dotp (F - B) (F - B) = dotp (F - D) (F - D))
    (hGce : dotp (G - C) (G - C) = dotp (G - E) (G - E))
    -- `F` on the arc `AB` away from `C`, `G` on the arc `AC` away from `B`
    (harcF : crossp (B - A) (F - A) * crossp (B - A) (C - A) < 0)
    (harcG : crossp (C - A) (G - A) * crossp (C - A) (B - A) < 0) :
    crossp (E - D) (G - F) = 0 := by
  have hD1 : D.1 = A.1 + l * (B.1 - A.1) := by rw [hD]; simp
  have hD2 : D.2 = A.2 + l * (B.2 - A.2) := by rw [hD]; simp
  have hE1 : E.1 = A.1 + m * (C.1 - A.1) := by rw [hE]; simp
  have hE2 : E.2 = A.2 + m * (C.2 - A.2) := by rw [hE]; simp
  -- The two squared side lengths are positive.
  have hp : 0 < dotp (B - A) (B - A) := by
    rcases (show (0:ℝ) ≤ dotp (B - A) (B - A) by
        simp only [dotp, Prod.fst_sub, Prod.snd_sub]
        nlinarith [sq_nonneg (B.1 - A.1), sq_nonneg (B.2 - A.2)]).lt_or_eq with h | h
    · exact h
    · exfalso
      apply hABC
      have hx : (B.1 - A.1) ^ 2 + (B.2 - A.2) ^ 2 = 0 := by
        simp only [dotp, Prod.fst_sub, Prod.snd_sub] at h
        linear_combination -h
      have h2 := (add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _)).mp hx
      have hb1 : B.1 - A.1 = 0 := by
        have := h2.1; exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
      have hb2 : B.2 - A.2 = 0 := by
        have := h2.2; exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
      simp only [crossp, Prod.fst_sub, Prod.snd_sub]
      linear_combination (C.2 - A.2) * hb1 - (C.1 - A.1) * hb2
  have hq : 0 < dotp (C - A) (C - A) := by
    rcases (show (0:ℝ) ≤ dotp (C - A) (C - A) by
        simp only [dotp, Prod.fst_sub, Prod.snd_sub]
        nlinarith [sq_nonneg (C.1 - A.1), sq_nonneg (C.2 - A.2)]).lt_or_eq with h | h
    · exact h
    · exfalso
      apply hABC
      have hx : (C.1 - A.1) ^ 2 + (C.2 - A.2) ^ 2 = 0 := by
        simp only [dotp, Prod.fst_sub, Prod.snd_sub] at h
        linear_combination -h
      have h2 := (add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _)).mp hx
      have hc1 : C.1 - A.1 = 0 := by
        have := h2.1; exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
      have hc2 : C.2 - A.2 = 0 := by
        have := h2.2; exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
      simp only [crossp, Prod.fst_sub, Prod.snd_sub]
      linear_combination (B.1 - A.1) * hc2 - (B.2 - A.2) * hc1
  -- `2 A·P + |P|² = 0` and its analogue for `Q`.
  have hAP : dotp (A - O) (B - A) = -(dotp (B - A) (B - A)) / 2 := by
    simp only [dotp, Prod.fst_sub, Prod.snd_sub] at hA hB ⊢
    linear_combination (hB - hA) / 2
  have hAQ : dotp (A - O) (C - A) = -(dotp (C - A) (C - A)) / 2 := by
    simp only [dotp, Prod.fst_sub, Prod.snd_sub] at hA hC ⊢
    linear_combination (hC - hA) / 2
  -- The perpendicular-bisector conditions, cleaned up.
  have hFP : dotp (F - O) (B - A) = l * dotp (B - A) (B - A) / 2 := by
    have hne : l - 1 ≠ 0 := ne_of_lt (by linarith)
    have key : (l - 1) * (2 * dotp (F - O) (B - A) - l * dotp (B - A) (B - A)) = 0 := by
      simp only [dotp, Prod.fst_sub, Prod.snd_sub] at hA hB hFbd ⊢
      rw [hD1, hD2] at hFbd
      linear_combination hFbd + (1 - l) * hA - (1 - l) * hB
    rcases mul_eq_zero.mp key with h | h
    · exact absurd h hne
    · linarith
  have hGQ : dotp (G - O) (C - A) = m * dotp (C - A) (C - A) / 2 := by
    have hne : m - 1 ≠ 0 := ne_of_lt (by linarith)
    have key : (m - 1) * (2 * dotp (G - O) (C - A) - m * dotp (C - A) (C - A)) = 0 := by
      simp only [dotp, Prod.fst_sub, Prod.snd_sub] at hA hC hGce ⊢
      rw [hE1, hE2] at hGce
      linear_combination hGce + (1 - m) * hA - (1 - m) * hC
    rcases mul_eq_zero.mp key with h | h
    · exact absurd h hne
    · linarith
  -- `AD = AE`.
  have hS : l ^ 2 * dotp (B - A) (B - A) = m ^ 2 * dotp (C - A) (C - A) := by
    simp only [dotp, Prod.fst_sub, Prod.snd_sub] at hDE ⊢
    rw [hD1, hD2, hE1, hE2] at hDE
    linear_combination hDE
  -- Lagrange gives the four square identities.
  have hX2 : crossp (B - A) (F - O) ^ 2
      = dotp (B - A) (B - A) * R ^ 2 - l ^ 2 * dotp (B - A) (B - A) ^ 2 / 4 := by
    have h := lagrange (F - O) (B - A)
    rw [hFc, hFP] at h
    linear_combination -h
  have hY2 : crossp (C - A) (G - O) ^ 2
      = dotp (C - A) (C - A) * R ^ 2 - m ^ 2 * dotp (C - A) (C - A) ^ 2 / 4 := by
    have h := lagrange (G - O) (C - A)
    rw [hGc, hGQ] at h
    linear_combination -h
  have hk2 : crossp (B - A) (A - O) ^ 2
      = dotp (B - A) (B - A) * R ^ 2 - dotp (B - A) (B - A) ^ 2 / 4 := by
    have h := lagrange (A - O) (B - A)
    rw [hA, hAP] at h
    linear_combination -h
  have hk'2 : crossp (C - A) (A - O) ^ 2
      = dotp (C - A) (C - A) * R ^ 2 - dotp (C - A) (C - A) ^ 2 / 4 := by
    have h := lagrange (A - O) (C - A)
    rw [hA, hAQ] at h
    linear_combination -h
  -- Rewrite the two arc hypotheses in terms of `X, Y, k, k'`.
  have hcrossFA : crossp (B - A) (F - A)
      = crossp (B - A) (F - O) - crossp (B - A) (A - O) := by
    simp only [crossp, Prod.fst_sub, Prod.snd_sub]; ring
  have hcrossGA : crossp (C - A) (G - A)
      = crossp (C - A) (G - O) - crossp (C - A) (A - O) := by
    simp only [crossp, Prod.fst_sub, Prod.snd_sub]; ring
  have hCBA : crossp (C - A) (B - A) = -crossp (B - A) (C - A) := by
    simp only [crossp, Prod.fst_sub, Prod.snd_sub]; ring
  rw [hcrossFA] at harcF
  rw [hcrossGA, hCBA] at harcG
  have harcG' : 0 < (crossp (C - A) (G - O) - crossp (C - A) (A - O))
      * crossp (B - A) (C - A) := by nlinarith [harcG]
  -- The scalar core.
  obtain ⟨hMY, hMX⟩ := core hp hq hl0 hl1 hm0 hm1 hS hX2 hY2 hk2 hk'2 hABC harcF harcG'
  -- Resolve `F` along `(P, Pᗮ)` and `G` along `(Q, Qᗮ)`.
  have hn : dotp (C - A) (B - A) = dotp (B - A) (C - A) := by
    simp only [dotp, Prod.fst_sub, Prod.snd_sub]; ring
  have e1 : dotp (B - A) (B - A) * crossp (C - A) (F - O)
      = l * dotp (B - A) (B - A) / 2 * -crossp (B - A) (C - A)
        + crossp (B - A) (F - O) * dotp (B - A) (C - A) := by
    have h := cross_decomp (F - O) (B - A) (C - A)
    rw [hFP, hCBA, hn] at h
    exact h
  have e2 : dotp (C - A) (C - A) * crossp (B - A) (G - O)
      = m * dotp (C - A) (C - A) / 2 * crossp (B - A) (C - A)
        + crossp (C - A) (G - O) * dotp (B - A) (C - A) := by
    have h := cross_decomp (G - O) (C - A) (B - A)
    rw [hGQ] at h
    exact h
  -- Expand the goal and finish.
  have expand : crossp (E - D) (G - F)
      = m * crossp (C - A) (G - O) - m * crossp (C - A) (F - O)
        - l * crossp (B - A) (G - O) + l * crossp (B - A) (F - O) := by
    simp only [crossp, Prod.fst_sub, Prod.snd_sub]
    rw [hD1, hD2, hE1, hE2]
    ring
  have final : dotp (B - A) (B - A) * dotp (C - A) (C - A) * crossp (E - D) (G - F) = 0 := by
    rw [expand]
    linear_combination (dotp (B - A) (B - A) * dotp (C - A) (C - A)) * hMY
      - (m * dotp (C - A) (C - A)) * e1 - (l * dotp (B - A) (B - A)) * e2
      - dotp (B - A) (C - A) * hMX
  rcases mul_eq_zero.mp final with h | h
  · exact absurd h (ne_of_gt (mul_pos hp hq))
  · exact h

end Imo2018P1
