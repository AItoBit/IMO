import Mathlib

/-!
# IMO 2004, Problem 1

`ABC` is acute with `AB ≠ AC`; the circle with diameter `BC` meets `AB` at `M` and `AC` at `N`;
`O` is the midpoint of `BC`; the bisectors of `∠BAC` and `∠MON` meet at `R`. Show that the
circumcircles of `BMR` and `CNR` meet on the side `BC`.

## Set-up

Coordinates, with `O` at the origin and `BC` the `x`-axis scaled so that `B = (1,0)`,
`C = (-1,0)` and `A = (u,v)`, `v > 0`. This is a genuine WLOG (a choice of Euclidean frame and
of unit). Then:

* `AB ≠ AC` is `u ≠ 0`, and the angle at `A` being acute is `u² + v² - 1 > 0` — exactly the
  statement that `A` lies outside the circle `ω` with diameter `BC`.
* `M` is the second intersection of `AB` with `ω`; since `∠BMC = 90°`, that is the foot of the
  perpendicular from `C` to `AB`, encoded as `M = A + s(B - A)` together with `CM ⊥ AB`.
  Likewise `N = A + t'(C - A)` with `BN ⊥ AC`.
* Since `OM = ON`, the bisector of `∠MON` is the perpendicular bisector of `MN`. So `R` is the
  point of the `A`-bisector equidistant from `M` and `N`.
* `K = (bB + cC)/(b+c)` with `b = AC`, `c = AB` is the foot of the `A`-bisector on `BC`, so `R`
  lies on the line `AK`: `R = A + t(K - A)`.

Concyclicity of four points is the vanishing of the usual determinant, `cyc` below.

## Proof

The AoPS solution's NOTE observes what its main argument does not use: the common point `K` is
the foot of the bisector of `∠BAC`. That turns the whole problem into a power-of-a-point
identity, because `A`, `M`, `B` are collinear and `A`, `R`, `K` are collinear:

  `B, M, R, K` concyclic  ⟺  `AM · AB = AR · AK`.

Writing `P = u² + v² - 1` for the power of `A` with respect to `ω`, the perpendicularity
conditions give `s·AB² = P` and `t'·AC² = P` at once — both are the power of `A`. So everything
reduces to the single identity `t·AK² = P`, after which `cyc_of_pow_eq` finishes both circles.

For `t·AK² = P`: the bisector condition `k(b+c) = b - c` squares to
`u(1 + k²) = k(u² + v² + 1)`, and combining the equidistance `RM = RN` with `s·AB² = t'·AC² = P`
yields `t·AK² = P` after cancelling `P` and `u` — which is where `u ≠ 0`, i.e. `AB ≠ AC`, is
needed. Finally `-1 < k < 1` because `k(b+c) = b - c` with `b, c > 0`, so `K` is interior to `BC`
— the point the NOTE says cost many contestants a mark.
-/

namespace Imo2004P1

/-- Twice the signed area of a triangle. -/
def area2 (a1 a2 b1 b2 c1 c2 : ℝ) : ℝ := a1 * (b2 - c2) + b1 * (c2 - a2) + c1 * (a2 - b2)

/-- The concyclicity determinant of four points: it vanishes exactly when they are concyclic
or collinear. -/
def cyc (a1 a2 b1 b2 c1 c2 d1 d2 : ℝ) : ℝ :=
  (a1 ^ 2 + a2 ^ 2) * area2 b1 b2 c1 c2 d1 d2
  - (b1 ^ 2 + b2 ^ 2) * area2 a1 a2 c1 c2 d1 d2
  + (c1 ^ 2 + c2 ^ 2) * area2 a1 a2 b1 b2 d1 d2
  - (d1 ^ 2 + d2 ^ 2) * area2 a1 a2 b1 b2 c1 c2

/-- Converse power of a point: if `M` is on line `AB`, `R` is on line `AK`, and
`AM · AB = AR · AK`, then `B`, `M`, `R`, `K` are concyclic. -/
theorem cyc_of_pow_eq (a1 a2 b1 b2 k1 k2 m1 m2 r1 r2 s t : ℝ)
    (hm1 : m1 = a1 + s * (b1 - a1)) (hm2 : m2 = a2 + s * (b2 - a2))
    (hr1 : r1 = a1 + t * (k1 - a1)) (hr2 : r2 = a2 + t * (k2 - a2))
    (h : s * ((b1 - a1) ^ 2 + (b2 - a2) ^ 2) = t * ((k1 - a1) ^ 2 + (k2 - a2) ^ 2)) :
    cyc b1 b2 m1 m2 r1 r2 k1 k2 = 0 := by
  subst hm1 hm2 hr1 hr2
  simp only [cyc, area2]
  linear_combination
    (-(s - 1) * (t - 1) * (a1 * (b2 - k2) + b1 * (k2 - a2) + k1 * (a2 - b2))) * h

/-- **IMO 2004 P1.** -/
theorem imo2004_p1
    (u v b c k s t' t m1 m2 n1 n2 r1 r2 : ℝ)
    (hv : 0 < v)                                    -- `A` is off the line `BC`
    (hu : u ≠ 0)                                    -- `AB ≠ AC`
    (hb : 0 < b) (hc : 0 < c)
    (hbsq : b ^ 2 = (u + 1) ^ 2 + v ^ 2)            -- `b = AC`
    (hcsq : c ^ 2 = (u - 1) ^ 2 + v ^ 2)            -- `c = AB`
    (hP : 0 < u ^ 2 + v ^ 2 - 1)                    -- the angle at `A` is acute
    (hk : k * (b + c) = b - c)                      -- `K` is the foot of the `A`-bisector
    -- `M` lies on `AB`, and `CM ⊥ AB`
    (hm1 : m1 = u + s * (1 - u)) (hm2 : m2 = v - s * v)
    (hMperp : (m1 - (-1)) * (1 - u) + (m2 - 0) * (0 - v) = 0)
    -- `N` lies on `AC`, and `BN ⊥ AC`
    (hn1 : n1 = u + t' * (-1 - u)) (hn2 : n2 = v - t' * v)
    (hNperp : (n1 - 1) * (-1 - u) + (n2 - 0) * (0 - v) = 0)
    -- `R` lies on `AK` and is equidistant from `M` and `N`
    (hr1 : r1 = u + t * (k - u)) (hr2 : r2 = v - t * v)
    (hReq : (r1 - m1) ^ 2 + (r2 - m2) ^ 2 = (r1 - n1) ^ 2 + (r2 - n2) ^ 2) :
    cyc 1 0 m1 m2 r1 r2 k 0 = 0 ∧ cyc (-1) 0 n1 n2 r1 r2 k 0 = 0 ∧ -1 < k ∧ k < 1 := by
  subst hm1 hm2 hn1 hn2 hr1 hr2
  have hbc : 0 < b + c := by linarith
  -- `K` is interior to `BC`
  have hk1 : -1 < k := by
    have h1 : (k + 1) * (b + c) = 2 * b := by linear_combination hk
    nlinarith [hb, hbc]
  have hk2 : k < 1 := by
    have h1 : (1 - k) * (b + c) = 2 * c := by linear_combination -hk
    nlinarith [hc, hbc]
  -- the bisector condition, cleared of square roots
  have hbc2 : b * (1 - k) = c * (1 + k) := by linear_combination -hk
  have hsq : b ^ 2 * (1 - k) ^ 2 = c ^ 2 * (1 + k) ^ 2 := by
    linear_combination (b * (1 - k) + c * (1 + k)) * hbc2
  have hbis : u * (1 + k ^ 2) = k * (u ^ 2 + v ^ 2 + 1) := by
    linear_combination (1 / 4) * hsq - ((1 - k) ^ 2 / 4) * hbsq + ((1 + k) ^ 2 / 4) * hcsq
  -- both feet realise the power of `A`
  have hs : s * ((1 - u) ^ 2 + v ^ 2) = u ^ 2 + v ^ 2 - 1 := by linear_combination hMperp
  have ht : t' * ((u + 1) ^ 2 + v ^ 2) = u ^ 2 + v ^ 2 - 1 := by linear_combination hNperp
  -- and so does `R` on the bisector
  have hgoal : t * ((k - u) ^ 2 + v ^ 2) = u ^ 2 + v ^ 2 - 1 := by
    have h0 : (4 * (u ^ 2 + v ^ 2 - 1) * u) *
        (t * ((k - u) ^ 2 + v ^ 2) - (u ^ 2 + v ^ 2 - 1)) = 0 := by
      linear_combination
        (-(((u + 1) ^ 2 + v ^ 2) * ((1 - u) ^ 2 + v ^ 2))) * hReq
        + (-(((u + 1) ^ 2 + v ^ 2) *
            (-((1 - u) ^ 2 + v ^ 2) * s + 2 * t * (k * (1 - u) + u ^ 2 - u + v ^ 2)
              - (u ^ 2 + v ^ 2 - 1)))) * hs
        + (-(((1 - u) ^ 2 + v ^ 2) *
            (((u + 1) ^ 2 + v ^ 2) * t' + 2 * t * (k * (1 + u) - u ^ 2 - u - v ^ 2)
              + (u ^ 2 + v ^ 2 - 1)))) * ht
        + (4 * (u ^ 2 + v ^ 2 - 1) * t) * hbis
    have hne : (4 * (u ^ 2 + v ^ 2 - 1) * u) ≠ 0 :=
      mul_ne_zero (by linarith) hu
    have h1 := (mul_eq_zero.1 h0).resolve_left hne
    linarith
  refine ⟨?_, ?_, hk1, hk2⟩
  · exact cyc_of_pow_eq u v 1 0 k 0 _ _ _ _ s t (by ring) (by ring) (by ring) (by ring)
      (by linear_combination hs - hgoal)
  · exact cyc_of_pow_eq u v (-1) 0 k 0 _ _ _ _ t' t (by ring) (by ring) (by ring) (by ring)
      (by linear_combination ht - hgoal)

end Imo2004P1
