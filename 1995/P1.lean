import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/--
Coordinate-normalized form of IMO 1995, Problem 1.

The four collinear points are
`A = (0,0)`, `B = (b,0)`, `C = (1,0)`, and `D = (d,0)`, with
`0 < b < 1 < d`.  The radical axis of the circles with diameters `AC` and
`BD` is the vertical line `x = z`; its equation is
`(b + d - 1) z = b d`.  We write `P = (z,t)`, where `t ≠ 0` expresses
`P ≠ Z`.

The equations `hMline`, `hMcircle`, `hNline`, and `hNcircle` say respectively
that `C,P,M` are collinear, `M` is on the circle with diameter `AC`, `B,P,N`
are collinear, and `N` is on the circle with diameter `BD`.  The two
inequalities exclude the already known intersections `M = C` and `N = B`.

The conclusion constructs a real `q` such that `Q = (z,q)` lies on both
`AM` and `DN`; since it also lies on `x = z = XY`, the three lines are
concurrent.
-/
theorem imo_1995_p1
    (b d z t mx my nx ny : ℝ)
    (_hb : 0 < b) (hbc : b < 1) (hcd : 1 < d) (ht : t ≠ 0)
    (hradical : (b + d - 1) * z = b * d)
    (hMline : (mx - 1) * t - my * (z - 1) = 0)
    (hMcircle : mx * (mx - 1) + my ^ 2 = 0)
    (hMneC : (mx, my) ≠ (1, 0))
    (hNline : (nx - b) * t - ny * (z - b) = 0)
    (hNcircle : (nx - b) * (nx - d) + ny ^ 2 = 0)
    (hNneB : (nx, ny) ≠ (b, 0)) :
    ∃ q : ℝ,
      z * my - q * mx = 0 ∧
      (z - d) * ny - q * (nx - d) = 0 := by
  have hmy : my ≠ 0 := by
    intro hmy0
    have hfactor : mx * (mx - 1) = 0 := by
      rw [hmy0] at hMcircle
      simpa using hMcircle
    rcases mul_eq_zero.mp hfactor with hmx0 | hmx1
    · rw [hmx0, hmy0] at hMline
      apply ht
      linarith
    · have hmx : mx = 1 := by linarith
      exact hMneC (Prod.ext hmx hmy0)
  have hny : ny ≠ 0 := by
    intro hny0
    have hfactor : (nx - b) * (nx - d) = 0 := by
      rw [hny0] at hNcircle
      simpa using hNcircle
    rcases mul_eq_zero.mp hfactor with hnxB | hnxD
    · have hnx : nx = b := by linarith
      exact hNneB (Prod.ext hnx hny0)
    · have hnx : nx = d := by linarith
      rw [hnx, hny0] at hNline
      have hdb : 0 < d - b := by linarith
      apply ht
      nlinarith
  have hMrelation : mx * (z - 1) + t * my = 0 := by
    have hproduct : my * (mx * (z - 1) + t * my) = 0 := by
      linear_combination t * hMcircle - mx * hMline
    exact (mul_eq_zero.mp hproduct).resolve_left hmy
  have hNrelation : (z - b) * (nx - d) + t * ny = 0 := by
    have hproduct : ny * ((z - b) * (nx - d) + t * ny) = 0 := by
      linear_combination t * hNcircle - (nx - d) * hNline
    exact (mul_eq_zero.mp hproduct).resolve_left hny
  have hmx : mx ≠ 0 := by
    intro hmx0
    rw [hmx0] at hMrelation
    have htm : t * my = 0 := by simpa using hMrelation
    exact hmy (by
      apply (mul_eq_zero.mp htm).resolve_left ht)
  have hradical' : (z - d) * (z - b) - z * (z - 1) = 0 := by
    nlinarith [hradical]
  let q : ℝ := z * my / mx
  refine ⟨q, ?_, ?_⟩
  · dsimp [q]
    rw [div_mul_cancel₀ _ hmx]
    ring
  · have hpoly :
        mx * ((z - d) * ny) - z * my * (nx - d) = 0 := by
      have htpoly :
          t * (mx * ((z - d) * ny) - z * my * (nx - d)) = 0 := by
        linear_combination
          mx * (z - d) * hNrelation -
          z * (nx - d) * hMrelation -
          mx * (nx - d) * hradical'
      exact (mul_eq_zero.mp htpoly).resolve_left ht
    dsimp [q]
    field_simp [hmx]
    nlinarith
