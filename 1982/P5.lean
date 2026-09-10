/-
# IMO 1982, Problem 5

The diagonals `AC` and `CE` of the regular hexagon `ABCDEF` are divided by
interior points `M` and `N` with

  `AM/AC = CN/CE = r`.

Determine `r` if `B`, `M`, `N` are collinear.

The answer is `r = √3/3 = 1/√3`.

## Modelling

Place the hexagon of side `1` centred at the origin (a similarity, so no loss of
generality), with `s = √3`:

  `A = (1, 0)`,  `B = (1/2, s/2)`,  `C = (-1/2, s/2)`,
  `D = (-1, 0)`, `E = (-1/2, -s/2)`, `F = (1/2, -s/2)`.

Then `M = A + r(C - A)` and `N = C + r(E - C)` are exactly the points with
`AM/AC = CN/CE = r`, and collinearity of `B, M, N` is the vanishing of the
determinant

  `(Mx - Bx)(Ny - By) = (My - By)(Nx - Bx)`.

The coordinates are written out in the hypotheses, so the statement mentions no
`Prod` projections.

## Proof

With those coordinates,

  `M = (1 - 3r/2, rs/2)`,  `N = (-1/2, s/2 - rs)`,

so the determinant equals `s(3r² - 1)/2`.  Since `s = √3 ≠ 0`, collinearity is
exactly `3r² = 1`, and `r > 0` gives `r = √3/3`.

This is Solution 5 of the AoPS page, but with the hexagon placed symmetrically
about the origin, which keeps every coordinate a rational multiple of `1` or of
`s` and makes the determinant a one-line `linear_combination`.
-/

import Mathlib

namespace Imo1982P5

/-- **IMO 1982, Problem 5.** -/
theorem imo1982_p5 (r s Mx My Nx Ny : ℝ)
    (hs : s = Real.sqrt 3) (hr0 : 0 < r) (hr1 : r < 1)
    -- `M = A + r (C - A)` with `A = (1, 0)`, `C = (-1/2, s/2)`
    (hMx : Mx = 1 + r * ((-1 / 2) - 1))
    (hMy : My = 0 + r * (s / 2 - 0))
    -- `N = C + r (E - C)` with `C = (-1/2, s/2)`, `E = (-1/2, -s/2)`
    (hNx : Nx = (-1 / 2) + r * ((-1 / 2) - (-1 / 2)))
    (hNy : Ny = s / 2 + r * ((-(s / 2)) - s / 2))
    -- `B = (1/2, s/2)` is collinear with `M` and `N`
    (hcol : (Mx - 1 / 2) * (Ny - s / 2) = (My - s / 2) * (Nx - 1 / 2)) :
    r = Real.sqrt 3 / 3 := by
  subst hs
  subst hMx
  subst hMy
  subst hNx
  subst hNy
  have hspos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  -- the collinearity determinant is `√3 (3r² - 1)/2`
  have hkey : Real.sqrt 3 * (3 * r ^ 2 - 1) = 0 := by linear_combination 2 * hcol
  have h3r : 3 * r ^ 2 - 1 = 0 := by
    rcases mul_eq_zero.mp hkey with h | h
    · exact absurd h (ne_of_gt hspos)
    · exact h
  -- and `r > 0`
  have hfac : (r - Real.sqrt 3 / 3) * (r + Real.sqrt 3 / 3) = 0 := by
    linear_combination (1 / 3 : ℝ) * h3r - (1 / 9 : ℝ) * hs2
  rcases mul_eq_zero.mp hfac with h | h
  · linarith
  · linarith

end Imo1982P5
