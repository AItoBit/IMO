import Mathlib

/-!
# IMO 2000, Problem 2

For positive reals `a, b, c` with `abc = 1`,
`(a - 1 + 1/b) (b - 1 + 1/c) (c - 1 + 1/a) ≤ 1`.

## Proof

Writing `a = x/y`, `b = y/z`, `c = z/x` turns this into
`(x - y + z)(y - z + x)(z - x + y) ≤ xyz` for positive `x, y, z`. The substitution is realized
concretely by `(x, y, z) = (a, 1, 1/b)`; this is legitimate exactly because `abc = 1`, which
forces `c = 1/(ab)`.

For the core inequality put `p = x - y + z`, `q = y - z + x`, `r = z - x + y`, so that
`p + q = 2x`, `q + r = 2y`, `r + p = 2z` are all positive. Hence at most one of `p, q, r` is
nonpositive.

* If one of them is `≤ 0`, the other two are `> 0`, so `pqr ≤ 0 < xyz`.
* If all are `> 0`, note `pq = x² - (y-z)² ≤ x²`, `qr = y² - (x-z)² ≤ y²`,
  `rp = z² - (x-y)² ≤ z²`. Multiplying, `(pqr)² ≤ (xyz)²`, and both sides being positive gives
  `pqr ≤ xyz`.

The last bullet replaces the AM-GM step of the AoPS write-up; it avoids square roots entirely,
which keeps the whole argument polynomial.
-/

namespace Imo2000P2

/-- The substituted form: `(x-y+z)(y-z+x)(z-x+y) ≤ xyz` for positive `x, y, z`. -/
theorem core (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (x - y + z) * (y - z + x) * (z - x + y) ≤ x * y * z := by
  rcases le_or_lt (x - y + z) 0 with hp | hp
  · -- `p ≤ 0`, so `q, r > 0` and the product is nonpositive
    have hq : 0 < y - z + x := by linarith
    have hr : 0 < z - x + y := by linarith
    nlinarith [mul_pos hq hr, mul_pos (mul_pos hx hy) hz]
  rcases le_or_lt (y - z + x) 0 with hq | hq
  · have hr : 0 < z - x + y := by linarith
    nlinarith [mul_pos hr hp, mul_pos (mul_pos hx hy) hz]
  rcases le_or_lt (z - x + y) 0 with hr | hr
  · nlinarith [mul_pos hp hq, mul_pos (mul_pos hx hy) hz]
  -- all three are positive
  have h1 : (x - y + z) * (y - z + x) ≤ x ^ 2 := by nlinarith [sq_nonneg (y - z)]
  have h2 : (y - z + x) * (z - x + y) ≤ y ^ 2 := by nlinarith [sq_nonneg (x - z)]
  have h3 : (z - x + y) * (x - y + z) ≤ z ^ 2 := by nlinarith [sq_nonneg (x - y)]
  have hqr : 0 < (y - z + x) * (z - x + y) := mul_pos hq hr
  have hrp : 0 < (z - x + y) * (x - y + z) := mul_pos hr hp
  have hprod : ((x - y + z) * (y - z + x) * (z - x + y)) ^ 2 ≤ (x * y * z) ^ 2 := by
    calc ((x - y + z) * (y - z + x) * (z - x + y)) ^ 2
        = ((x - y + z) * (y - z + x)) * ((y - z + x) * (z - x + y)) *
            ((z - x + y) * (x - y + z)) := by ring
      _ ≤ x ^ 2 * y ^ 2 * z ^ 2 := by
          refine mul_le_mul (mul_le_mul h1 h2 hqr.le (by positivity)) h3 hrp.le (by positivity)
      _ = (x * y * z) ^ 2 := by ring
  have hpos : 0 < (x - y + z) * (y - z + x) * (z - x + y) := mul_pos (mul_pos hp hq) hr
  nlinarith [hprod, hpos, mul_pos (mul_pos hx hy) hz]

/-- **IMO 2000 P2.** -/
theorem imo2000_p2 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) :
    (a - 1 + 1 / b) * (b - 1 + 1 / c) * (c - 1 + 1 / a) ≤ 1 := by
  have ha' : a ≠ 0 := ne_of_gt ha
  have hb' : b ≠ 0 := ne_of_gt hb
  have hc' : c = 1 / (a * b) := by
    field_simp
    linear_combination habc
  -- the substitution `(x, y, z) = (a, 1, 1/b)`
  have hcore := core a 1 (1 / b) ha one_pos (by positivity)
  have key : (a - 1 + 1 / b) * (b - 1 + 1 / c) * (c - 1 + 1 / a)
      = (b / a) * ((a - 1 + 1 / b) * (1 - 1 / b + a) * (1 / b - a + 1)) := by
    rw [hc']
    field_simp
    ring
  rw [key]
  have hba : (0 : ℝ) < b / a := by positivity
  calc (b / a) * ((a - 1 + 1 / b) * (1 - 1 / b + a) * (1 / b - a + 1))
      ≤ (b / a) * (a * 1 * (1 / b)) := mul_le_mul_of_nonneg_left hcore hba.le
    _ = 1 := by field_simp

end Imo2000P2
