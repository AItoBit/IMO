import Mathlib

/-!
# IMO 2004, Problem 5

In a convex quadrilateral `ABCD` the diagonal `BD` bisects neither `∠ABC` nor `∠CDA`. The point
`P` inside satisfies `∠PBC = ∠DBA` and `∠PDC = ∠BDA`. Then `ABCD` is cyclic iff `AP = CP`.

## Set-up

Coordinates chosen so that `AC` lies on the `x`-axis with midpoint at the origin:
`A = (-r, 0)`, `C = (r, 0)` with `r > 0`; then `B = (x,y)`, `D = (u,v)`, `P = (s,w)`. This is a
genuine WLOG (a rigid motion). In this frame:

* `AP = CP` is `(s+r)² + w² = (s-r)² + w²`, i.e. `s = 0`;
* `A, B, C, D` concyclic is `(x²+y²-r²)v = (u²+v²-r²)y` — both `B` and `D` lie on a circle
  through `(±r, 0)`, i.e. one centred at `(0,t)`, and `t` computed from `B` and from `D` agree.

The two angle conditions are the *isogonality* of `BP` with `BD` at `B`, and of `DP` with `DB`
at `D`. In complex notation with `A = -r`, `C = r` these read

  `(d-b)(p-b) = lam · (a-b)(c-b) = lam · (b² - r²)`,  `lam` real,
  `(b-d)(p-d) = mu · (a-d)(c-d) = mu · (d² - r²)`,  `mu` real,

and `h1`–`h4` below are the real and imaginary parts of those two equations. Using real `lam`,
`mu` rather than positive ones is the directed-angle form, so the theorem proved is slightly
stronger than the stated one in both directions.

## Proof

Eliminating `w`, `lam`, `mu` from the four linear equations `h1`–`h4` yields the single identity

  `((x-u)² + (y-v)²) · E · s = K · cyc`

where `cyc = (x²+y²-r²)v - (u²+v²-r²)y` is the concyclicity expression,
`K = r²(x-u)² + (xv-yu)²`, and `E = r²(xy-uv) + xy(v²-u²) + uv(x²-y²)`. Both directions follow:

* `s = 0` forces `K · cyc = 0`, and `K ≠ 0`, so `cyc = 0`;
* `cyc = 0` forces `((x-u)²+(y-v)²) · E · s = 0`, and both factors are nonzero, so `s = 0`.

`K = 0` would need `x = u` and `xv = yu`, hence (as `B ≠ D`) `x = u = 0`: both `B` and `D` on the
perpendicular bisector of `AC`, which makes `BD` bisect `∠ABC`. So the problem's hypothesis gives
`K ≠ 0`. This is exactly where "`BD` bisects neither angle" is used, and it is needed only for the
direction `AP = CP ⟹ cyclic`.

`E ≠ 0` says the two isogonal lines are not parallel, i.e. `P` is their unique intersection. In
the concyclic case `E = 0` happens exactly when `BD` is a diameter; a configuration with `BD` a
diameter admits a point `P` at all only when `ABCD` is a square, which is again a case where `BD`
bisects `∠ABC`. Deriving that from `h1`–`h4` is a separate argument, so `E ≠ 0` is carried as an
explicit hypothesis here; it is only needed for the direction `cyclic ⟹ AP = CP`.

## Note on the AoPS page

The posted solution proves only `cyclic ⟹ AP = CP`, and does so through points `E`, `F` that are
never defined (from the figure they are the second intersections of `DP`, `BP` with the circle).
The converse — the direction that actually needs the bisecting hypothesis — is not addressed
there at all.
-/

namespace Imo2004P5

/-- Equal distances and equal squared distances are the same condition. -/
theorem sqrt_eq_iff (s w r : ℝ) :
    Real.sqrt ((s + r) ^ 2 + w ^ 2) = Real.sqrt ((s - r) ^ 2 + w ^ 2)
      ↔ (s + r) ^ 2 + w ^ 2 = (s - r) ^ 2 + w ^ 2 := by
  constructor
  · intro h
    have h1 : (0 : ℝ) ≤ (s + r) ^ 2 + w ^ 2 := by positivity
    have h2 : (0 : ℝ) ≤ (s - r) ^ 2 + w ^ 2 := by positivity
    rw [← Real.sq_sqrt h1, ← Real.sq_sqrt h2, h]
  · intro h; rw [h]

/-- **IMO 2004 P5.** -/
theorem imo2004_p5 (r x y u v s w lam mu : ℝ)
    (hr : 0 < r)
    -- `B ≠ D`
    (hbd : (x - u) ^ 2 + (y - v) ^ 2 ≠ 0)
    -- `BD` does not bisect `∠ABC`
    (hK : ¬(x = 0 ∧ u = 0))
    -- the two isogonal lines are not parallel
    (hE : r ^ 2 * (x * y - u * v) + x * y * (v ^ 2 - u ^ 2) + u * v * (x ^ 2 - y ^ 2) ≠ 0)
    -- `∠PBC = ∠DBA`
    (h1 : (u - x) * (s - x) - (v - y) * (w - y) = lam * (x ^ 2 - y ^ 2 - r ^ 2))
    (h2 : (u - x) * (w - y) + (v - y) * (s - x) = lam * (2 * x * y))
    -- `∠PDC = ∠BDA`
    (h3 : (x - u) * (s - u) - (y - v) * (w - v) = mu * (u ^ 2 - v ^ 2 - r ^ 2))
    (h4 : (x - u) * (w - v) + (y - v) * (s - u) = mu * (2 * u * v)) :
    ((s + r) ^ 2 + w ^ 2 = (s - r) ^ 2 + w ^ 2)
      ↔ (x ^ 2 + y ^ 2 - r ^ 2) * v = (u ^ 2 + v ^ 2 - r ^ 2) * y := by
  -- the elimination identity
  have key :
      ((x - u) ^ 2 + (y - v) ^ 2)
        * (r ^ 2 * (x * y - u * v) + x * y * (v ^ 2 - u ^ 2) + u * v * (x ^ 2 - y ^ 2)) * s
      = (r ^ 2 * (x - u) ^ 2 + (x * v - y * u) ^ 2)
        * ((x ^ 2 + y ^ 2 - r ^ 2) * v - (u ^ 2 + v ^ 2 - r ^ 2) * y) := by
    linear_combination
      (-x * y * (-r ^ 2 * u + r ^ 2 * x + u ^ 3 - u ^ 2 * x + u * v ^ 2 - 2 * u * v * y
        + v ^ 2 * x)) * h1
      + ((x ^ 2 - y ^ 2 - r ^ 2) * (-r ^ 2 * u + r ^ 2 * x + u ^ 3 - u ^ 2 * x + u * v ^ 2
        - 2 * u * v * y + v ^ 2 * x) / 2) * h2
      + (u * v * (r ^ 2 * u - r ^ 2 * x - u * x ^ 2 + u * y ^ 2 - 2 * v * x * y + x ^ 3
        + x * y ^ 2)) * h3
      + (-(u ^ 2 - v ^ 2 - r ^ 2) * (r ^ 2 * u - r ^ 2 * x - u * x ^ 2 + u * y ^ 2
        - 2 * v * x * y + x ^ 3 + x * y ^ 2) / 2) * h4
  -- `K ≠ 0`, from the bisecting hypothesis
  have hKne : r ^ 2 * (x - u) ^ 2 + (x * v - y * u) ^ 2 ≠ 0 := by
    intro h0
    have hA : r ^ 2 * (x - u) ^ 2 = 0 := by nlinarith [sq_nonneg (x - u), sq_nonneg (x * v - y * u)]
    have hB : (x * v - y * u) ^ 2 = 0 := by nlinarith [sq_nonneg (x - u), sq_nonneg (x * v - y * u)]
    have hxu : x = u := by nlinarith [sq_nonneg (x - u)]
    have hxv : x * v - y * u = 0 := by nlinarith [hB]
    have hx0 : x * (v - y) = 0 := by rw [hxu]; linarith [hxv, hxu]
    rcases mul_eq_zero.1 hx0 with h | h
    · exact hK ⟨h, by rw [← hxu]; exact h⟩
    · apply hbd
      have hvy : v = y := by linarith
      rw [hxu, hvy]
      ring
  constructor
  · intro hs
    have hsr : s * r = 0 := by nlinarith [hs]
    have hs0 : s = 0 := by
      rcases mul_eq_zero.1 hsr with h | h
      · exact h
      · exact absurd h (ne_of_gt hr)
    rw [hs0, mul_zero] at key
    have h5 := (mul_eq_zero.1 key.symm).resolve_left hKne
    linarith
  · intro hcyc
    have hcyc0 : (x ^ 2 + y ^ 2 - r ^ 2) * v - (u ^ 2 + v ^ 2 - r ^ 2) * y = 0 := by linarith
    rw [hcyc0, mul_zero] at key
    have h5 := (mul_eq_zero.1 key).resolve_left (mul_ne_zero hbd hE)
    rw [h5]
    ring

end Imo2004P5
