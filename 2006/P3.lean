import Mathlib

/-!
# IMO 2006, Problem 3

Determine the least `M` with
`|ab(a²-b²) + bc(b²-c²) + ca(c²-a²)| ≤ M (a² + b² + c²)²` for all real `a, b, c`.

Answer: `M = 9√2/32`.

## Proof

Write `E = ab(a²-b²) + bc(b²-c²) + ca(c²-a²)`. Substituting `s = a+b+c`, `x = a-b`, `y = b-c`
(so `a - c = x + y`) turns the problem into two variables' worth of structure:

  `E = s·xy(x+y)`,   `a² + b² + c² = (s² + 2(x²+xy+y²))/3`.

Putting `A = s²`, `v = 2(x²+xy+y²)`, `w = xy(x+y)`, the claim `512 E² ≤ 81(a²+b²+c²)⁴` becomes

  `512 · A · w² ≤ (A + v)⁴`,

which follows from two exact identities:

* `4(x²+xy+y²)³ - 27 x²y²(x+y)² = ((x-y)(2x+y)(x+2y))²`, giving `54 w² ≤ v³`;
* `27(A+v)⁴ - 256 A v³ = (3A - v)²(3A² + 14Av + 27v²)`, the four-term AM–GM
  `A + v/3 + v/3 + v/3 ≥ 4(Av³/27)^{1/4}` in polynomial form.

Chaining them, `512 A w² ≤ (512/54) A v³ = (256/27) A v³ ≤ (A+v)⁴`.

Equality forces `x = y` (first identity) and `3A = v` (second), i.e. `a-b = b-c` and
`(a+b+c)² = 6(a-b)²`. Scaling, `(a,b,c) = (3+√2, √2, √2-3)` gives `E = 162√2` and
`a²+b²+c² = 24`, so any valid `M` satisfies `162√2 ≤ 576 M`, i.e. `M ≥ 9√2/32`.

Both identities replace the write-up's calculus: it maximises `Δ` in `q` by completing a square
and then maximises `f(t) = t(3-t)³/54` on `[0,3]` by differentiating. The `(3A-v)²` factorisation
above is exactly that second optimisation (`t = 3/4` there corresponds to `3A = v` here), but as
an algebraic identity rather than a derivative computation.
-/

namespace Imo2006P3

theorem abs_le_of_sq_le_sq {u K : ℝ} (h : u ^ 2 ≤ K ^ 2) (hK : 0 ≤ K) : |u| ≤ K := by
  nlinarith [abs_nonneg u, sq_abs u, h, hK]

/-- The inequality after the substitution `s = a+b+c`, `x = a-b`, `y = b-c`. -/
theorem core_swy (s x y : ℝ) :
    512 * (s * (x * y * (x + y))) ^ 2 ≤ 81 * ((s ^ 2 + 2 * (x ^ 2 + x * y + y ^ 2)) / 3) ^ 4 := by
  have hA : (0 : ℝ) ≤ s ^ 2 := sq_nonneg s
  have hv : (0 : ℝ) ≤ 2 * (x ^ 2 + x * y + y ^ 2) := by
    nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg (x + y)]
  -- `27 w² ≤ 4(x²+xy+y²)³`
  have hw : 27 * (x * y * (x + y)) ^ 2 ≤ 4 * (x ^ 2 + x * y + y ^ 2) ^ 3 := by
    nlinarith [sq_nonneg ((x - y) * (2 * x + y) * (x + 2 * y))]
  have h1 : 54 * (x * y * (x + y)) ^ 2 ≤ (2 * (x ^ 2 + x * y + y ^ 2)) ^ 3 := by nlinarith [hw]
  -- `256 A v³ ≤ 27 (A+v)⁴`
  have hQ : (0 : ℝ) ≤ 3 * (s ^ 2) ^ 2 + 14 * (s ^ 2) * (2 * (x ^ 2 + x * y + y ^ 2))
      + 27 * (2 * (x ^ 2 + x * y + y ^ 2)) ^ 2 := by
    nlinarith [sq_nonneg (s ^ 2), mul_nonneg hA hv, sq_nonneg (2 * (x ^ 2 + x * y + y ^ 2))]
  have h2 : 256 * (s ^ 2) * (2 * (x ^ 2 + x * y + y ^ 2)) ^ 3
      ≤ 27 * ((s ^ 2) + 2 * (x ^ 2 + x * y + y ^ 2)) ^ 4 := by
    nlinarith [mul_nonneg (sq_nonneg (3 * (s ^ 2) - 2 * (x ^ 2 + x * y + y ^ 2))) hQ]
  have h3 : (s ^ 2) * (54 * (x * y * (x + y)) ^ 2)
      ≤ (s ^ 2) * ((2 * (x ^ 2 + x * y + y ^ 2)) ^ 3) :=
    mul_le_mul_of_nonneg_left h1 hA
  nlinarith [h3, h2]

theorem core (a b c : ℝ) :
    512 * (a * b * (a ^ 2 - b ^ 2) + b * c * (b ^ 2 - c ^ 2) + c * a * (c ^ 2 - a ^ 2)) ^ 2
      ≤ 81 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 4 := by
  have h1 : a * b * (a ^ 2 - b ^ 2) + b * c * (b ^ 2 - c ^ 2) + c * a * (c ^ 2 - a ^ 2)
      = (a + b + c) * ((a - b) * (b - c) * ((a - b) + (b - c))) := by ring
  have h2 : a ^ 2 + b ^ 2 + c ^ 2
      = ((a + b + c) ^ 2 + 2 * ((a - b) ^ 2 + (a - b) * (b - c) + (b - c) ^ 2)) / 3 := by ring
  rw [h1, h2]
  exact core_swy (a + b + c) (a - b) (b - c)

/-- **IMO 2006 P3.** -/
theorem imo2006_p3 :
    IsLeast {M : ℝ | ∀ a b c : ℝ,
        |a * b * (a ^ 2 - b ^ 2) + b * c * (b ^ 2 - c ^ 2) + c * a * (c ^ 2 - a ^ 2)|
          ≤ M * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2}
      (9 * Real.sqrt 2 / 32) := by
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs2nn : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  constructor
  · -- the bound holds
    intro a b c
    have hK : (0 : ℝ) ≤ 9 * Real.sqrt 2 / 32 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 := by positivity
    refine abs_le_of_sq_le_sq ?_ hK
    have hrw : (9 * Real.sqrt 2 / 32 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2) ^ 2
        = 81 / 512 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 4 := by
      linear_combination (81 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 4 / 1024) * hs2
    rw [hrw]
    linarith [core a b c]
  · -- and it is least
    intro M hM
    have h := hM (3 + Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 2 - 3)
    have hE : (3 + Real.sqrt 2) * Real.sqrt 2 * ((3 + Real.sqrt 2) ^ 2 - Real.sqrt 2 ^ 2)
        + Real.sqrt 2 * (Real.sqrt 2 - 3) * (Real.sqrt 2 ^ 2 - (Real.sqrt 2 - 3) ^ 2)
        + (Real.sqrt 2 - 3) * (3 + Real.sqrt 2) * ((Real.sqrt 2 - 3) ^ 2 - (3 + Real.sqrt 2) ^ 2)
        = 162 * Real.sqrt 2 := by ring
    have hQ : (3 + Real.sqrt 2) ^ 2 + Real.sqrt 2 ^ 2 + (Real.sqrt 2 - 3) ^ 2 = 24 := by
      linear_combination 3 * hs2
    rw [hE, hQ, abs_of_nonneg (by positivity)] at h
    norm_num at h
    linarith

end Imo2006P3
