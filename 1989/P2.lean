import Mathlib

/-!
# IMO 1989, Problem 2 — metric core

`ABC` is a triangle; the bisector of angle `A` meets the circumcircle at `A₁` (similarly
`B₁`, `C₁`). The line `AA₁` meets the external bisectors at `B` and `C` in `A₀`
(similarly `B₀`, `C₀`). Prove

  `[A₀B₀C₀] = 2 · [AC₁BA₁CB₁] ≥ 4 · [ABC]`.

## What is formalized here

Mathlib has no circumcircle/angle-bisector intersection API, and no area formula for a
triangle in terms of its inradius, so the synthetic step cannot be carried out.
What is formalized is the **metric core**, i.e. everything the AoPS solution does after the
synthetic reductions:

* `[A₁BC] = ¼a² tan(A/2) = ¼a² · 2r/(b+c-a)`, so the hexagon has area
  `hexArea = S + Σ ¼a² · 2r/(b+c-a)`;
* `A₀`, `B₀`, `C₀` are the excenters, the exradius is `rₐ = r(a+b+c)/(b+c-a)`, and the
  excentral triangle splits into `ABC` together with `A₀BC`, `B₀CA`, `C₀AB`, so
  `excentralArea = S + Σ ½a · rₐ`.

Taking those two formulas as the definitions, both claims are proved below with no `sorry`:

* `excentralArea_eq_two_mul_hexArea` : `[A₀B₀C₀] = 2 · [hexagon]`;
* `four_mul_le_excentralArea`        : `4 · [ABC] ≤ [A₀B₀C₀]`;
* `imo1989_p2_core`                  : both at once.

The only inequality needed is `Σ a/(b+c-a) ≥ 3`, proved by Ravi substitution.

Note the AoPS page drops the `+[ABC]` term from `[A₀B₀C₀]`; with that omission the first
identity is false (for an equilateral triangle it would give `3S = 4S`). The term is
restored here.
-/

namespace Imo1989P2

variable {a b c r S : ℝ}

/-- Area of the hexagon `AC₁BA₁CB₁`: the triangle plus the three circular "ears". -/
noncomputable def hexArea (a b c r S : ℝ) : ℝ :=
  S + (1 / 4) * a ^ 2 * (2 * r / (b + c - a))
    + (1 / 4) * b ^ 2 * (2 * r / (c + a - b))
    + (1 / 4) * c ^ 2 * (2 * r / (a + b - c))

/-- Area of the excentral triangle `A₀B₀C₀`: the triangle plus the three triangles
`A₀BC`, `B₀CA`, `C₀AB`, each of area `½ · side · exradius`. -/
noncomputable def excentralArea (a b c r S : ℝ) : ℝ :=
  S + (1 / 2) * a * (r * (a + b + c) / (b + c - a))
    + (1 / 2) * b * (r * (a + b + c) / (c + a - b))
    + (1 / 2) * c * (r * (a + b + c) / (a + b - c))

/-- The key inequality, by Ravi substitution and AM–GM. -/
theorem three_le_sum_div (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hu : 0 < b + c - a) (hv : 0 < c + a - b) (hw : 0 < a + b - c) :
    3 ≤ a / (b + c - a) + b / (c + a - b) + c / (a + b - c) := by
  rw [div_add_div _ _ hu.ne' hv.ne', div_add_div _ _ (by positivity) hw.ne',
    le_div_iff₀ (by positivity)]
  nlinarith [mul_nonneg hu.le (sq_nonneg (b - c)), mul_nonneg hv.le (sq_nonneg (c - a)),
    mul_nonneg hw.le (sq_nonneg (a - b))]

/-- `[A₀B₀C₀] = 2 · [AC₁BA₁CB₁]`. -/
theorem excentralArea_eq_two_mul_hexArea
    (hu : 0 < b + c - a) (hv : 0 < c + a - b) (hw : 0 < a + b - c)
    (hS : S = r * (a + b + c) / 2) :
    excentralArea a b c r S = 2 * hexArea a b c r S := by
  simp only [excentralArea, hexArea, hS]
  field_simp
  ring

/-- `4 · [ABC] ≤ [A₀B₀C₀]`. -/
theorem four_mul_le_excentralArea
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hr : 0 < r)
    (hu : 0 < b + c - a) (hv : 0 < c + a - b) (hw : 0 < a + b - c)
    (hS : S = r * (a + b + c) / 2) :
    4 * S ≤ excentralArea a b c r S := by
  have hkey := three_le_sum_div ha hb hc hu hv hw
  have hp : 0 < r * (a + b + c) / 2 := by positivity
  have hrw : excentralArea a b c r S - 4 * S
      = (r * (a + b + c) / 2) *
        (a / (b + c - a) + b / (c + a - b) + c / (a + b - c) - 3) := by
    simp only [excentralArea, hS]
    field_simp
    ring
  nlinarith [mul_nonneg hp.le (by linarith : (0 : ℝ) ≤
    a / (b + c - a) + b / (c + a - b) + c / (a + b - c) - 3)]

/-- **IMO 1989 P2, metric core.** -/
theorem imo1989_p2_core
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hr : 0 < r)
    (hu : 0 < b + c - a) (hv : 0 < c + a - b) (hw : 0 < a + b - c)
    (hS : S = r * (a + b + c) / 2) :
    excentralArea a b c r S = 2 * hexArea a b c r S ∧ 4 * S ≤ excentralArea a b c r S :=
  ⟨excentralArea_eq_two_mul_hexArea hu hv hw hS,
   four_mul_le_excentralArea ha hb hc hr hu hv hw hS⟩

/-- Equality holds for the equilateral triangle. -/
example : excentralArea 1 1 1 (Real.sqrt 3 / 6) (Real.sqrt 3 / 4)
    = 4 * (Real.sqrt 3 / 4) := by
  simp only [excentralArea]
  norm_num
  ring

end Imo1989P2
