import Mathlib

/-!
# IMO 1989, Problem 4 — metric core

`ABCD` is a convex quadrilateral with `AB = AD + BC`, and `P` is an interior point at distance
`h` from the line `CD` with `AP = h + AD` and `BP = h + BC`. Prove

  `1/√h ≥ 1/√AD + 1/√BC`.

## What is formalized here

Mathlib has no API for convex quadrilaterals, for "the point is inside", or for the position of
a vertex relative to a side line, so the synthetic reduction cannot be carried out. What is
formalized is the metric content of the AoPS solution, with `a = AD`, `b = BC`.

The solution turns the hypotheses into three circles: `A` of radius `a`, `B` of radius `b`
(externally tangent, since `AB = a + b`) and `P` of radius `h` (externally tangent to both,
since `AP = a + h` and `BP = b + h`), with `P` also at distance `h` from the line `CD`.
Writing `x` for the horizontal offsets along that line, external tangency to a circle of
radius `ρ` sitting at height `ρ` forces `x² = 4ρh`; so the three offsets are `2√(ab)`,
`2√(ah)` and `2√(bh)`, and `P` fitting in the gap is exactly `√(ah) + √(bh) ≤ √(ab)`.

Proved below with no `sorry`:

* `sq_of_tangent`         : external tangency gives the squared horizontal offset;
* `imo1989_p4_core`       : `√(ah) + √(bh) ≤ √(ab) → 1/√a + 1/√b ≤ 1/√h`;
* `imo1989_p4_tangent`    : in the extremal configuration (both circles tangent to the line,
  `P` horizontally between them) equality `1/√h = 1/√a + 1/√b` holds, so the bound is sharp;
* `sharp_value`           : the extremal height is `h = ab/(√a+√b)²`.
-/

open Real

namespace Imo1989P4

/-- Two circles of radii `ρ₁`, `ρ₂` with centres at heights `ρ₁`, `ρ₂` above a line and
externally tangent to each other have squared horizontal offset `4ρ₁ρ₂`. -/
theorem sq_of_tangent {r₁ r₂ u v : ℝ}
    (h : Real.sqrt ((u - v) ^ 2 + (r₁ - r₂) ^ 2) = r₁ + r₂) :
    (u - v) ^ 2 = 4 * (r₁ * r₂) := by
  have hsq : (u - v) ^ 2 + (r₁ - r₂) ^ 2 = (r₁ + r₂) ^ 2 := by
    have h0 : (0 : ℝ) ≤ (u - v) ^ 2 + (r₁ - r₂) ^ 2 := by positivity
    calc (u - v) ^ 2 + (r₁ - r₂) ^ 2
        = Real.sqrt ((u - v) ^ 2 + (r₁ - r₂) ^ 2) ^ 2 := (Real.sq_sqrt h0).symm
      _ = (r₁ + r₂) ^ 2 := by rw [h]
  nlinarith [hsq]

/-- **Metric core of IMO 1989 P4.** -/
theorem imo1989_p4_core {a b h : ℝ} (ha : 0 < a) (hb : 0 < b) (hh : 0 < h)
    (hle : Real.sqrt (a * h) + Real.sqrt (b * h) ≤ Real.sqrt (a * b)) :
    1 / Real.sqrt a + 1 / Real.sqrt b ≤ 1 / Real.sqrt h := by
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.2 hb
  have hsh : 0 < Real.sqrt h := Real.sqrt_pos.2 hh
  rw [Real.sqrt_mul ha.le, Real.sqrt_mul hb.le, Real.sqrt_mul ha.le] at hle
  rw [div_add_div _ _ hsa.ne' hsb.ne', div_le_div_iff₀ (by positivity) hsh]
  nlinarith [hle, hsa, hsb, hsh]

/-- Extremal configuration: circles of radii `a` and `b` tangent to the line `y = 0` from above
and externally tangent to each other; a circle of radius `h` tangent to the line and to both,
horizontally between them. Then equality holds, so the bound of `imo1989_p4_core` is sharp. -/
theorem imo1989_p4_tangent {a b h p q r : ℝ} (ha : 0 < a) (hb : 0 < b) (hh : 0 < h)
    (hAB : Real.sqrt ((p - q) ^ 2 + (a - b) ^ 2) = a + b)
    (hAP : Real.sqrt ((p - r) ^ 2 + (a - h) ^ 2) = a + h)
    (hBP : Real.sqrt ((r - q) ^ 2 + (h - b) ^ 2) = h + b)
    (hbet : 0 ≤ (p - r) * (r - q)) :
    1 / Real.sqrt h = 1 / Real.sqrt a + 1 / Real.sqrt b := by
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.2 hb
  have hsh : 0 < Real.sqrt h := Real.sqrt_pos.2 hh
  -- the three squared horizontal offsets
  have e1 : (p - q) ^ 2 = 4 * (a * b) := sq_of_tangent hAB
  have e2 : (p - r) ^ 2 = 4 * (a * h) := sq_of_tangent hAP
  have e3 : (r - q) ^ 2 = 4 * (h * b) := sq_of_tangent hBP
  -- the middle offset is the product of the two absolute offsets
  have habs : (p - r) * (r - q) = 4 * (h * (Real.sqrt a * Real.sqrt b)) := by
    have hmul : ((p - r) * (r - q)) ^ 2 = (4 * (h * (Real.sqrt a * Real.sqrt b))) ^ 2 := by
      have hA : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha.le
      have hB : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb.le
      calc ((p - r) * (r - q)) ^ 2 = (p - r) ^ 2 * (r - q) ^ 2 := by ring
        _ = (4 * (a * h)) * (4 * (h * b)) := by rw [e2, e3]
        _ = 16 * (h ^ 2 * (Real.sqrt a ^ 2 * Real.sqrt b ^ 2)) := by rw [hA, hB]; ring
        _ = (4 * (h * (Real.sqrt a * Real.sqrt b))) ^ 2 := by ring
    have hnn : (0 : ℝ) ≤ 4 * (h * (Real.sqrt a * Real.sqrt b)) := by positivity
    calc (p - r) * (r - q) = Real.sqrt (((p - r) * (r - q)) ^ 2) := (Real.sqrt_sq hbet).symm
      _ = Real.sqrt ((4 * (h * (Real.sqrt a * Real.sqrt b))) ^ 2) := by rw [hmul]
      _ = 4 * (h * (Real.sqrt a * Real.sqrt b)) := Real.sqrt_sq hnn
  -- combining: `ab = h (√a + √b)²`
  have hkey : a * b = h * (Real.sqrt a + Real.sqrt b) ^ 2 := by
    have hA : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha.le
    have hB : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb.le
    have hexp : (p - q) ^ 2 = (p - r) ^ 2 + 2 * ((p - r) * (r - q)) + (r - q) ^ 2 := by ring
    rw [e1, e2, e3, habs] at hexp
    nlinarith [hexp, hA, hB]
  -- hence `√h (√a + √b) = √a √b`
  have hmain : Real.sqrt h * (Real.sqrt a + Real.sqrt b) = Real.sqrt a * Real.sqrt b := by
    have hsq : (Real.sqrt h * (Real.sqrt a + Real.sqrt b)) ^ 2
        = (Real.sqrt a * Real.sqrt b) ^ 2 := by
      have hA : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha.le
      have hB : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb.le
      have hH : Real.sqrt h ^ 2 = h := Real.sq_sqrt hh.le
      calc (Real.sqrt h * (Real.sqrt a + Real.sqrt b)) ^ 2
          = Real.sqrt h ^ 2 * (Real.sqrt a + Real.sqrt b) ^ 2 := by ring
        _ = h * (Real.sqrt a + Real.sqrt b) ^ 2 := by rw [hH]
        _ = a * b := hkey.symm
        _ = (Real.sqrt a * Real.sqrt b) ^ 2 := by rw [mul_pow, hA, hB]
    have hnn1 : (0 : ℝ) ≤ Real.sqrt h * (Real.sqrt a + Real.sqrt b) := by positivity
    have hnn2 : (0 : ℝ) ≤ Real.sqrt a * Real.sqrt b := by positivity
    calc Real.sqrt h * (Real.sqrt a + Real.sqrt b)
        = Real.sqrt ((Real.sqrt h * (Real.sqrt a + Real.sqrt b)) ^ 2) := (Real.sqrt_sq hnn1).symm
      _ = Real.sqrt ((Real.sqrt a * Real.sqrt b) ^ 2) := by rw [hsq]
      _ = Real.sqrt a * Real.sqrt b := Real.sqrt_sq hnn2
  rw [div_add_div _ _ hsa.ne' hsb.ne', eq_div_iff (by positivity), div_mul_eq_mul_div,
    div_eq_iff hsh.ne']
  linear_combination -hmain

/-- The extremal height: `h = ab/(√a+√b)²`. -/
theorem sharp_value {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    let h := a * b / (Real.sqrt a + Real.sqrt b) ^ 2
    0 < h ∧ 1 / Real.sqrt h = 1 / Real.sqrt a + 1 / Real.sqrt b := by
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.2 hb
  intro h
  have hA : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha.le
  have hB : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb.le
  have hhpos : 0 < h := by
    show 0 < a * b / (Real.sqrt a + Real.sqrt b) ^ 2
    positivity
  refine ⟨hhpos, ?_⟩
  have hval : h = (Real.sqrt a * Real.sqrt b / (Real.sqrt a + Real.sqrt b)) ^ 2 := by
    show a * b / (Real.sqrt a + Real.sqrt b) ^ 2 = _
    rw [div_pow, mul_pow, hA, hB]
  have hsqrt : Real.sqrt h = Real.sqrt a * Real.sqrt b / (Real.sqrt a + Real.sqrt b) := by
    rw [hval, Real.sqrt_sq (by positivity)]
  rw [hsqrt, div_add_div _ _ hsa.ne' hsb.ne', one_div_div]
  rw [div_eq_div_iff (by positivity) (by positivity)]
  ring

end Imo1989P4
