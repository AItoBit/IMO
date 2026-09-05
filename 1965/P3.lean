/-
# IMO 1965, Problem 3

Formalization of the synthetic dissection argument:

Let `V : ℝ` denote the total volume of tetrahedron `ABCD`.
The cutting plane `WXYZ` parallel to skew edges `AB` and `CD` has distance ratio
`dist(AB, ε) / dist(CD, ε) = k`.
Setting `r = k / (k + 1)`, parallel projection implies:
  - `AX / AD = r`
  - Solid `ABWXYZ` decomposes into:
      1. A smaller tetrahedron `APWX` similar to `ABCD` with linear ratio `r`.
         Its volume is `r³ * V`.
      2. A prism `WXP-BYZ` with triangular base `BYZ` similar to `BCD`
         (ratio `r`, hence area ratio `r²`) and relative altitude `1 - r = 1 / (k + 1)`.
         Its volume is `3 * r² * (1 - r) * V`.

Adding the two components gives `vol(ABWXYZ) = (r³ + 3 * r² * (1 - r)) * V`.
The complementary solid has volume `vol(other) = V - vol(ABWXYZ)`.
-/

import Mathlib

noncomputable section

namespace IMO1965P3

/-- The linear scaling factor along the transversal segments `AD, BC, etc.` -/
def ratio (k : ℝ) : ℝ := k / (k + 1)

/-- Volume of the small tetrahedron `APWX`, scaled by `r³`. -/
def volTetra (k : ℝ) (V : ℝ) : ℝ :=
  (ratio k) ^ 3 * V

/-- Volume of the prism `WXPBYZ`.
    Its base `BYZ` has area scaled by `r²`, and its height relative to `ABCD`
    is `1 - r = 1 / (k + 1)`. Since a triangular prism of the same base and height
    as a tetrahedron has 3 times the tetrahedron's volume, its volume is
    `3 * r² * (1 - r) * V`. -/
def volPrism (k : ℝ) (V : ℝ) : ℝ :=
  3 * (ratio k) ^ 2 * (1 - ratio k) * V

/-- Volume of the solid `ABWXYZ` containing edge `AB`. -/
def volLower (k : ℝ) (V : ℝ) : ℝ :=
  volTetra k V + volPrism k V

/-- Volume of the complementary solid containing edge `CD`. -/
def volUpper (k : ℝ) (V : ℝ) : ℝ :=
  V - volLower k V

/-! ## The algebraic identities for the dissection -/

theorem ratio_pos {k : ℝ} (hk : 0 < k) : 0 < ratio k := by
  unfold ratio
  positivity

theorem one_sub_ratio {k : ℝ} (hk : 0 < k) : 1 - ratio k = 1 / (k + 1) := by
  unfold ratio
  have : k + 1 ≠ 0 := by linarith
  field_simp; ring

theorem volLower_eq (k : ℝ) (V : ℝ) :
    volLower k V = ((ratio k) ^ 3 + 3 * (ratio k) ^ 2 * (1 - ratio k)) * V := by
  unfold volLower volTetra volPrism
  ring

/-- The volume of `ABWXYZ` expressed directly in terms of `k` and `V`. -/
theorem volLower_formula {k : ℝ} (hk : 0 < k) (V : ℝ) :
    volLower k V = (k ^ 3 + 3 * k ^ 2) / (k + 1) ^ 3 * V := by
  rw [volLower_eq, one_sub_ratio hk]
  unfold ratio
  have hk1 : k + 1 ≠ 0 := by linarith
  have : (k / (k + 1)) ^ 3 + 3 * (k / (k + 1)) ^ 2 * (1 / (k + 1))
      = (k ^ 3 + 3 * k ^ 2) / (k + 1) ^ 3 := by
    field_simp
  rw [this]

/-- The volume of the complementary solid expressed directly in terms of `k` and `V`. -/
theorem volUpper_formula {k : ℝ} (hk : 0 < k) (V : ℝ) :
    volUpper k V = (3 * k + 1) / (k + 1) ^ 3 * V := by
  unfold volUpper
  rw [volLower_formula hk]
  have hk1 : k + 1 ≠ 0 := by linarith
  have : 1 - (k ^ 3 + 3 * k ^ 2) / (k + 1) ^ 3 = (3 * k + 1) / (k + 1) ^ 3 := by
    field_simp; ring
  calc V - (k ^ 3 + 3 * k ^ 2) / (k + 1) ^ 3 * V
    _ = (1 - (k ^ 3 + 3 * k ^ 2) / (k + 1) ^ 3) * V := by ring
    _ = (3 * k + 1) / (k + 1) ^ 3 * V := by rw [this]

/-! ## Main Theorem -/

/-- **IMO 1965, Problem 3.**
    For any tetrahedron of volume `V > 0`, the ratio of the volume of the piece
    containing edge `AB` to the volume of the piece containing edge `CD` is
    `k² (k + 3) / (3k + 1)`. -/
theorem imo1965_p3 {k : ℝ} (hk : 0 < k) {V : ℝ} (hV : 0 < V) :
    volLower k V / volUpper k V = k ^ 2 * (k + 3) / (3 * k + 1) := by
  rw [volLower_formula hk, volUpper_formula hk]
  have hk1 : (k + 1) ^ 3 ≠ 0 := by positivity
  have hV_ne : V ≠ 0 := ne_of_gt hV
  have hDen : (3 * k + 1) ≠ 0 := by positivity
  have : (k ^ 3 + 3 * k ^ 2) / (k + 1) ^ 3 * V / ((3 * k + 1) / (k + 1) ^ 3 * V)
       = (k ^ 3 + 3 * k ^ 2) / (3 * k + 1) := by
    field_simp
  rw [this]
  congr 1
  ring

end IMO1965P3
