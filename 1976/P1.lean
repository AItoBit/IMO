import Mathlib

/-!
# IMO 1976 Problem 1

In a plane convex quadrilateral of area `32`, the sum of the lengths of two opposite sides
and one diagonal is `16`. Determine all the possible lengths of the other diagonal.

Answer: the other diagonal has length `8 * √2`, and this value is attained.

## Formalization notes

Points are elements of the Euclidean plane `EuclideanSpace ℝ (Fin 2)`.

A quadrilateral `A B C D` is encoded by its four vertices listed in counterclockwise order
(any convex quadrilateral admits such a labelling), and *strict convexity* is expressed by
saying that each of the four consecutive turns is a strict left turn, i.e. all four cross
products `cross A B B C`, `cross B C C D`, `cross C D D A`, `cross D A A B` are positive
(`IMO1976P1.ConvexCCW`).

`IMO1976P1.area` is the signed (shoelace) area; the area of the quadrilateral is its absolute
value, so the hypothesis of the problem reads `|area A B C D| = 32`.

The two opposite sides are `AB` and `DC`, the given diagonal is `BD`, and the answer concerns
the other diagonal `AC`.
-/

namespace IMO1976P1

open Real

/-- The Euclidean plane. -/
abbrev Pt := EuclideanSpace ℝ (Fin 2)

/-- The two–dimensional cross product of the vectors `Q - P` and `S - R`. -/
noncomputable def cross (P Q R S : Pt) : ℝ :=
  (Q 0 - P 0) * (S 1 - R 1) - (Q 1 - P 1) * (S 0 - R 0)

/-- Strict convexity of the quadrilateral `A B C D`, whose vertices are listed in
counterclockwise order: each consecutive turn is a strict left turn. -/
def ConvexCCW (A B C D : Pt) : Prop :=
  0 < cross A B B C ∧ 0 < cross B C C D ∧ 0 < cross C D D A ∧ 0 < cross D A A B

/-- The area of the quadrilateral `A B C D` (shoelace formula, valid for a
counterclockwise-oriented convex quadrilateral `A B C D`). -/
noncomputable def area (A B C D : Pt) : ℝ :=
  ((A 0 * B 1 - B 0 * A 1) + (B 0 * C 1 - C 0 * B 1) + (C 0 * D 1 - D 0 * C 1) +
    (D 0 * A 1 - A 0 * D 1)) / 2

/-- The squared distance in the Euclidean plane, in coordinates. -/
lemma dist_sq (X Y : Pt) : dist X Y ^ 2 = (X 0 - Y 0) ^ 2 + (X 1 - Y 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_two, Real.dist_eq, sq_abs]

/-- The abstract skeleton of the argument.  Here `p = AB`, `q = DC`, `r = BD`, `ac = AC`,
`T1`, `T2` are twice the areas of the triangles `ABD` and `BCD`, `E1`, `E2` are the dot
products of the sides `BA`, `DC` with the diagonal, and `K` is the dot product of the
vectors `A - B` and `D - C`. -/
lemma core_ineq (p q r ac T1 T2 E1 E2 K : ℝ)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hsplit : T1 + T2 = 64)
    (hlag1 : r ^ 2 * p ^ 2 = E1 ^ 2 + T1 ^ 2)
    (hlag2 : r ^ 2 * q ^ 2 = E2 ^ 2 + T2 ^ 2)
    (hkey : K * r ^ 2 = E1 * E2 + T1 * T2)
    (hacsq : ac ^ 2 = p ^ 2 + r ^ 2 + q ^ 2 - 2 * E1 + 2 * K - 2 * E2)
    (hsum : p + r + q = 16) :
    ac ^ 2 = 128 := by
  have hb1 : T1 ≤ r * p := by nlinarith [sq_nonneg E1, mul_nonneg hr hp]
  have hb2 : T2 ≤ r * q := by nlinarith [sq_nonneg E2, mul_nonneg hr hq]
  have hpq16 : p + q = 16 - r := by linarith
  have hrpq : r * p + r * q = 16 * r - r ^ 2 := by linear_combination r * hpq16
  have hsq : (r - 8) ^ 2 ≤ 0 := by nlinarith
  have hr8 : r = 8 := by nlinarith [sq_nonneg (r - 8)]
  subst hr8
  have he1 : T1 = 8 * p := by linarith
  have he2 : T2 = 8 * q := by linarith
  have hpq : p + q = 8 := by linarith
  have hE1z : E1 = 0 := by
    have h : E1 ^ 2 = 0 := by nlinarith
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
  have hE2z : E2 = 0 := by
    have h : E2 ^ 2 = 0 := by nlinarith
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
  have hK : K = p * q := by
    rw [hE1z, hE2z, he1, he2] at hkey
    nlinarith [hkey]
  have h64 : p ^ 2 + 2 * (p * q) + q ^ 2 = 64 := by linear_combination (p + q + 8) * hpq
  rw [hacsq, hE1z, hE2z, hK]
  linarith [h64]

/-- The purely algebraic content of the problem, in coordinates. -/
lemma algebraic_core (a0 a1 b0 b1 c0 c1 d0 d1 p q r ac : ℝ)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hp2 : p ^ 2 = (a0 - b0) ^ 2 + (a1 - b1) ^ 2)
    (hq2 : q ^ 2 = (d0 - c0) ^ 2 + (d1 - c1) ^ 2)
    (hr2 : r ^ 2 = (b0 - d0) ^ 2 + (b1 - d1) ^ 2)
    (hac2 : ac ^ 2 = (a0 - c0) ^ 2 + (a1 - c1) ^ 2)
    (harea : ((a0 * b1 - b0 * a1) + (b0 * c1 - c0 * b1) + (c0 * d1 - d0 * c1) +
      (d0 * a1 - a0 * d1)) / 2 = 32)
    (hsum : p + r + q = 16) : ac ^ 2 = 128 := by
  refine core_ineq p q r ac
    ((d0 - b0) * (a1 - b1) - (d1 - b1) * (a0 - b0))
    ((b0 - d0) * (c1 - d1) - (b1 - d1) * (c0 - d0))
    ((d0 - b0) * (a0 - b0) + (d1 - b1) * (a1 - b1))
    ((b0 - d0) * (c0 - d0) + (b1 - d1) * (c1 - d1))
    ((a0 - b0) * (d0 - c0) + (a1 - b1) * (d1 - c1))
    hp hq hr ?_ ?_ ?_ ?_ ?_ hsum
  · linarith
  · rw [hr2, hp2]; ring
  · rw [hr2, hq2]; ring
  · rw [hr2]; ring
  · rw [hac2, hp2, hq2, hr2]; ring

/-- **IMO 1976, Problem 1.**  In a convex quadrilateral `ABCD` of area `32` with
`AB + BD + DC = 16`, the other diagonal has length `8 * √2`.

Here `AB` and `DC` are the two opposite sides and `BD` is the given diagonal; `AC` is the
other diagonal. -/
theorem imo1976_p1 (A B C D : Pt) (hconv : ConvexCCW A B C D)
    (harea : |area A B C D| = 32)
    (hsum : dist A B + dist B D + dist D C = 16) :
    dist A C = 8 * Real.sqrt 2 := by
  obtain ⟨-, hc2, -, hc4⟩ := hconv
  simp only [cross] at hc2 hc4
  simp only [area] at harea
  rw [abs_of_pos (by linarith)] at harea
  have hAC : dist A C ^ 2 = 128 :=
    algebraic_core (A 0) (A 1) (B 0) (B 1) (C 0) (C 1) (D 0) (D 1)
      (dist A B) (dist D C) (dist B D) (dist A C)
      dist_nonneg dist_nonneg dist_nonneg (dist_sq A B) (dist_sq D C) (dist_sq B D)
      (dist_sq A C) harea (by linarith)
  have h1 : dist A C = Real.sqrt 128 := by rw [← hAC, Real.sqrt_sq dist_nonneg]
  rw [h1, show (128 : ℝ) = 8 ^ 2 * 2 by norm_num, Real.sqrt_mul (by positivity),
    Real.sqrt_sq (by norm_num)]

/-- The value `8 * √2` is attained: an explicit convex quadrilateral of area `32` with
`AB + BD + DC = 16` and `AC = 8 * √2`. -/
theorem imo1976_p1_attained :
    ∃ A B C D : Pt, ConvexCCW A B C D ∧ |area A B C D| = 32 ∧
      dist A B + dist B D + dist D C = 16 ∧ dist A C = 8 * Real.sqrt 2 := by
  have h16 : Real.sqrt 16 = 4 := by
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have h64 : Real.sqrt 64 = 8 := by
    rw [show (64 : ℝ) = 8 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have h128 : Real.sqrt 128 = 8 * Real.sqrt 2 := by
    rw [show (128 : ℝ) = 8 ^ 2 * 2 by norm_num, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by norm_num)]
  refine ⟨!₂[0, 4], !₂[0, 0], !₂[8, -4], !₂[8, 0], ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · norm_num [cross]
  · norm_num [cross]
  · norm_num [cross]
  · norm_num [cross]
  · norm_num [area]
  · norm_num [EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.dist_eq, h16, h64]
  · norm_num [EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.dist_eq, h128]

end IMO1976P1
