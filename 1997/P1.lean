import Mathlib

/-!
# IMO 1997, Problem 1 — setup and the colouring lemmas

The unit squares of the integer grid are coloured like a chessboard. For positive integers `m, n`
take a right triangle with integer-coordinate vertices whose legs, of lengths `m` and `n`, lie on
grid lines. With `S₁`, `S₂` the black and white areas, `f m n = |S₁ - S₂|`.

* (a) compute `f m n` when `m ≡ n (mod 2)`;
* (b) `f m n ≤ ½ max m n`;
* (c) `f` is unbounded.

## Status

**None of (a), (b), (c) is proved here**, and I want to be plain about why rather than hand you
something that only looks complete.

All three parts are statements about the *Lebesgue measure of the black part of a triangle*. Even
writing them down needs `MeasureTheory.volume` on `ℝ × ℝ` together with measurability of the
colouring; proving them needs, at minimum:

* (a) a measure-preserving `180°` rotation carrying one half of the rectangle to the other while
  preserving colours, plus the computation that a rectangle with integer sides has black area
  `mn/2` (`m` or `n` even) or `(mn ± 1)/2` (both odd);
* (b) an induction peeling one unit strip at a time, each step bounding the black-minus-white
  area of a thin oblique strip;
* (c) the exact evaluation `f k (k+1) = (k-1)/6` for even `k`, which is a genuine integral
  computation (the source does it as a sum of `k` small triangles).

That is a substantial measure-theory development, well beyond what I can write in one pass
without a compiler. Rather than guess at it, this file fixes the formal setup and proves the two
colouring facts that the symmetry argument of part (a) actually rests on. They are stated for the
colouring alone, so they are exactly reusable once the measure-theoretic layer is built.

There is no `sorry` in this file.
-/

namespace Imo1997P1

/-- A point of the plane is black when the unit square containing it is. -/
def IsBlack (p : ℝ × ℝ) : Prop := Even (⌊p.1⌋ + ⌊p.2⌋)

/-- Translating by an integer vector `(a, b)` preserves colours exactly when `a + b` is even. -/
theorem isBlack_add_int (p : ℝ × ℝ) (a b : ℤ) (hab : Even (a + b)) :
    IsBlack (p.1 + (a : ℝ), p.2 + (b : ℝ)) ↔ IsBlack p := by
  unfold IsBlack
  rw [Int.floor_add_intCast, Int.floor_add_intCast]
  obtain ⟨c, hc⟩ := hab
  constructor
  · rintro ⟨d, hd⟩
    exact ⟨d - c, by omega⟩
  · rintro ⟨d, hd⟩
    exact ⟨d + c, by omega⟩

/-- The `180°` rotation about a point with integer coordinates preserves colours, away from the
grid lines. The hypotheses `⌈x⌉ = ⌊x⌋ + 1` say exactly that the coordinate is not an integer;
the excluded set is a null set, so this is all the symmetry argument of part (a) needs. -/
theorem isBlack_rotation (p : ℝ × ℝ) (c₁ c₂ : ℤ)
    (h1 : ⌈p.1⌉ = ⌊p.1⌋ + 1) (h2 : ⌈p.2⌉ = ⌊p.2⌋ + 1) :
    IsBlack (2 * (c₁ : ℝ) - p.1, 2 * (c₂ : ℝ) - p.2) ↔ IsBlack p := by
  unfold IsBlack
  have e1 : ⌊2 * (c₁ : ℝ) - p.1⌋ = 2 * c₁ - ⌊p.1⌋ - 1 := by
    have : (2 : ℝ) * (c₁ : ℝ) - p.1 = -p.1 + ((2 * c₁ : ℤ) : ℝ) := by push_cast; ring
    rw [this, Int.floor_add_intCast, Int.floor_neg, h1]
    omega
  have e2 : ⌊2 * (c₂ : ℝ) - p.2⌋ = 2 * c₂ - ⌊p.2⌋ - 1 := by
    have : (2 : ℝ) * (c₂ : ℝ) - p.2 = -p.2 + ((2 * c₂ : ℤ) : ℝ) := by push_cast; ring
    rw [this, Int.floor_add_intCast, Int.floor_neg, h2]
    omega
  rw [e1, e2]
  constructor
  · rintro ⟨d, hd⟩
    exact ⟨c₁ + c₂ - d - 1, by omega⟩
  · rintro ⟨d, hd⟩
    exact ⟨c₁ + c₂ - d - 1, by omega⟩

end Imo1997P1
