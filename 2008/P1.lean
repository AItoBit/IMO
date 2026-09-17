import Mathlib

/-!
# IMO 2008, Problem 1

An acute triangle `ABC` has orthocentre `H`. The circle through `H` centred at the midpoint of
`BC` meets line `BC` at `A₁, A₂`; likewise for `CA` and `AB`. Show that
`A₁, A₂, B₁, B₂, C₁, C₂` lie on a circle.

## Set-up

Put the circumcentre at the origin, so `|A| = |B| = |C| = R` and the orthocentre is
`H = A + B + C` (the standard vector identity). This is a genuine WLOG: a translation.

`Mₐ = (B+C)/2` is the midpoint of `BC`, and the `A`-circle is the one centred at `Mₐ` through
`H`. A point of line `BC` is `Mₐ + t(C - B)`, and it lies on that circle exactly when
`|t(C-B)|² = |Mₐ - H|²`. That pair of conditions is `OnCircleA` below, stated in coordinates.

## Proof

The whole problem is the single computation

  `|Mₐ + t(C-B)|² = |Mₐ|² + 2t·⟨Mₐ, C-B⟩ + |t(C-B)|²
                  = |Mₐ|² + 0 + |Mₐ - H|²
                  = 2R² + ⟨A,B⟩ + ⟨B,C⟩ + ⟨C,A⟩`,

whose value is symmetric in `A, B, C`. The middle term vanishes because
`⟨(B+C)/2, C-B⟩ = (|C|² - |B|²)/2 = 0`, i.e. `OMₐ ⊥ BC`; and `Mₐ - H = -(A + (B+C)/2)`, so
`|Mₐ|² + |Mₐ-H|² = 2|Mₐ|² + |A|² + 2⟨A,Mₐ⟩`, which expands to the symmetric expression above.

So all six points lie on the circle centred at the circumcentre with squared radius
`2R² + ⟨A,B⟩ + ⟨B,C⟩ + ⟨C,A⟩`. In particular the common circle is concentric with the
circumcircle — the write-up reaches the same conclusion at the end ("the circumcentre of
`C₁C₂B₁B₂` is the circumcentre of `ABC`"), but only after a similar-triangles and
radical-axis argument; here it drops out of the computation.

Note the acuteness hypothesis is not needed for the concyclicity: it only guarantees that the
circles really do meet the lines, which here is an assumption on the given points.
-/

namespace Imo2008P1

/-- `(p₁, p₂)` is one of the two points where the circle through the orthocentre `A + B + C`
centred at the midpoint of `BC` meets the line `BC`. -/
def OnCircleA (a1 a2 b1 b2 c1 c2 p1 p2 : ℝ) : Prop :=
  ∃ t : ℝ,
    p1 = (b1 + c1) / 2 + t * (c1 - b1) ∧
    p2 = (b2 + c2) / 2 + t * (c2 - b2) ∧
    (t * (c1 - b1)) ^ 2 + (t * (c2 - b2)) ^ 2
      = ((b1 + c1) / 2 - (a1 + b1 + c1)) ^ 2 + ((b2 + c2) / 2 - (a2 + b2 + c2)) ^ 2

/-- The computation behind the whole problem. -/
theorem key (a1 a2 b1 b2 c1 c2 R t : ℝ)
    (hA : a1 ^ 2 + a2 ^ 2 = R ^ 2) (hB : b1 ^ 2 + b2 ^ 2 = R ^ 2)
    (hC : c1 ^ 2 + c2 ^ 2 = R ^ 2)
    (hdist : (t * (c1 - b1)) ^ 2 + (t * (c2 - b2)) ^ 2
      = ((b1 + c1) / 2 - (a1 + b1 + c1)) ^ 2 + ((b2 + c2) / 2 - (a2 + b2 + c2)) ^ 2) :
    ((b1 + c1) / 2 + t * (c1 - b1)) ^ 2 + ((b2 + c2) / 2 + t * (c2 - b2)) ^ 2
      = 2 * R ^ 2 + (a1 * b1 + a2 * b2) + (b1 * c1 + b2 * c2) + (c1 * a1 + c2 * a2) := by
  linear_combination hA + (1 / 2 - t) * hB + (1 / 2 + t) * hC + hdist

/-- **IMO 2008 P1.** Every one of the six points lies on the circle centred at the circumcentre
with squared radius `2R² + ⟨A,B⟩ + ⟨B,C⟩ + ⟨C,A⟩`. -/
theorem imo2008_p1 (a1 a2 b1 b2 c1 c2 R : ℝ)
    (hA : a1 ^ 2 + a2 ^ 2 = R ^ 2) (hB : b1 ^ 2 + b2 ^ 2 = R ^ 2)
    (hC : c1 ^ 2 + c2 ^ 2 = R ^ 2)
    (p1 p2 : ℝ)
    (hp : OnCircleA a1 a2 b1 b2 c1 c2 p1 p2 ∨ OnCircleA b1 b2 c1 c2 a1 a2 p1 p2
        ∨ OnCircleA c1 c2 a1 a2 b1 b2 p1 p2) :
    p1 ^ 2 + p2 ^ 2
      = 2 * R ^ 2 + (a1 * b1 + a2 * b2) + (b1 * c1 + b2 * c2) + (c1 * a1 + c2 * a2) := by
  rcases hp with ⟨t, h1, h2, hd⟩ | ⟨t, h1, h2, hd⟩ | ⟨t, h1, h2, hd⟩
  · rw [h1, h2]
    linarith [key a1 a2 b1 b2 c1 c2 R t hA hB hC hd]
  · rw [h1, h2]
    linarith [key b1 b2 c1 c2 a1 a2 R t hB hC hA hd]
  · rw [h1, h2]
    linarith [key c1 c2 a1 a2 b1 b2 R t hC hA hB hd]

end Imo2008P1
