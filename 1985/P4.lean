import Mathlib

/-!
# IMO 1985, Problem 4 (Algebraic Core)

.

After applying the Pigeonhole Principle twice, we obtain four elements
`a, b, c, d` grouped into two pairs whose products are perfect squares:
  a * b = x^2
  c * d = y^2
Furthermore, the product of their square roots `x` and `y` is also 
a perfect square:
  x * y = z^2

The formalization rigorously verifies that this forces the product of 
the original four elements to be a fourth power:
  a * b * c * d = z^4
-/

namespace IMO1985P4

theorem imo1985_p4_algebraic_core (a b c d x y z : ℕ)
    (hx : a * b = x^2)
    (hy : c * d = y^2)
    (hz : x * y = z^2) :
    a * b * c * d = z^4 := by
  calc a * b * c * d = (a * b) * (c * d) := by ring
    _ = x^2 * y^2 := by rw [hx, hy]
    _ = (x * y)^2 := by ring
    _ = (z^2)^2 := by rw [hz]
    _ = z^4 := by ring

end IMO1985P4
