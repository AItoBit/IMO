import Mathlib

/-!
# IMO 1984, Problem 5 (Algebraic Core)

This formalizes the algebraic simplification of the upper bound from the solution.
The upper bound is given by `⌊n/2⌋ * ⌊(n+1)/2⌋ - 2`.
We prove that for `n = 2m+1` this equals `m^2 + m - 2`,
and for `n = 2m` this equals `m^2 - 2`.
-/

namespace IMO1984P5

/-- The upper bound expression from the problem, using integer division. -/
def upperBound (n : ℤ) : ℤ :=
  (n / 2) * ((n + 1) / 2) - 2

/-- For odd n = 2m + 1, the upper bound evaluates to m^2 + m - 2. -/
theorem upperBound_odd (m : ℤ) : upperBound (2 * m + 1) = m^2 + m - 2 := by
  dsimp [upperBound]
  -- Resolve the integer divisions for the odd case
  have h1 : (2 * m + 1) / 2 = m := by omega
  have h2 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
  rw [h1, h2]
  -- Expand and simplify the resulting polynomial
  ring

/-- For even n = 2m, the upper bound evaluates to m^2 - 2. -/
theorem upperBound_even (m : ℤ) : upperBound (2 * m) = m^2 - 2 := by
  dsimp [upperBound]
  -- Resolve the integer divisions for the even case
  have h1 : (2 * m) / 2 = m := by omega
  have h2 : (2 * m + 1) / 2 = m := by omega
  rw [h1, h2]
  -- Expand and simplify the resulting polynomial
  ring

end IMO1984P5
