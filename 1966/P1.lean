import Mathlib

/--
Formalization of the contest problem, following the given solution.
* `a`        = number of students who solved B and C but not A;
* `2*x - a`  = number who solved B only,  `x - a` = number who solved C only
  (`x` a positive integer and `a ≤ x`, so `x - a ≥ 0`);
* `2*y - 1`  = number who solved A, and `y` = number who solved only A.
The two stated conditions become `h_total` and `h_half`.  We prove that the
number of students who solved only problem B, namely `2*x - a`, is `6`.
No `sorry`, no `axiom` declarations: `omega` gives a kernel‑checkable
Presburger‑arithmetic proof. -/
theorem contest_b_only (x y a : ℤ)
    (_hx : 0 < x) (_hy : 0 < y) (_ha : 0 < a)
    (_hxa : a ≤ x)                        -- i.e. `x - a ≥ 0`
    (_h_total : 2 * y - 1 + 3 * x - a = 25)
    (_h_half  : y = 3 * x - 2 * a) :
    2 * x - a = 6 := by
  -- Eliminating `y` from the two conditions gives `9x - 5a = 26`.
  have _hD : 9 * x - 5 * a = 26 := by omega
  -- With `1 ≤ a` and `a ≤ x`, the Diophantine equation forces `x = 4`, `a = 2`
  -- (the next solution `x = 9, a = 11` violates `a ≤ x`).
  have _hx4 : x = 4 := by omega
  have _ha2 : a = 2 := by omega
  -- Hence “B only” `= 2*x - a = 8 - 2 = 6`.
  omega
