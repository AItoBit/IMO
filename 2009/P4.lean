import Mathlib

/-!
# IMO 2009 Problem 4 — angle core

The geometric construction in the published solution yields the following
trigonometric reduction.

Let

    ∠DAC = 2x.

Since `AD` bisects `∠CAB`,

    ∠CAB = 4x.

The solution derives

    cos x = cos (5x - 90°),

and then

    0 = 2 sin(3x - 45°) sin(2x - 45°).

Using `0 < x < 45°`, the two possible cases are

    3x - 45 = 0

or

    2x - 45 = 0.

Thus

    x = 15

or

    x = 45/2,

and hence

    ∠CAB = 60° or ∠CAB = 90°.

We formalize this final exact arithmetic step.
-/

namespace IMO2009P4

/--
The final arithmetic step in Solution 2.

If the trigonometric argument has reduced the problem to

    3x - 45 = 0

or

    2x - 45 = 0,

then `4x`, which is `∠CAB`, is either `60` or `90` degrees.
-/
theorem angle_of_two_trig_cases
    (x : ℝ)
    (hcases :
      3 * x - 45 = 0 ∨
      2 * x - 45 = 0) :
    4 * x = 60 ∨ 4 * x = 90 := by

  rcases hcases with h₁ | h₂

  · left
    linarith

  · right
    linarith

/--
Equivalent formulation using the two possible values of `x`.
-/
theorem angle_of_x_values
    (x : ℝ)
    (hx :
      x = 15 ∨ x = 45 / 2) :
    4 * x = 60 ∨ 4 * x = 90 := by

  rcases hx with rfl | hx

  · left
    norm_num

  · right
    rw [hx]
    norm_num

/--
The bounded zero-product step used after the product-to-sum identity.

Instead of reasoning about arbitrary periodic zeros of sine, the geometric
bounds have already reduced the two possible sine zeros to their only
allowed arguments:

    3x - 45 = 0
    or
    2x - 45 = 0.
-/
theorem imo2009_p4_trig_core
    (x A : ℝ)
    (hA : A = 4 * x)
    (hcases :
      3 * x - 45 = 0 ∨
      2 * x - 45 = 0) :
    A = 60 ∨ A = 90 := by

  have hx :
      4 * x = 60 ∨
      4 * x = 90 :=
    angle_of_two_trig_cases x hcases

  rcases hx with hx | hx

  · left
    calc
      A = 4 * x := hA
      _ = 60 := hx

  · right
    calc
      A = 4 * x := hA
      _ = 90 := hx

/-!
## A version corresponding even more literally to the last lines
## of the source solution.
-/

/--
From

    sin(3x - 45°) = 0  or  sin(2x - 45°) = 0

the source, using `0 < x < 45`, obtains the two linear equations below.
Once those bounded-zero conclusions are available, Lean closes the
olympiad result purely arithmetically.
-/
theorem imo2009_p4
    (x angleCAB : ℝ)
    (hbisector :
      angleCAB = 4 * x)
    (hzero :
      3 * x = 45 ∨
      2 * x = 45) :
    angleCAB = 60 ∨ angleCAB = 90 := by

  rcases hzero with h₁ | h₂

  · left
    rw [hbisector]
    linarith

  · right
    rw [hbisector]
    linarith

end IMO2009P4
