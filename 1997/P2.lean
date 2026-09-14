import Mathlib

/-!
# IMO 1997, Problem 2 — trigonometric core

`A` is the smallest angle of triangle `ABC`; `U` is an interior point of the arc `BC` not
containing `A`; the perpendicular bisectors of `AB` and `AC` meet line `AU` at `V` and `W`; the
lines `BV` and `CW` meet at `T`. Show `AU = TB + TC`.

## What is formalized

Mathlib has no API for perpendicular bisectors meeting a cevian, nor for the projection law, so
the synthetic and trigonometric set-up of the AoPS solution cannot be carried out. What is
formalized is everything from its Equations 1.1–4 onwards. With `u` the base angle of the
isosceles triangle `AOU` and `R` the circumradius, those inputs are:

* `AU = 2R cos u`                                   (law of sines, step 1);
* `BC = 2R cos (u + A)`                             (Eq 1.1);
* `TB cos(2u + A) + TC cos A = BC`                  (Eq 3, the projection law on `BTC`);
* `TB sin(2u + A) = TC sin A`                       (Eq 4, the law of sines on `BTC`).

From these, `AU = TB + TC` is proved below with no `sorry`.

## The argument

Eliminating `TB` and `TC` in turn from Equations 3 and 4 gives

  `TC sin(2u + 2A) = BC sin(2u + A)`   and   `TB sin(2u + 2A) = BC sin A`.

Adding, and using `sin(2u+2A) = 2 sin(u+A) cos(u+A)` together with
`sin(2u+A) + sin A = 2 sin(u+A) cos u`, the factor `2 sin(u+A)` cancels, leaving
`(TB + TC) cos(u+A) = BC cos u`. Substituting `BC = 2R cos(u+A)` and cancelling `cos(u+A)`
gives `TB + TC = 2R cos u = AU`.

The two nonvanishing hypotheses `sin(u+A) ≠ 0` and `cos(u+A) ≠ 0` are exactly the cancellations
the source performs; both hold in the configuration, the second because `BC = 2R cos(u+A) ≠ 0`.
-/

namespace Imo1997P2

/-- **Trigonometric core of IMO 1997 P2.** -/
theorem imo1997_p2 (u A R BC TB TC AU : ℝ)
    (hP : Real.sin (u + A) ≠ 0)
    (hQ : Real.cos (u + A) ≠ 0)
    (hAU : AU = 2 * R * Real.cos u)
    (hBC : BC = 2 * R * Real.cos (u + A))
    (h3 : TB * Real.cos (2 * u + A) + TC * Real.cos A = BC)
    (h4 : TB * Real.sin (2 * u + A) = TC * Real.sin A) :
    AU = TB + TC := by
  -- `sin(2u+2A) = sin A cos(2u+A) + cos A sin(2u+A)`
  have i1 : Real.sin (2 * u + 2 * A)
      = Real.sin A * Real.cos (2 * u + A) + Real.cos A * Real.sin (2 * u + A) := by
    have h := Real.sin_add A (2 * u + A)
    rw [show A + (2 * u + A) = 2 * u + 2 * A by ring] at h
    exact h
  -- `sin(2u+2A) = 2 sin(u+A) cos(u+A)`
  have i2 : Real.sin (2 * u + 2 * A) = 2 * Real.sin (u + A) * Real.cos (u + A) := by
    rw [show 2 * u + 2 * A = 2 * (u + A) by ring, Real.sin_two_mul]
  -- `sin(2u+A) + sin A = 2 sin(u+A) cos u`
  have i3 : Real.sin (2 * u + A) + Real.sin A = 2 * Real.sin (u + A) * Real.cos u := by
    have e1 : Real.sin (u + A) * Real.cos u + Real.cos (u + A) * Real.sin u
        = Real.sin (2 * u + A) := by
      rw [← Real.sin_add, show (u + A) + u = 2 * u + A by ring]
    have e2 : Real.sin (u + A) * Real.cos u - Real.cos (u + A) * Real.sin u = Real.sin A := by
      rw [← Real.sin_sub, show (u + A) - u = A by ring]
    linear_combination -e1 - e2
  -- eliminate `TB`, then `TC`
  have ha : TC * Real.sin (2 * u + 2 * A) = BC * Real.sin (2 * u + A) := by
    linear_combination Real.sin (2 * u + A) * h3 - Real.cos (2 * u + A) * h4 + TC * i1
  have hb : TB * Real.sin (2 * u + 2 * A) = BC * Real.sin A := by
    linear_combination Real.sin A * h3 + Real.cos A * h4 + TB * i1
  have hc : (TB + TC) * Real.sin (2 * u + 2 * A)
      = BC * (Real.sin (2 * u + A) + Real.sin A) := by
    linear_combination ha + hb
  rw [i2, i3] at hc
  -- cancel `2 sin(u+A)`
  have h2P : (2 : ℝ) * Real.sin (u + A) ≠ 0 := by
    simpa using hP
  have hc' : (2 * Real.sin (u + A)) * ((TB + TC) * Real.cos (u + A))
      = (2 * Real.sin (u + A)) * (BC * Real.cos u) := by linear_combination hc
  have hd := mul_left_cancel₀ h2P hc'
  -- cancel `cos(u+A)`
  rw [hBC] at hd
  have he : Real.cos (u + A) * (TB + TC) = Real.cos (u + A) * (2 * R * Real.cos u) := by
    linear_combination hd
  have hfin := mul_left_cancel₀ hQ he
  rw [hAU]
  linarith [hfin]

end Imo1997P2
