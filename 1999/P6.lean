import Mathlib

/-!
# IMO 1999, Problem 6

Determine all `f : ℝ → ℝ` with `f (x - f y) = f (f y) + x * f y + f x - 1` for all `x, y`.

Answer: `f x = 1 - x²/2`.

## Proof

Write `c = f 0`.

* `c ≠ 0`: putting `x = y = 0` with `f 0 = 0` gives `0 = -1`.
* Putting `x = f y` gives `c = 2 f (f y) + (f y)² - 1`, i.e.
  `f (f y) = (c + 1 - (f y)²)/2` — valid for every value `f y` of `f`.
* Putting `x = f z` and substituting the previous line twice,
  `f (f z - f y) = c - (f z - f y)²/2`.
* Every real is such a difference: `x = 0`'s instance reads
  `f (x - c) - f x = f c + c x - 1`, which is a nonconstant affine function of `x` because
  `c ≠ 0`, so it attains every value. Hence `f w = c - w²/2` for **all** `w`.
* Comparing this at `w = c` with `f (f 0) = (c + 1 - c²)/2` gives `c = 1`.

Note the AoPS write-up derives `f x = (c+1)/2 - x²/2` "for all `x`" from the substitution
`x = f y`, which only licenses it on the range of `f` (its own parenthetical admits this), and
then uses evenness of that formula at `-c`. The difference step above closes that gap: it proves
the formula on the *set of differences* of values of `f`, which is all of `ℝ`.
-/

namespace Imo1999P6

theorem imo1999_p6 (f : ℝ → ℝ) :
    (∀ x y : ℝ, f (x - f y) = f (f y) + x * f y + f x - 1) ↔ (∀ x : ℝ, f x = 1 - x ^ 2 / 2) := by
  constructor
  · intro P
    -- `f 0 ≠ 0`
    have hc : f 0 ≠ 0 := by
      intro h
      have h1 := P 0 0
      simp [h] at h1
    -- the formula on the range of `f`
    have hrange : ∀ y : ℝ, f (f y) = (f 0 + 1 - (f y) ^ 2) / 2 := by
      intro y
      have h1 := P (f y) y
      rw [sub_self] at h1
      have hsq : (f y) ^ 2 = f y * f y := pow_two _
      linarith
    -- the formula on differences of values
    have hdiff : ∀ y z : ℝ, f (f z - f y) = f 0 - (f z - f y) ^ 2 / 2 := by
      intro y z
      have h1 := P (f z) y
      rw [hrange y, hrange z] at h1
      rw [h1]
      ring
    -- every real is such a difference
    have hsurj : ∀ w : ℝ, ∃ y z : ℝ, f z - f y = w := by
      intro w
      refine ⟨(w - f (f 0) + 1) / f 0, (w - f (f 0) + 1) / f 0 - f 0, ?_⟩
      have h1 := P ((w - f (f 0) + 1) / f 0) 0
      have hxf : ((w - f (f 0) + 1) / f 0) * f 0 = w - f (f 0) + 1 := by
        field_simp
      rw [h1]
      linarith
    -- hence the formula everywhere
    have hform : ∀ w : ℝ, f w = f 0 - w ^ 2 / 2 := by
      intro w
      obtain ⟨y, z, hyz⟩ := hsurj w
      have h1 := hdiff y z
      rw [hyz] at h1
      exact h1
    -- and `f 0 = 1`
    have hc1 : f 0 = 1 := by
      have h1 := hrange 0
      have h2 := hform (f 0)
      rw [h2] at h1
      linarith
    intro x
    rw [hform x, hc1]
  · intro hf x y
    simp only [hf]
    ring

end Imo1999P6
