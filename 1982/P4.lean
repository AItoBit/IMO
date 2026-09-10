/-
# IMO 1982, Problem 4

Prove that if `n` is a positive integer such that `x³ - 3xy² + y³ = n` has a
solution in integers, then it has at least three such solutions.  Show that the
equation has no integer solutions for `n = 2891`.

## Part (a)

The map

  `T (x, y) = (y - x, -x)`

sends solutions to solutions — a direct expansion gives
`(y-x)³ - 3(y-x)(-x)² + (-x)³ = x³ - 3xy² + y³` — and `T³ = id`, since
`T (x,y) = (y-x, -x)`, `T² (x,y) = (-y, x-y)`, `T³ (x,y) = (x,y)`.

So `(x, y)`, `(y - x, -x)`, `(-y, x - y)` are three solutions, and each of the
three possible coincidences forces `x = y = 0`, hence `n = 0`, excluded by
`n > 0`.

## Part (b)

`2891 = 7² · 59`, so `7 ∣ 2891` but `7³ = 343 ∤ 2891`.  An exhaustive check of
the `49` pairs in `ZMod 7` shows

  `a³ - 3ab² + b³ = 0` in `ZMod 7`  ⟹  `a = 0` and `b = 0`,

so any integer solution has `7 ∣ x` and `7 ∣ y`; writing `x = 7a`, `y = 7b`
turns the equation into `343 (a³ - 3ab² + b³) = 2891`, which is impossible.
-/

import Mathlib

namespace Imo1982P4

/-- **IMO 1982, Problem 4 (a).**  A solution yields three pairwise distinct
solutions. -/
theorem imo1982_p4a (n : ℤ) (hn : 0 < n) (x y : ℤ)
    (h : x ^ 3 - 3 * x * y ^ 2 + y ^ 3 = n) :
    ∃ p q r : ℤ × ℤ, p ≠ q ∧ q ≠ r ∧ p ≠ r ∧
      p.1 ^ 3 - 3 * p.1 * p.2 ^ 2 + p.2 ^ 3 = n ∧
      q.1 ^ 3 - 3 * q.1 * q.2 ^ 2 + q.2 ^ 3 = n ∧
      r.1 ^ 3 - 3 * r.1 * r.2 ^ 2 + r.2 ^ 3 = n := by
  -- a solution of a positive `n` is not the zero pair
  have hxy : ¬ (x = 0 ∧ y = 0) := by
    rintro ⟨rfl, rfl⟩
    norm_num at h
    omega
  refine ⟨(x, y), (y - x, -x), (-y, x - y), ?_, ?_, ?_, h, ?_, ?_⟩
  · intro hcon
    rw [Prod.mk.injEq] at hcon
    exact hxy ⟨by omega, by omega⟩
  · intro hcon
    rw [Prod.mk.injEq] at hcon
    exact hxy ⟨by omega, by omega⟩
  · intro hcon
    rw [Prod.mk.injEq] at hcon
    exact hxy ⟨by omega, by omega⟩
  · show (y - x) ^ 3 - 3 * (y - x) * (-x) ^ 2 + (-x) ^ 3 = n
    linear_combination h
  · show (-y) ^ 3 - 3 * (-y) * (x - y) ^ 2 + (x - y) ^ 3 = n
    linear_combination h

/-- **IMO 1982, Problem 4 (b).**  No integer solutions for `n = 2891`. -/
theorem imo1982_p4b : ¬ ∃ x y : ℤ, x ^ 3 - 3 * x * y ^ 2 + y ^ 3 = 2891 := by
  rintro ⟨x, y, h⟩
  -- the only zero of the form modulo `7` is the origin
  have key : ∀ a b : ZMod 7, a ^ 3 - 3 * a * b ^ 2 + b ^ 3 = 0 → a = 0 ∧ b = 0 := by
    decide
  have h2891 : (2891 : ZMod 7) = 0 := by decide
  have hc : ((x : ZMod 7)) ^ 3 - 3 * (x : ZMod 7) * ((y : ZMod 7)) ^ 2
      + ((y : ZMod 7)) ^ 3 = 0 := by
    have hh : ((x ^ 3 - 3 * x * y ^ 2 + y ^ 3 : ℤ) : ZMod 7) = ((2891 : ℤ) : ZMod 7) := by
      rw [h]
    push_cast at hh
    rw [hh, h2891]
  obtain ⟨hx0, hy0⟩ := key _ _ hc
  have hx : (7 : ℤ) ∣ x := by
    have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd x 7).mp hx0
    exact_mod_cast hd
  have hy : (7 : ℤ) ∣ y := by
    have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd y 7).mp hy0
    exact_mod_cast hd
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  obtain ⟨K, hK⟩ : ∃ K : ℤ, a ^ 3 - 3 * a * b ^ 2 + b ^ 3 = K := ⟨_, rfl⟩
  have h2 : 343 * K = 2891 := by rw [← hK]; linear_combination h
  omega

end Imo1982P4
