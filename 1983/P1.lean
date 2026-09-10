/-
# IMO 1983, Problem 1

Find all `f` on the positive reals, with positive real values, such that

* (i) `f (x * f y) = y * f x` for all `x, y > 0`;
* (ii) `f x → 0` as `x → ∞`.

The answer is `f x = 1/x`.

## Modelling

`f : ℝ → ℝ`, with every hypothesis restricted to positive arguments, and (ii)
as `Tendsto f atTop (nhds 0)`.  The values of `f` on `x ≤ 0` are unconstrained.
The converse (that `1/x` really is a solution) is `imo1983_p1_solution`.

## Proof

1. `f 1 = 1`.  Putting `x = y = 1` gives `f (f 1) = f 1`; putting `x = 1`,
   `y = f 1` gives `f (f (f 1)) = (f 1)²`, and the left side collapses to `f 1`,
   so `f 1 = (f 1)²` with `f 1 > 0`.
2. **No fixed point exceeds 1.**  If `f b = b` then (i) with `y = b` gives
   `f (x b) = b f x`, whence `f (bⁿ) = bⁿ` by induction.  If `b > 1` then
   `bⁿ → ∞`, so `f (bⁿ) → 0` by (ii); but `f (bⁿ) = bⁿ → ∞`.
3. **`1` is the only fixed point.**  If `f a = a` with `a < 1`, then `x = 1/a`
   in `f (x a) = a f x` gives `1 = a f (1/a)`, so `1/a` is a fixed point
   greater than `1`, contradicting 2.
4. Putting `y = x` in (i) gives `f (x f x) = x f x`, so `x f x` is a fixed
   point, hence `x f x = 1`, i.e. `f x = 1/x`.

Steps 2–3 replace the `b^(2^k)` iteration of the AoPS write-up by the plain
powers `bⁿ`, which is enough and lets the limit argument be a single
`not_tendsto_nhds_of_tendsto_atTop`.
-/

import Mathlib

namespace Imo1983P1

/-- **IMO 1983, Problem 1.** -/
theorem imo1983_p1 (f : ℝ → ℝ) (hpos : ∀ x, 0 < x → 0 < f x)
    (hfe : ∀ x y, 0 < x → 0 < y → f (x * f y) = y * f x)
    (hlim : Filter.Tendsto f Filter.atTop (nhds 0)) :
    ∀ x, 0 < x → f x = 1 / x := by
  have hf1pos : 0 < f 1 := hpos 1 one_pos
  -- 1. `f 1 = 1`
  have e1 : f (f 1) = f 1 := by
    have h := hfe 1 1 one_pos one_pos
    simpa using h
  have hf1 : f 1 = 1 := by
    have h := hfe 1 (f 1) one_pos hf1pos
    rw [one_mul, e1, e1] at h
    have h2 : f 1 * (f 1 - 1) = 0 := by linear_combination -h
    rcases mul_eq_zero.mp h2 with h3 | h3
    · linarith
    · linarith
  -- 2. no fixed point is `> 1`
  have no_fix_gt : ∀ b, 1 < b → f b = b → False := by
    intro b hb hfb
    have hb0 : 0 < b := by linarith
    have hpow : ∀ n : ℕ, f (b ^ n) = b ^ n := by
      intro n
      induction n with
      | zero => simpa using hf1
      | succ m ih =>
        have hbm : 0 < b ^ m := pow_pos hb0 m
        have h := hfe (b ^ m) b hbm hb0
        rw [hfb, ih] at h
        rw [pow_succ, h]
        ring
    have h1 : Filter.Tendsto (fun n : ℕ => b ^ n) Filter.atTop Filter.atTop :=
      tendsto_pow_atTop_atTop_of_one_lt hb
    have h2 : Filter.Tendsto (fun n : ℕ => f (b ^ n)) Filter.atTop (nhds 0) :=
      hlim.comp h1
    have h3 : (fun n : ℕ => f (b ^ n)) = fun n : ℕ => b ^ n := funext hpow
    rw [h3] at h2
    exact not_tendsto_nhds_of_tendsto_atTop h1 0 h2
  -- 3. `1` is the only fixed point
  have fixed_eq_one : ∀ a, 0 < a → f a = a → a = 1 := by
    intro a ha hfa
    have hane : a ≠ 0 := ne_of_gt ha
    rcases lt_trichotomy a 1 with h | h | h
    · exfalso
      have hinv : 0 < 1 / a := by positivity
      have hkey := hfe (1 / a) a hinv ha
      rw [hfa, show (1 / a) * a = 1 from by field_simp, hf1] at hkey
      -- `hkey : 1 = a * f (1/a)`
      have hfinv : f (1 / a) = 1 / a := by
        field_simp
        linarith
      have h1a : 1 < 1 / a := by
        have hd : 0 < (1 - a) / a := div_pos (by linarith) ha
        have he : (1 - a) / a = 1 / a - 1 := by field_simp
        rw [he] at hd
        linarith
      exact no_fix_gt (1 / a) h1a hfinv
    · exact h
    · exact absurd hfa (fun hh => no_fix_gt a h hh)
  -- 4. conclude
  intro x hx
  have hfx : 0 < f x := hpos x hx
  have hxf : 0 < x * f x := mul_pos hx hfx
  have hfix : f (x * f x) = x * f x := hfe x x hx hx
  have hone := fixed_eq_one (x * f x) hxf hfix
  field_simp
  linarith

/-- The function `x ↦ 1/x` does satisfy the two conditions. -/
theorem imo1983_p1_solution :
    (∀ x : ℝ, 0 < x → 0 < 1 / x) ∧
    (∀ x y : ℝ, 0 < x → 0 < y → 1 / (x * (1 / y)) = y * (1 / x)) ∧
    Filter.Tendsto (fun x : ℝ => 1 / x) Filter.atTop (nhds 0) := by
  refine ⟨fun x hx => by positivity, fun x y hx hy => by field_simp, ?_⟩
  simpa [one_div] using tendsto_inv_atTop_zero

end Imo1983P1
