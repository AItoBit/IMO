/-
# IMO 1982, Problem 1

`f` is defined on the positive integers with non-negative integer values,
`f 2 = 0`, `f 3 > 0`, `f 9999 = 3333`, and

  `f (m + n) - f m - f n = 0` or `1`  for all `m, n`.

Determine `f 1982`.

The answer is `f 1982 = 660`.

## Modelling

`f : ℕ → ℕ` (so values are automatically non-negative), with the functional
hypothesis restricted to `m, n ≥ 1` and stated without subtraction:

  `f (m + n) = f m + f n ∨ f (m + n) = f m + f n + 1`.

`f 0` is unconstrained.

## Proof

Only superadditivity is needed; the exact values `f (3k) = k` of Solutions 1
and 3 are never used.

* `f (m + n) ≥ f m + f n`, hence `f (k * m) ≥ k * f m`.
* `f 2 ≥ 2 f 1` gives `f 1 = 0`; then `f 3 ∈ {f 2 + f 1, f 2 + f 1 + 1} = {0,1}`
  and `f 3 > 0` gives `f 3 = 1`.
* Lower bound: `f 1982 ≥ f 1980 + f 2 ≥ 660 · f 3 = 660`.
* Upper bound: `9999 = 5·1982 + 89` and `89 = 87 + 2`, so
  `3333 = f 9999 ≥ 5 f 1982 + f 89 ≥ 5 f 1982 + 29 f 3 = 5 f 1982 + 29`,
  giving `5 f 1982 ≤ 3304`, i.e. `f 1982 ≤ 660`.
-/

import Mathlib

namespace Imo1982P1

/-- **IMO 1982, Problem 1.** -/
theorem imo1982_p1 (f : ℕ → ℕ)
    (h : ∀ m n, 1 ≤ m → 1 ≤ n → f (m + n) = f m + f n ∨ f (m + n) = f m + f n + 1)
    (h2 : f 2 = 0) (h3 : 0 < f 3) (h9999 : f 9999 = 3333) :
    f 1982 = 660 := by
  -- superadditivity
  have super : ∀ m n, 1 ≤ m → 1 ≤ n → f m + f n ≤ f (m + n) := by
    intro m n hm hn
    rcases h m n hm hn with hh | hh <;> omega
  -- `f 1 = 0`
  have hf1 : f 1 = 0 := by
    have hs := super 1 1 (by omega) (by omega)
    norm_num at hs
    omega
  -- `f 3 = 1`
  have hf3 : f 3 = 1 := by
    have hd := h 2 1 (by omega) (by omega)
    norm_num at hd
    omega
  -- `f (k * m) ≥ k * f m`
  have mult : ∀ k m, 1 ≤ k → 1 ≤ m → k * f m ≤ f (k * m) := by
    intro k
    induction k with
    | zero => intro m hk hm; omega
    | succ j ih =>
      intro m hk hm
      rcases Nat.eq_zero_or_pos j with hj | hj
      · subst hj; simp
      · have h1 := ih m hj hm
        have h2' := super (j * m) m (Nat.mul_pos hj hm) hm
        have e : (j + 1) * m = j * m + m := by ring
        have e2 : (j + 1) * f m = j * f m + f m := by ring
        rw [e, e2]
        omega
  -- lower bound
  have hl : 660 * f 3 ≤ f 1980 := by
    have hm := mult 660 3 (by omega) (by omega)
    norm_num at hm
    exact hm
  have hlow : 660 ≤ f 1982 := by
    have hs := super 1980 2 (by omega) (by omega)
    norm_num at hs
    omega
  -- upper bound
  have h87 : 29 * f 3 ≤ f 87 := by
    have hm := mult 29 3 (by omega) (by omega)
    norm_num at hm
    exact hm
  have h89 : 29 ≤ f 89 := by
    have hs := super 87 2 (by omega) (by omega)
    norm_num at hs
    omega
  have h9910 : 5 * f 1982 ≤ f 9910 := by
    have hm := mult 5 1982 (by omega) (by omega)
    norm_num at hm
    exact hm
  have hup : f 1982 ≤ 660 := by
    have hs := super 9910 89 (by omega) (by omega)
    norm_num at hs
    omega
  omega

end Imo1982P1
