/-
# IMO 1977, Problem 5

Let `a, b` be positive integers.  Dividing `a² + b²` by `a + b` gives quotient
`q` and remainder `r`.  Find all pairs `(a, b)` with `q² + r = 1977`.

The answer is `(50, 37), (37, 50), (50, 7), (7, 50)`.

## Modelling

"Quotient `q` and remainder `r`" is `a² + b² = q(a+b) + r` together with
`r < a + b`.  "Find all" is an `iff`.

## Proof

This follows the official solution.

* `2ab ≤ a² + b²` and `r < a + b` give `(a+b)² ≤ 2(q(a+b) + r) < 2(q+1)(a+b)`,
  hence `a + b ≤ 2q + 1`.
* `r ≥ 0` gives `q² ≤ 1977`, so `q ≤ 44`.
* `1977 = q² + r < q² + a + b ≤ q² + 2q + 1 = (q+1)²`, so `q ≥ 44`.

Hence `q = 44`, `r = 41`, and `a² + b² = 44(a+b) + 41`, i.e.

  `(a - 22)² + (b - 22)² = 1009`.

Since `32² = 1024 > 1009` this forces `a, b ≤ 53`, and the remaining finite
search replaces the official "list all squares up to 505 and their differences
from 1009" step.

Each arithmetic step is isolated in its own small lemma: with the whole context
present, `nlinarith` searches over far too many hypothesis products and times
out.
-/

import Mathlib

set_option maxRecDepth 10000

namespace Imo1977P5

/-- `q ≤ 44`, from `q² ≤ 1977`. -/
private lemma qle {q r : ℤ} (hq0 : 0 ≤ q) (hr0 : 0 ≤ r) (h : q ^ 2 + r = 1977) :
    q ≤ 44 := by
  nlinarith

/-- `a + b ≤ 2q + 1`, from `(a+b)² ≤ 2(a²+b²) = 2(q(a+b)+r) < 2(q+1)(a+b)`. -/
private lemma abbound {a b q r : ℤ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hr : r < a + b)
    (h : a ^ 2 + b ^ 2 = q * (a + b) + r) : a + b ≤ 2 * q + 1 := by
  nlinarith [sq_nonneg (a - b)]

/-- `q ≥ 44`, from `1977 = q² + r < q² + 2q + 1`. -/
private lemma qge {a b q r : ℤ} (hq0 : 0 ≤ q) (h : q ^ 2 + r = 1977)
    (hr : r < a + b) (hab : a + b ≤ 2 * q + 1) : 44 ≤ q := by
  nlinarith

/-- From `x² + y² = 1009` and `32² = 1024`, we get `x ≤ 31`. -/
private lemma sq_bound {x y : ℤ} (h : x ^ 2 + y ^ 2 = 1009) : x ≤ 31 := by
  nlinarith [sq_nonneg y]

set_option maxHeartbeats 1000000 in
/-- The finite search: the only solutions of `a² + b² = 44(a+b) + 41` with
`a, b ≤ 53` are the four expected pairs. -/
private lemma enum : ∀ a ∈ Finset.range 54, ∀ b ∈ Finset.range 54,
    a ^ 2 + b ^ 2 = 44 * (a + b) + 41 →
      (a = 50 ∧ b = 37) ∨ (a = 37 ∧ b = 50) ∨ (a = 50 ∧ b = 7) ∨ (a = 7 ∧ b = 50) := by
  decide

/-- **IMO 1977, Problem 5.** -/
theorem imo1977_p5 (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (∃ q r : ℕ, a ^ 2 + b ^ 2 = q * (a + b) + r ∧ r < a + b ∧ q ^ 2 + r = 1977)
      ↔ ((a = 50 ∧ b = 37) ∨ (a = 37 ∧ b = 50) ∨
          (a = 50 ∧ b = 7) ∨ (a = 7 ∧ b = 50)) := by
  constructor
  · rintro ⟨q, r, heq, hr, hqr⟩
    -- everything moves to `ℤ`
    have hq0 : (0 : ℤ) ≤ (q : ℤ) := by exact_mod_cast Nat.zero_le q
    have hr0 : (0 : ℤ) ≤ (r : ℤ) := by exact_mod_cast Nat.zero_le r
    have haZ : (1 : ℤ) ≤ (a : ℤ) := by exact_mod_cast ha
    have hbZ : (1 : ℤ) ≤ (b : ℤ) := by exact_mod_cast hb
    have heqZ : (a : ℤ) ^ 2 + (b : ℤ) ^ 2 = (q : ℤ) * ((a : ℤ) + (b : ℤ)) + (r : ℤ) := by
      exact_mod_cast heq
    have hrZ : (r : ℤ) < (a : ℤ) + (b : ℤ) := by exact_mod_cast hr
    have hqrZ : (q : ℤ) ^ 2 + (r : ℤ) = 1977 := by exact_mod_cast hqr
    -- `q = 44`, `r = 41`
    have hab := abbound haZ hbZ hrZ heqZ
    have h44 : (q : ℤ) = 44 := le_antisymm (qle hq0 hr0 hqrZ) (qge hq0 hqrZ hrZ hab)
    have hr41 : (r : ℤ) = 41 := by
      rw [h44] at hqrZ
      linarith
    have heq44 : a ^ 2 + b ^ 2 = 44 * (a + b) + 41 := by
      have hZ : (a : ℤ) ^ 2 + (b : ℤ) ^ 2 = 44 * ((a : ℤ) + (b : ℤ)) + 41 := by
        rw [h44, hr41] at heqZ
        exact heqZ
      exact_mod_cast hZ
    -- `(a-22)² + (b-22)² = 1009`
    have hsum : ((a : ℤ) - 22) ^ 2 + ((b : ℤ) - 22) ^ 2 = 1009 := by
      have hZ : (a : ℤ) ^ 2 + (b : ℤ) ^ 2 = 44 * ((a : ℤ) + (b : ℤ)) + 41 := by
        exact_mod_cast heq44
      linear_combination hZ
    have hsum' : ((b : ℤ) - 22) ^ 2 + ((a : ℤ) - 22) ^ 2 = 1009 := by linarith
    have ha54 : a < 54 := by
      have h := sq_bound hsum
      omega
    have hb54 : b < 54 := by
      have h := sq_bound hsum'
      omega
    exact enum a (Finset.mem_range.mpr ha54) b (Finset.mem_range.mpr hb54) heq44
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
      exact ⟨44, 41, by norm_num, by norm_num, by norm_num⟩

end Imo1977P5
