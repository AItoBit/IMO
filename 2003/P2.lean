import Mathlib

/-!
# IMO 2003, Problem 2

Determine all pairs `(a, b)` of positive integers such that `a² / (2ab² - b³ + 1)` is a positive
integer.

Answer: `(2n, 1)`, `(n, 2n)` and `(8n⁴ - n, 2n)` for positive integers `n`.

## Proof

Being a positive integer is `∃ k > 0, a² = k (2ab² - b³ + 1)`; note this already forces the
denominator to be positive, since `a² > 0`.

If `b = 1` the denominator is `2a`, so `a² = 2ka` and `a = 2k`.

If `b > 1`, put `a' = 2kb² - a`. Then `a a' = k(b³ - 1) > 0`, so `a'` is a positive integer, and
`a'` satisfies the same equation with the same `k`. The key step (`key` below) is: if
`a² ≤ k(b³ - 1)`, then `b = 2a` and `k = a²`. Indeed `a² = kD` gives `D ≤ b³ - 1`, hence
`a < b`; also `k ≥ 1` gives `D ≤ a² < b²`. Writing `D = (2a - b)b² + 1`, the bounds `0 < D < b²`
force `2a - b ≥ 0` and `2a - b ≤ 0`, so `b = 2a`, and then `D = 1` and `k = a²`.

Now either `a ≤ a'`, and then `a² ≤ a a' = k(b³-1)` gives `(a, b) = (n, 2n)` with `n = a`; or
`a' < a`, and then `a'² ≤ a a' = k(b³-1)` gives `b = 2a'` and `k = a'²`, whence
`a = k(b³-1)/a' = 8a'⁴ - a'`.

## A remark on the write-up

The AoPS solution says "without loss of generality, let `a' ≥ a`". That is not a symmetry of the
situation: `a` is given and `a'` is determined by it. What is true is that the *other* case gives
the third family rather than the second, which is why three families appear in the answer and
only two in the displayed argument. Both cases are treated below.
-/

namespace Imo2003P2

/-- The key step: if the product of the two roots is at least `a²`, the pair is `(n, 2n)`. -/
theorem key {a b k : ℤ} (ha : 0 < a) (hb : 1 < b) (hk : 0 < k)
    (hak : a ^ 2 = k * (2 * a * b ^ 2 - b ^ 3 + 1))
    (hle : a ^ 2 ≤ k * (b ^ 3 - 1)) :
    b = 2 * a ∧ k = a ^ 2 := by
  have ha2 : 0 < a ^ 2 := by positivity
  have hb2sq : 0 < b ^ 2 := by positivity
  have hb2four : (4 : ℤ) ≤ b ^ 2 := by nlinarith
  -- the denominator is positive
  have hDpos : 0 < 2 * a * b ^ 2 - b ^ 3 + 1 := by
    by_contra hcon
    push Not at hcon
    nlinarith [hak, hk, ha2, hcon]
  -- `D ≤ b³ - 1`, hence `a < b`
  have h1 : 2 * a * b ^ 2 - b ^ 3 + 1 ≤ b ^ 3 - 1 := by
    have h0 : k * (2 * a * b ^ 2 - b ^ 3 + 1) ≤ k * (b ^ 3 - 1) := by linarith [hak, hle]
    exact le_of_mul_le_mul_left h0 hk
  have hab : a < b := by nlinarith [h1, hb2sq]
  -- `D ≤ a² < b²`
  have hDa : 2 * a * b ^ 2 - b ^ 3 + 1 ≤ a ^ 2 := by nlinarith [hak, hk, hDpos]
  have hab2 : a ^ 2 < b ^ 2 := by nlinarith [hab, ha]
  -- `0 < (2a - b)b² + 1 < b²` pins `2a = b`
  have hge : 0 ≤ 2 * a - b := by
    by_contra hcon
    push Not at hcon
    have h3 : 2 * a - b ≤ -1 := by omega
    have hprod : 0 ≤ (-1 - (2 * a - b)) * b ^ 2 := mul_nonneg (by linarith) (by positivity)
    nlinarith [hDpos, hb2four, hprod]
  have hle2 : 2 * a - b ≤ 0 := by
    by_contra hcon
    push Not at hcon
    have h3 : 1 ≤ 2 * a - b := by omega
    have hprod : 0 ≤ (2 * a - b - 1) * b ^ 2 := mul_nonneg (by linarith) (by positivity)
    nlinarith [hDa, hab2, hprod]
  have hbe : b = 2 * a := by omega
  refine ⟨hbe, ?_⟩
  subst hbe
  linear_combination -hak

/-- **IMO 2003 P2.** -/
theorem imo2003_p2 (a b : ℤ) (ha : 0 < a) (hb : 0 < b) :
    (∃ k : ℤ, 0 < k ∧ a ^ 2 = k * (2 * a * b ^ 2 - b ^ 3 + 1)) ↔
      (∃ n : ℤ, 0 < n ∧ ((a = 2 * n ∧ b = 1) ∨ (a = n ∧ b = 2 * n) ∨
        (a = 8 * n ^ 4 - n ∧ b = 2 * n))) := by
  constructor
  · rintro ⟨k, hk, hak⟩
    have ha2 : 0 < a ^ 2 := by positivity
    have hb1 : 1 ≤ b := by omega
    rcases eq_or_lt_of_le hb1 with h | hb2
    · -- `b = 1`
      have hbe : b = 1 := h.symm
      subst hbe
      refine ⟨k, hk, Or.inl ⟨?_, rfl⟩⟩
      exact mul_right_cancel₀ (ne_of_gt ha) (by linear_combination hak)
    · -- `b > 1`: introduce the other root
      obtain ⟨a', ha'⟩ : ∃ a', a' = 2 * k * b ^ 2 - a := ⟨_, rfl⟩
      have hroot : a * a' = k * (b ^ 3 - 1) := by rw [ha']; linear_combination -hak
      have hb3 : 0 < b ^ 3 - 1 := by nlinarith
      have ha'pos : 0 < a' := by
        rcases lt_trichotomy a' 0 with h1 | h1 | h1
        · nlinarith [hroot, hk, hb3, ha, h1]
        · rw [h1, mul_zero] at hroot
          nlinarith [hk, hb3]
        · exact h1
      rcases le_total a a' with hcase | hcase
      · -- `a ≤ a'` : the family `(n, 2n)`
        have hle : a ^ 2 ≤ k * (b ^ 3 - 1) := by
          rw [← hroot]
          nlinarith [hcase, ha]
        obtain ⟨hbe, -⟩ := key ha hb2 hk hak hle
        exact ⟨a, ha, Or.inr (Or.inl ⟨rfl, hbe⟩)⟩
      · -- `a' < a` : the family `(8n⁴ - n, 2n)`
        have hak' : a' ^ 2 = k * (2 * a' * b ^ 2 - b ^ 3 + 1) := by
          rw [ha']; linear_combination hak
        have hle' : a' ^ 2 ≤ k * (b ^ 3 - 1) := by
          rw [← hroot]
          nlinarith [hcase, ha'pos]
        obtain ⟨hbe, hke⟩ := key ha'pos hb2 hk hak' hle'
        refine ⟨a', ha'pos, Or.inr (Or.inr ⟨?_, hbe⟩)⟩
        refine mul_right_cancel₀ (ne_of_gt ha'pos) ?_
        rw [hroot, hke, hbe]
        ring
  · rintro ⟨n, hn, (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)⟩
    · exact ⟨n, hn, by rw [h1, h2]; ring⟩
    · exact ⟨n ^ 2, pow_pos hn 2, by rw [h1, h2]; ring⟩
    · exact ⟨n ^ 2, pow_pos hn 2, by rw [h1, h2]; ring⟩

end Imo2003P2
