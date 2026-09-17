import Mathlib

/-!
# IMO 2006, Problem 4

Determine all pairs `(x, y)` of integers with `1 + 2^x + 2^(2x+1) = y^2`.

Answer: `(0, ±2)` and `(4, ±23)`.

## Formalization

`x` is taken in `ℕ` (for negative `x` the left side is not an integer) and `y` in `ℤ`.

## Proof

`x = 0, 1, 2` give `y² = 4, 11, 37`, so only `x = 0` survives. For `x ≥ 3` write `x = k + 3` and
put `P = 2^k ≥ 1`, so the equation reads `1 + 8P + 128P² = y²`. Assume `y > 0`.

`y` is odd, say `y = 2a + 1`; then `a(a+1) = 2P(1+16P)`. Exactly one of `a`, `a+1` is even:

* `a = 2b`: then `b(2b+1) = P(1+16P)`, and `P` is a power of `2` coprime to the odd `2b+1`,
  so `P ∣ b`. Writing `b = Pc` gives `y = 4Pc + 1`.
* `a = 2t+1`: then `(2t+1)(t+1) = P(1+16P)` and likewise `P ∣ t+1`, giving `y = 4Pc - 1`.

This is the write-up's `y = 2^{x-1} m + ε` with `ε = ±1`. Substituting and cancelling `8P`:

* `ε = +1`: `2P(c² - 8) = 1 - c`. Positivity of `y` forces `c ≥ 1`, so the right side is `≤ 0`,
  hence `c² ≤ 8` and `c ≤ 2`; both `c = 1` and `c = 2` fail.
* `ε = -1`: `2P(c² - 8) = 1 + c`. Again `c ≥ 1`, so the right side is positive, forcing `c ≥ 3`;
  and `1 + c ≥ 2(c² - 8)` gives `2c² - c - 17 ≤ 0`, so `c ≤ 3`. Thus `c = 3`, whence `2P = 4`,
  `P = 2`, `k = 1`, `x = 4` and `y = 23`.

Note the argument never needs `m` odd — the write-up's `(∗)` asserts it, but the two branches
close without it.
-/

namespace Imo2006P4

/-- The heart of the problem: for `x = k + 3` and `y > 0` the only solution is `k = 1`, `y = 23`. -/
theorem key (k : ℕ) (y : ℤ) (hy : 0 < y)
    (h : 1 + 8 * 2 ^ k + 128 * ((2 : ℤ) ^ k) ^ 2 = y ^ 2) : k = 1 ∧ y = 23 := by
  have hPpos : (0 : ℤ) < 2 ^ k := by positivity
  have hP1 : (1 : ℤ) ≤ 2 ^ k := by omega
  -- `y` is odd
  have hyo : y % 2 = 1 := by
    rcases Int.emod_two_eq_zero_or_one y with he | ho
    · exfalso
      obtain ⟨c, hc⟩ : ∃ c, y = 2 * c := ⟨y / 2, by omega⟩
      obtain ⟨d, hd⟩ : ∃ d, (1 : ℤ) = 4 * d :=
        ⟨c ^ 2 - 2 * 2 ^ k - 32 * ((2 : ℤ) ^ k) ^ 2, by rw [hc] at h; linear_combination h⟩
      omega
    · exact ho
  obtain ⟨a, ha⟩ : ∃ a, y = 2 * a + 1 := ⟨y / 2, by omega⟩
  have hfac : a * (a + 1) = 2 * 2 ^ k * (1 + 16 * 2 ^ k) := by
    have h4 : 4 * (a * (a + 1)) = 4 * (2 * 2 ^ k * (1 + 16 * 2 ^ k)) := by
      rw [ha] at h; linear_combination -h
    linarith
  rcases Int.emod_two_eq_zero_or_one a with hae | hao
  · -- `a` even: `y = 4Pc + 1`
    exfalso
    obtain ⟨b, hb⟩ : ∃ b, a = 2 * b := ⟨a / 2, by omega⟩
    have hb2 : b * (2 * b + 1) = 2 ^ k * (1 + 16 * 2 ^ k) := by
      have h2 : 2 * (b * (2 * b + 1)) = 2 * (2 ^ k * (1 + 16 * 2 ^ k)) := by
        rw [hb] at hfac; linear_combination hfac
      linarith
    have hcop : IsCoprime ((2 : ℤ) ^ k) (2 * b + 1) := IsCoprime.pow_left ⟨-b, 1, by ring⟩
    obtain ⟨c, hc⟩ : (2 : ℤ) ^ k ∣ b := hcop.dvd_of_dvd_mul_right ⟨1 + 16 * 2 ^ k, hb2⟩
    have hy4 : y = 4 * 2 ^ k * c + 1 := by rw [ha, hb, hc]; ring
    have heq2 : 1 + 16 * 2 ^ k = 2 * 2 ^ k * c ^ 2 + c := by
      refine mul_left_cancel₀ (a := (8 : ℤ) * 2 ^ k) (by positivity) ?_
      rw [hy4] at h; linear_combination h
    have hkey : 2 * 2 ^ k * (c ^ 2 - 8) = 1 - c := by linarith
    -- `c ≥ 1`
    have hc1 : 1 ≤ c := by
      by_contra hcon
      have hc0 : c ≤ 0 := by omega
      have hle : y ≤ 1 := by rw [hy4]; nlinarith
      have hy1 : y = 1 := by omega
      rw [hy1] at h
      nlinarith
    have hc2 : c ≤ 2 := by nlinarith
    interval_cases c <;> linarith
  · -- `a` odd: `y = 4Pc - 1`
    obtain ⟨t, ht⟩ : ∃ t, a = 2 * t + 1 := ⟨a / 2, by omega⟩
    have hb2 : (2 * t + 1) * (t + 1) = 2 ^ k * (1 + 16 * 2 ^ k) := by
      have h2 : 2 * ((2 * t + 1) * (t + 1)) = 2 * (2 ^ k * (1 + 16 * 2 ^ k)) := by
        rw [ht] at hfac; linear_combination hfac
      linarith
    have hcop : IsCoprime ((2 : ℤ) ^ k) (2 * t + 1) := IsCoprime.pow_left ⟨-t, 1, by ring⟩
    obtain ⟨c, hc⟩ : (2 : ℤ) ^ k ∣ (t + 1) := hcop.dvd_of_dvd_mul_left ⟨1 + 16 * 2 ^ k, hb2⟩
    have hy4 : y = 4 * 2 ^ k * c - 1 := by rw [ha, ht]; linarith
    have heq2 : 1 + 16 * 2 ^ k = 2 * 2 ^ k * c ^ 2 - c := by
      refine mul_left_cancel₀ (a := (8 : ℤ) * 2 ^ k) (by positivity) ?_
      rw [hy4] at h; linear_combination h
    have hkey : 2 * 2 ^ k * (c ^ 2 - 8) = 1 + c := by linarith
    have hc1 : 1 ≤ c := by nlinarith
    have hc3 : 3 ≤ c := by nlinarith
    have hc4 : c ≤ 3 := by
      nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ 2 ^ k - 1) (by nlinarith : (0 : ℤ) ≤ c ^ 2 - 8)]
    have hce : c = 3 := by omega
    subst hce
    have hPe : (2 : ℤ) ^ k = 2 := by linarith
    have hk1 : k = 1 := by
      rcases Nat.lt_or_ge k 2 with hlt | hge
      · interval_cases k
        · exfalso; norm_num at hPe
        · rfl
      · exfalso
        have hnat : (4 : ℕ) ≤ 2 ^ k := by
          calc (4 : ℕ) = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hge
        have h4 : (4 : ℤ) ≤ (2 : ℤ) ^ k := by exact_mod_cast hnat
        linarith
    exact ⟨hk1, by rw [hy4, hPe]; ring⟩

/-- **IMO 2006 P4.** -/
theorem imo2006_p4 (x : ℕ) (y : ℤ) :
    1 + 2 ^ x + 2 ^ (2 * x + 1) = y ^ 2 ↔
      (x = 0 ∧ (y = 2 ∨ y = -2)) ∨ (x = 4 ∧ (y = 23 ∨ y = -23)) := by
  constructor
  · intro h
    rcases Nat.lt_or_ge x 3 with hlt | hge
    · interval_cases x
      · left
        refine ⟨rfl, ?_⟩
        have h4 : y ^ 2 = 4 := by norm_num at h; linarith
        have hz : (y - 2) * (y + 2) = 0 := by linear_combination h4
        rcases mul_eq_zero.1 hz with h1 | h1
        · left; linarith
        · right; linarith
      · exfalso
        have h11 : y ^ 2 = 11 := by norm_num at h; linarith
        have hb1 : -4 < y := by nlinarith
        have hb2 : y < 4 := by nlinarith
        interval_cases y <;> norm_num at h11
      · exfalso
        have h37 : y ^ 2 = 37 := by norm_num at h; linarith
        have hb1 : -7 < y := by nlinarith
        have hb2 : y < 7 := by nlinarith
        interval_cases y <;> norm_num at h37
    · right
      obtain ⟨k, hk⟩ : ∃ k, x = k + 3 := ⟨x - 3, by omega⟩
      subst hk
      have hrw : (1 : ℤ) + 2 ^ (k + 3) + 2 ^ (2 * (k + 3) + 1)
          = 1 + 8 * 2 ^ k + 128 * ((2 : ℤ) ^ k) ^ 2 := by ring
      rw [hrw] at h
      have hPpos : (0 : ℤ) < 2 ^ k := by positivity
      have hyne : y ≠ 0 := by
        intro h0
        rw [h0] at h
        nlinarith
      rcases lt_or_gt_of_ne hyne with hneg | hpos
      · obtain ⟨hk1, hy23⟩ := key k (-y) (by linarith) (by linear_combination h)
        exact ⟨by omega, Or.inr (by linarith)⟩
      · obtain ⟨hk1, hy23⟩ := key k y hpos h
        exact ⟨by omega, Or.inl hy23⟩
  · rintro (⟨rfl, (rfl | rfl)⟩ | ⟨rfl, (rfl | rfl)⟩) <;> norm_num

end Imo2006P4
