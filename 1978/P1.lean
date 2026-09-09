/-
# IMO 1978, Problem 1

Let `m, n` be positive integers with `1 ≤ m < n` such that `1978^m` and `1978^n`
have the same last three decimal digits.  Find `m, n` making `m + n` least.

The answer is `m = 3`, `n = 103`, so `m + n = 106`.

## Modelling

"Same last three digits" is `1978^m % 1000 = 1978^n % 1000`, and "find `m, n`
minimising `m + n`" is `IsLeast` for the set of attainable values of `m + n`.

## Proof

Write `n = m + d` with `d ≥ 1`.

* **`m ≥ 3`** (the `2`-part).  `4 ∣ 1978^k` for `k ≥ 2` and `8 ∣ 1978^k` for
  `k ≥ 3`.  If `m = 1` then `1978^m ≡ 2 (mod 8)` while `4 ∣ 1978^n`, so
  `1978^n mod 8 ∈ {0,4}`; if `m = 2` then `1978^m ≡ 4 (mod 8)` while
  `8 ∣ 1978^n`.  Both are impossible.
* **`d ≥ 100`** (the `5`-part).  From `125 ∣ 1000`, `1978^m ≡ 1978^m · 1978^d
  (mod 125)`, and `1978` is invertible mod `125`, so `1978^d ≡ 1 (mod 125)`.
  The multiplicative order of `1978` mod `125` is `100` (`φ(125) = 100`, and
  `1978^s ≢ 1` for `0 < s < 100`), hence `100 ∣ d`.

Therefore `m + n = 2m + d ≥ 6 + 100 = 106`, attained at `(3, 103)`.

The order computation — the step the AoPS write-up does "by hand" — is the one
finite check here, done by `decide` over `s < 100`.
-/

import Mathlib

set_option maxRecDepth 10000

namespace Imo1978P1

/-- `1978` has multiplicative order exactly `100` modulo `125`. -/
private lemma order_125 {d : ℕ} (h : 1978 ^ d ≡ 1 [MOD 125]) : 100 ∣ d := by
  have h100 : 1978 ^ 100 ≡ 1 [MOD 125] := by decide
  have hzero : ∀ s ∈ Finset.range 100, 1978 ^ s ≡ 1 [MOD 125] → s = 0 := by decide
  have hd : d = 100 * (d / 100) + d % 100 := (Nat.div_add_mod d 100).symm
  have hstep : 1978 ^ (d % 100) ≡ 1 [MOD 125] := by
    have e : 1978 ^ d = (1978 ^ 100) ^ (d / 100) * 1978 ^ (d % 100) := by
      rw [← pow_mul, ← pow_add, ← hd]
    rw [e] at h
    have h1 : (1978 ^ 100) ^ (d / 100) ≡ 1 [MOD 125] := by
      simpa using h100.pow (d / 100)
    calc 1978 ^ (d % 100) ≡ 1 * 1978 ^ (d % 100) [MOD 125] := by rw [one_mul]
      _ ≡ (1978 ^ 100) ^ (d / 100) * 1978 ^ (d % 100) [MOD 125] := (h1.mul_right _).symm
      _ ≡ 1 [MOD 125] := h
  have hlt : d % 100 < 100 := Nat.mod_lt d (by norm_num)
  have := hzero (d % 100) (Finset.mem_range.mpr hlt) hstep
  omega

private lemma dvd4 : ∀ k, 2 ≤ k → 4 ∣ 1978 ^ k := by
  intro k hk
  obtain ⟨j, rfl⟩ : ∃ j, k = 2 + j := ⟨k - 2, by omega⟩
  rw [pow_add]
  exact Dvd.dvd.mul_right (by norm_num) _

private lemma dvd8 : ∀ k, 3 ≤ k → 8 ∣ 1978 ^ k := by
  intro k hk
  obtain ⟨j, rfl⟩ : ∃ j, k = 3 + j := ⟨k - 3, by omega⟩
  rw [pow_add]
  exact Dvd.dvd.mul_right (by norm_num) _

/-- **IMO 1978, Problem 1.** -/
theorem imo1978_p1 :
    IsLeast {s : ℕ | ∃ m n : ℕ, 1 ≤ m ∧ m < n ∧
      1978 ^ m % 1000 = 1978 ^ n % 1000 ∧ s = m + n} 106 := by
  constructor
  · -- `(m, n) = (3, 103)`
    exact ⟨3, 103, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · rintro s ⟨m, n, hm, hmn, heq, rfl⟩
    obtain ⟨d, hd1, rfl⟩ : ∃ d, 1 ≤ d ∧ n = m + d := ⟨n - m, by omega, by omega⟩
    have hmod : 1978 ^ m ≡ 1978 ^ (m + d) [MOD 1000] := heq
    -- the `2`-part: `m ≥ 3`
    have hm3 : 3 ≤ m := by
      by_contra hcon
      have hm2 : m ≤ 2 := by omega
      have h8eq : 1978 ^ m ≡ 1978 ^ (m + d) [MOD 8] :=
        Nat.ModEq.of_dvd (by norm_num) hmod
      interval_cases m
      · have h4 : 4 ∣ 1978 ^ (1 + d) := dvd4 _ (by omega)
        have e1 : 1978 ^ 1 % 8 = 2 := by norm_num
        have h8eq' : 1978 ^ 1 % 8 = 1978 ^ (1 + d) % 8 := h8eq
        omega
      · have h8 : 8 ∣ 1978 ^ (2 + d) := dvd8 _ (by omega)
        have e2 : 1978 ^ 2 % 8 = 4 := by norm_num
        have h8eq' : 1978 ^ 2 % 8 = 1978 ^ (2 + d) % 8 := h8eq
        omega
    -- the `5`-part: `d ≥ 100`
    have h125 : 1978 ^ m ≡ 1978 ^ (m + d) [MOD 125] :=
      Nat.ModEq.of_dvd (by norm_num) hmod
    rw [pow_add] at h125
    have hcop : Nat.gcd 125 (1978 ^ m) = 1 :=
      Nat.Coprime.pow_right m (by norm_num)
    have hcancel : (1 : ℕ) ≡ 1978 ^ d [MOD 125] := by
      refine Nat.ModEq.cancel_left_of_coprime hcop ?_
      simpa using h125
    have hdvd : 100 ∣ d := order_125 hcancel.symm
    have hd100 : 100 ≤ d := Nat.le_of_dvd (by omega) hdvd
    omega

end Imo1978P1
