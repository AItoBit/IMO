import Mathlib

/-!
# IMO 1996, Problem 4

Positive integers `a`, `b` are such that `15a + 16b` and `16a - 15b` are both squares of positive
integers. Find the least possible value of the smaller of the two squares.

Answer: `481² = 231361`.

## Proof

Writing `15a + 16b = m²` and `16a - 15b = n²`, squaring and adding gives

  `m⁴ + n⁴ = (15a+16b)² + (16a-15b)² = 481(a² + b²)`,

so `481 = 13 · 37` divides `m⁴ + n⁴`. Modulo `13` and modulo `37` the only way a sum of two
fourth powers can vanish is for both to vanish (checked by `decide`), so `13` and `37` divide
both `m` and `n`, hence `481 ∣ m` and `481 ∣ n`. Both being positive, `m, n ≥ 481` and each
square is at least `481²`.

The value is attained at `a = 481·76 = 36556`, `b = 481·49 = 23569`, where
`15a + 16b = 962²` and `16a - 15b = 481²`.

To avoid truncated subtraction, `16a - 15b = n²` is written `16a = 15b + n²`.
-/

namespace Imo1996P4

theorem zmod13 (x y : ZMod 13) (h : x ^ 4 + y ^ 4 = 0) : x = 0 ∧ y = 0 := by
  revert x y
  decide

theorem zmod37 (x y : ZMod 37) (h : x ^ 4 + y ^ 4 = 0) : x = 0 ∧ y = 0 := by
  revert x y
  decide

theorem imo1996_p4 :
    IsLeast {k : ℕ | ∃ a b m n : ℕ, 0 < a ∧ 0 < b ∧ 0 < m ∧ 0 < n ∧
      15 * a + 16 * b = m ^ 2 ∧ 16 * a = 15 * b + n ^ 2 ∧ k = min (m ^ 2) (n ^ 2)}
      231361 := by
  constructor
  · -- `a = 481·76`, `b = 481·49`, `m = 962`, `n = 481`
    refine ⟨36556, 23569, 962, 481, by norm_num, by norm_num, by norm_num, by norm_num,
      by norm_num, by norm_num, by norm_num⟩
  · rintro k ⟨a, b, m, n, ha, hb, hm, hn, h1, h2, rfl⟩
    -- the key identity, over `ℤ`
    have h1' : (15 : ℤ) * a + 16 * b = (m : ℤ) ^ 2 := by exact_mod_cast h1
    have h2' : (16 : ℤ) * a = 15 * b + (n : ℤ) ^ 2 := by exact_mod_cast h2
    have key : (m : ℤ) ^ 4 + (n : ℤ) ^ 4 = 481 * ((a : ℤ) ^ 2 + (b : ℤ) ^ 2) := by
      linear_combination (-((m : ℤ) ^ 2 + 15 * a + 16 * b)) * h1'
        + (-((n : ℤ) ^ 2 + 16 * a - 15 * b)) * h2'
    -- divisibility by 13
    have h13 : (13 : ℕ) ∣ m ∧ (13 : ℕ) ∣ n := by
      have hz : ((m : ZMod 13)) ^ 4 + ((n : ZMod 13)) ^ 4 = 0 := by
        calc ((m : ZMod 13)) ^ 4 + ((n : ZMod 13)) ^ 4
            = ((((m : ℤ) ^ 4 + (n : ℤ) ^ 4 : ℤ)) : ZMod 13) := by push_cast; ring
          _ = (((481 * ((a : ℤ) ^ 2 + (b : ℤ) ^ 2) : ℤ)) : ZMod 13) := by rw [key]
          _ = 0 := by
              push_cast
              rw [show ((481 : ZMod 13)) = 0 by decide]
              ring
      obtain ⟨hx, hy⟩ := zmod13 _ _ hz
      exact ⟨(ZMod.natCast_eq_zero_iff m 13).1 hx,
        (ZMod.natCast_eq_zero_iff n 13).1 hy⟩
    -- divisibility by 37
    have h37 : (37 : ℕ) ∣ m ∧ (37 : ℕ) ∣ n := by
      have hz : ((m : ZMod 37)) ^ 4 + ((n : ZMod 37)) ^ 4 = 0 := by
        calc ((m : ZMod 37)) ^ 4 + ((n : ZMod 37)) ^ 4
            = ((((m : ℤ) ^ 4 + (n : ℤ) ^ 4 : ℤ)) : ZMod 37) := by push_cast; ring
          _ = (((481 * ((a : ℤ) ^ 2 + (b : ℤ) ^ 2) : ℤ)) : ZMod 37) := by rw [key]
          _ = 0 := by
              push_cast
              rw [show ((481 : ZMod 37)) = 0 by decide]
              ring
      obtain ⟨hx, hy⟩ := zmod37 _ _ hz
      exact ⟨(ZMod.natCast_eq_zero_iff m 37).1 hx,
        (ZMod.natCast_eq_zero_iff n 37).1 hy⟩
    -- hence `481 ∣ m` and `481 ∣ n`
    have hcop : Nat.Coprime 13 37 := by decide
    have hm481 : (481 : ℕ) ∣ m := by
      have h := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop h13.1 h37.1
      norm_num at h
      exact h
    have hn481 : (481 : ℕ) ∣ n := by
      have h := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop h13.2 h37.2
      norm_num at h
      exact h
    have hmge : 481 ≤ m := Nat.le_of_dvd hm hm481
    have hnge : 481 ≤ n := Nat.le_of_dvd hn hn481
    refine le_min ?_ ?_
    · calc (231361 : ℕ) = 481 ^ 2 := by norm_num
        _ ≤ m ^ 2 := Nat.pow_le_pow_left hmge 2
    · calc (231361 : ℕ) = 481 ^ 2 := by norm_num
        _ ≤ n ^ 2 := Nat.pow_le_pow_left hnge 2

end Imo1996P4
