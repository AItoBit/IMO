import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace IMO1975P4

/-- The sum of the decimal digits of a natural number. -/
def digitSum (n : ℕ) : ℕ := (Nat.digits 10 n).sum

/-- If `n < 10 ^ k` then the digit sum of `n` is at most `9 * k`. -/
lemma digitSum_le_of_lt_pow {n k : ℕ} (h : n < 10 ^ k) : digitSum n ≤ 9 * k := by
  have hlen : (Nat.digits 10 n).length ≤ k :=
    (Nat.digits_length_le_iff (by norm_num) n).mpr h
  have hbound : (Nat.digits 10 n).sum ≤ (Nat.digits 10 n).length • 9 :=
    List.sum_le_card_nsmul _ 9 (fun x hx => Nat.le_of_lt_succ (Nat.digits_lt_base (by norm_num) hx))
  calc digitSum n ≤ (Nat.digits 10 n).length • 9 := hbound
    _ = 9 * (Nat.digits 10 n).length := by simp [smul_eq_mul, Nat.mul_comm]
    _ ≤ 9 * k := Nat.mul_le_mul_left 9 hlen

/-- The digit sum is congruent to the number itself modulo `9`. -/
lemma digitSum_mod_nine (n : ℕ) : digitSum n % 9 = n % 9 :=
  (Nat.modEq_digits_sum 9 10 (by norm_num) n).symm

/-- `4444 ^ 4444 < 10 ^ 17776`. -/
lemma pow_lt : 4444 ^ 4444 < 10 ^ 17776 := by
  calc (4444 : ℕ) ^ 4444 < (10 ^ 4) ^ 4444 := by
        exact Nat.pow_lt_pow_left (by norm_num) (by norm_num)
    _ = 10 ^ 17776 := by rw [← pow_mul]

/-- `4444 ^ 4444 ≡ 7 [MOD 9]`. -/
lemma pow_mod_nine : 4444 ^ 4444 % 9 = 7 := by
  have h : (4444 : ℕ) ^ 4444 = ((4444 ^ 3) ^ 1481) * 4444 := by
    rw [← pow_mul, ← pow_succ]
  rw [h, Nat.mul_mod, Nat.pow_mod]
  norm_num

/-- Every `b ≤ 54` with `b ≡ 7 [MOD 9]` has digit sum `7`. -/
lemma digitSum_eq_seven_of_le_54 (b : ℕ) (hb : b ≤ 54) (hmod : b % 9 = 7) : digitSum b = 7 := by
  interval_cases b <;> simp_all [digitSum]

/-- **IMO 1975, Problem 4.**  Let `A` be the sum of the decimal digits of `4444 ^ 4444`,
and `B` the sum of the digits of `A`.  Then the sum of the digits of `B` equals `7`. -/
theorem digitSum_digitSum_digitSum_pow :
    digitSum (digitSum (digitSum (4444 ^ 4444))) = 7 := by
  set A : ℕ := digitSum (4444 ^ 4444) with hA
  set B : ℕ := digitSum A with hB
  -- `A ≤ 9 * 17776 = 159984 < 10 ^ 6`
  have hA6 : A < 10 ^ 6 := lt_of_le_of_lt (digitSum_le_of_lt_pow pow_lt) (by norm_num)
  -- hence `B ≤ 54`
  have hB54 : B ≤ 54 := by
    have := digitSum_le_of_lt_pow (n := A) (k := 6) hA6
    omega
  -- and `B ≡ 4444 ^ 4444 ≡ 7 [MOD 9]`
  have hBmod : B % 9 = 7 := by
    rw [hB, digitSum_mod_nine, hA, digitSum_mod_nine, pow_mod_nine]
  exact digitSum_eq_seven_of_le_54 B hB54 hBmod

end IMO1975P4
