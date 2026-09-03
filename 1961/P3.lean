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

/-!
# IMO 1961 Problem 3

Solve the equation `cos^n x - sin^n x = 1`, where `n` is a positive integer.

The answer: if `n` is even the solution set is `{m * π | m : ℤ}`, and if `n` is odd it is
`{2 * m * π | m : ℤ} ∪ {2 * m * π - π / 2 | m : ℤ}`.
-/

open Real

/-- Pointwise characterization of the solutions of `cos^n x - sin^n x = 1`. -/
theorem Imo1961Q3 {n : ℕ} {x : ℝ} (h₀ : n ≠ 0) :
    (cos x) ^ n - (sin x) ^ n = 1 ↔
      (∃ k : ℤ, k * π = x) ∧ Even n ∨ (∃ k : ℤ, k * (2 * π) = x) ∧ Odd n ∨
        (∃ k : ℤ, -(π / 2) + k * (2 * π) = x) ∧ Odd n := by
  constructor
  · intro h
    rcases eq_or_ne (sin x) 0 with hsinx | hsinx
    · rw [hsinx, zero_pow h₀, sub_zero, pow_eq_one_iff_of_ne_zero h₀, cos_eq_one_iff,
        cos_eq_neg_one_iff] at h
      rcases h with ⟨k, rfl⟩ | ⟨⟨k, rfl⟩, hn⟩
      · cases n.even_or_odd with
        | inl hn => refine .inl ⟨⟨k * 2, ?_⟩, hn⟩; simp [mul_assoc]
        | inr hn => exact .inr <| .inl ⟨⟨_, rfl⟩, hn⟩
      · exact .inl ⟨⟨2 * k + 1, by push_cast; ring⟩, hn⟩
    · rcases eq_or_ne (cos x) 0 with hcosx | hcosx
      · right; right
        rw [hcosx, zero_pow h₀, zero_sub, ← neg_inj, neg_neg, pow_eq_neg_one_iff,
          sin_eq_neg_one_iff] at h
        simpa only [eq_comm] using h
      · have hcos1 : |cos x| < 1 := by
          rw [abs_cos_eq_sqrt_one_sub_sin_sq, sqrt_lt' one_pos]
          simp [sq_pos_of_ne_zero hsinx]
        have hsin1 : |sin x| < 1 := by
          rw [abs_sin_eq_sqrt_one_sub_cos_sq, sqrt_lt' one_pos]
          simp [sq_pos_of_ne_zero hcosx]
        match n with
        | 1 =>
          rw [pow_one, pow_one, sub_eq_iff_eq_add] at h
          have : 2 * sin x * cos x = 0 := by
            simpa [h, add_sq, add_assoc, ← two_mul, mul_add, mul_assoc, ← sq]
              using cos_sq_add_sin_sq x
          simp [hsinx, hcosx] at this
        | 2 =>
          rw [← cos_sq_add_sin_sq x, sub_eq_add_neg, add_right_inj, neg_eq_self] at h
          exact absurd (eq_zero_of_pow_eq_zero h) hsinx
        | (n + 1 + 2) =>
          set m := n + 1
          refine absurd ?_ h.not_lt
          calc
            (cos x) ^ (m + 2) - (sin x) ^ (m + 2) ≤ |cos x| ^ (m + 2) + |sin x| ^ (m + 2) := by
              simp only [← abs_pow, sub_eq_add_neg]
              gcongr
              exacts [le_abs_self _, neg_le_abs _]
            _ = |cos x| ^ m * cos x ^ 2 + |sin x| ^ m * sin x ^ 2 := by simp [pow_add]
            _ < 1 ^ m * cos x ^ 2 + 1 ^ m * sin x ^ 2 := by gcongr
            _ = 1 := by simp
  · rintro (⟨⟨k, rfl⟩, hn⟩ | ⟨⟨k, rfl⟩, -⟩ | ⟨⟨k, rfl⟩, hn⟩)
    · rw [sin_int_mul_pi, zero_pow h₀, sub_zero, ← hn.pow_abs, abs_cos_int_mul_pi, one_pow]
    · have : sin (k * (2 * π)) = 0 := by simpa [mul_assoc] using sin_int_mul_pi (k * 2)
      simp [h₀, this]
    · simp [hn.neg_pow, h₀]

/-- **IMO 1961 Problem 3.** The solution set of `cos^n x - sin^n x = 1` for `n > 0`:
if `n` is even it is `{m * π | m : ℤ}`, and if `n` is odd it consists of the reals of the
form `2 * m * π` or `2 * m * π - π / 2` with `m : ℤ`. -/
theorem imo_1961_p3 (n : ℕ) (h₀ : n > 0) :
    {x : ℝ | Real.cos x ^ n - Real.sin x ^ n = 1} =
    (if Even n then {(m : ℝ) * π | m : ℤ} else
      {a : ℝ | ∃ m : ℤ, a = 2 * m * π ∨ a = 2 * m * π - π / 2}) := by
  have hn0 : n ≠ 0 := h₀.ne'
  ext x
  simp only [Set.mem_ofPred_eq]
  rw [Imo1961Q3 hn0]
  split_ifs with hev
  · have hodd : ¬ Odd n := by simpa [Nat.not_odd_iff_even] using hev
    simp only [Set.mem_ofPred_eq, hev, hodd, and_true, and_false, or_false]
  · have hodd : Odd n := Nat.not_even_iff_odd.1 hev
    simp only [Set.mem_ofPred_eq, hev, hodd, and_true, and_false, false_or]
    constructor
    · rintro (⟨k, rfl⟩ | ⟨k, rfl⟩)
      · exact ⟨k, Or.inl (by ring)⟩
      · exact ⟨k, Or.inr (by ring)⟩
    · rintro ⟨k, rfl | rfl⟩
      · exact Or.inl ⟨k, by ring⟩
      · exact Or.inr ⟨k, by ring⟩
