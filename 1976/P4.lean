import Mathlib

/-!
# IMO 1976 Problem 4

Determine the greatest number which is the product of some positive integers whose
sum is `1976`.

The answer is `2 * 3 ^ 658`.
-/

namespace Imo1976P4

/-- `x ^ 3 ≤ 3 ^ x` for every natural number `x`. -/
theorem cube_le_three_pow (x : ℕ) : x ^ 3 ≤ 3 ^ x := by
  induction x with
  | zero => decide
  | succ n ih =>
    rcases Nat.lt_or_ge n 3 with hn | hn
    · interval_cases n <;> decide
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
      calc (m + 3 + 1) ^ 3 ≤ 3 * (m + 3) ^ 3 := by
            ring_nf; nlinarith [sq_nonneg m, pow_nonneg (Nat.zero_le m) 3]
        _ ≤ 3 * 3 ^ (m + 3) := Nat.mul_le_mul_left 3 ih
        _ = 3 ^ (m + 3 + 1) := by ring

/-- The cube of the product of a list of naturals is at most `3` to the power of its sum. -/
theorem list_prod_cube_le (l : List ℕ) : l.prod ^ 3 ≤ 3 ^ l.sum := by
  induction l with
  | nil => decide
  | cons a t ih =>
    have h : (a * t.prod) ^ 3 = a ^ 3 * t.prod ^ 3 := by ring
    simp only [List.prod_cons, List.sum_cons, h, pow_add]
    exact Nat.mul_le_mul (cube_le_three_pow a) ih

/-- For `x ≥ 4` the sharper bound `9 * x ^ 3 ≤ 8 * 3 ^ x` holds. -/
theorem nine_mul_cube_le_of_four_le (x : ℕ) (hx : 4 ≤ x) : 9 * x ^ 3 ≤ 8 * 3 ^ x := by
  induction x, hx using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    calc 9 * (n + 1) ^ 3 ≤ 3 * (9 * n ^ 3) := by
          obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
          ring_nf; nlinarith [sq_nonneg m, pow_nonneg (Nat.zero_le m) 3]
      _ ≤ 3 * (8 * 3 ^ n) := Nat.mul_le_mul_left 3 ih
      _ = 8 * 3 ^ (n + 1) := by ring

/-- For `x ≠ 3`, the sharper bound `9 * x ^ 3 ≤ 8 * 3 ^ x` holds. -/
theorem nine_mul_cube_le (x : ℕ) (hx : x ≠ 3) : 9 * x ^ 3 ≤ 8 * 3 ^ x := by
  rcases Nat.lt_or_ge x 4 with hlt | hge
  · interval_cases x
    · decide
    · decide
    · decide
    · exact absurd rfl hx
  · exact nine_mul_cube_le_of_four_le x hge

/-- A list all of whose entries equal `3` has sum `3 * length`. -/
theorem sum_eq_of_all_three (l : List ℕ) (h : ∀ x ∈ l, x = 3) : l.sum = 3 * l.length := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ha : a = 3 := h a (by simp)
    have ht : ∀ x ∈ t, x = 3 := fun x hx => h x (by simp [hx])
    have := ih ht
    simp only [List.sum_cons, List.length_cons, ha, this]
    ring

/-- Any list of positive integers summing to `1976` has product at most `2 * 3 ^ 658`. -/
theorem prod_le (l : List ℕ) (hsum : l.sum = 1976) : l.prod ≤ 2 * 3 ^ 658 := by
  -- Some element is different from `3`, since `3 ∤ 1976`.
  have hex : ∃ x ∈ l, x ≠ 3 := by
    by_contra h
    push_neg at h
    have := sum_eq_of_all_three l h
    omega
  obtain ⟨x, hxl, hx3⟩ := hex
  obtain ⟨s, t, rfl⟩ := List.append_of_mem hxl
  have hsum' : s.sum + t.sum + x = 1976 := by
    simp only [List.sum_append, List.sum_cons] at hsum
    omega
  have hprod : (s ++ x :: t).prod ^ 3 = x ^ 3 * ((s ++ t).prod) ^ 3 := by
    simp only [List.prod_append, List.prod_cons]
    ring
  have hst : (s ++ t).prod ^ 3 ≤ 3 ^ (s.sum + t.sum) := by
    have := list_prod_cube_le (s ++ t)
    simpa [List.sum_append] using this
  have key : 9 * (s ++ x :: t).prod ^ 3 ≤ 8 * 3 ^ 1976 := by
    calc 9 * (s ++ x :: t).prod ^ 3 = (9 * x ^ 3) * ((s ++ t).prod) ^ 3 := by
          rw [hprod]; ring
      _ ≤ (8 * 3 ^ x) * 3 ^ (s.sum + t.sum) := Nat.mul_le_mul (nine_mul_cube_le x hx3) hst
      _ = 8 * 3 ^ (s.sum + t.sum + x) := by rw [pow_add]; ring
      _ = 8 * 3 ^ 1976 := by rw [hsum']
  have hcube : (s ++ x :: t).prod ^ 3 ≤ (2 * 3 ^ 658) ^ 3 := by
    have h9 : 9 * ((2 * 3 ^ 658 : ℕ) ^ 3) = 8 * 3 ^ 1976 := by
      have h1 : (2 * 3 ^ 658 : ℕ) ^ 3 = 8 * 3 ^ 1974 := by ring
      rw [h1, show (1976 : ℕ) = 2 + 1974 from by norm_num, pow_add]
      ring
    rw [← h9] at key
    exact Nat.le_of_mul_le_mul_left key (by norm_num)
  exact (Nat.pow_le_pow_iff_left (by norm_num)).mp hcube

/-- The greatest product of positive integers with sum `1976` is `2 * 3 ^ 658`. -/
theorem imo1976_p4 :
    IsGreatest {p : ℕ | ∃ l : List ℕ, (∀ x ∈ l, 0 < x) ∧ l.sum = 1976 ∧ l.prod = p}
      (2 * 3 ^ 658) := by
  constructor
  · refine ⟨2 :: List.replicate 658 3, ?_, ?_, ?_⟩
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · norm_num
      · rw [List.eq_of_mem_replicate hy]; norm_num
    · rw [List.sum_cons, List.sum_replicate, smul_eq_mul]
    · rw [List.prod_cons, List.prod_replicate]
  · rintro p ⟨l, _, hsum, rfl⟩
    exact prod_le l hsum

end Imo1976P4
