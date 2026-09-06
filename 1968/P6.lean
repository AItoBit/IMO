import Mathlib

open Finset
open scoped BigOperators

/--
Formalization of IMO 1968 Problem 6.
Evaluates the infinite sum of floor((n + 2^k) / 2^{k+1}) to n.
Since terms where 2^{k+1} > n + 2^k are zero, the sum is formulated 
as a finite sum up to N where 2^N > n, directly yielding the final atomic conclusion.
-/
theorem imo1968_p6_sum (n N : ℕ) (h : n < 2 ^ N) :
    ∑ k ∈ range N, (n + 2 ^ k) / 2 ^ (k + 1) = n := by
  revert n
  induction N with
  | zero =>
    intro n h
    have h_zero : n = 0 := by omega
    subst h_zero
    simp
  | succ N ih =>
    intro n h
    rw [sum_range_succ']
    have h_shift : ∑ j ∈ range N, (n + 2 ^ (j + 1)) / 2 ^ (j + 1 + 1) = ∑ j ∈ range N, (n / 2 + 2 ^ j) / 2 ^ (j + 1) := by
      apply sum_congr rfl
      intro j _
      have h1 : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [pow_succ, mul_comm]
      have h2 : 2 ^ (j + 1 + 1) = 2 * 2 ^ (j + 1) := by rw [pow_succ, mul_comm]
      rw [h1, h2, ← Nat.div_div_eq_div_mul]
      congr 1
      generalize 2 ^ j = A
      omega
    rw [h_shift]
    
    have hn2 : n / 2 < 2 ^ N := by
      have h_pow : 2 ^ (N + 1) = 2 * 2 ^ N := by rw [pow_succ, mul_comm]
      rw [h_pow] at h
      generalize 2 ^ N = B at h ⊢
      omega
      
    rw [ih (n / 2) hn2]
    
    have h_base : (n + 2 ^ 0) / 2 ^ (0 + 1) = (n + 1) / 2 := rfl
    rw [h_base]
    omega
