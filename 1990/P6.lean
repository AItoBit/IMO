import Mathlib

open Finset

/-- 
Solution 2 of IMO 1990 Problem 6 reduces the geometric condition 
to proving that \sum_{n=0}^{994} c_n \omega^n = 0 for a primitive 995-th 
root of unity \omega, where c_n is a permutation of {3, 7, ..., 3979}.

This theorem formalizes and fully proves the core algebraic identity 
for the explicit permutation constructed in the solution.
-/
theorem imo1990_p6_algebraic_core {R : Type*} [CommRing R] (x : R)
    (h199 : ∑ j ∈ range 199, x^(5 * j) = 0)
    (h5 : ∑ k ∈ range 5, x^(199 * k) = 0) :
    ∑ j ∈ range 199, ∑ k ∈ range 5,
      ((4 * (199 * k + j) + 3 : ℕ) : R) * x^(5 * j + 199 * k) = 0 := by
  
  -- Step 1: Rewrite the inner sum terms to decouple j and k
  have h_term : ∀ j k, ((4 * (199 * k + j) + 3 : ℕ) : R) * x^(5 * j + 199 * k) =
      (((4 * 199 * k + 3 : ℕ) : R) * x^(199 * k)) * x^(5 * j) +
      (((4 * j : ℕ) : R) * x^(5 * j)) * x^(199 * k) := by
    intro j k
    rw [pow_add]
    push_cast
    ring
  
  -- Distribute the sum over the addition
  simp_rw [h_term, sum_add_distrib]
  
  -- Step 2: Evaluate the first half of the sum using h199
  have h1 : (∑ j ∈ range 199, ∑ k ∈ range 5, (((4 * 199 * k + 3 : ℕ) : R) * x^(199 * k)) * x^(5 * j)) = 0 := by
    simp_rw [← sum_mul]
    rw [← mul_sum, h199, mul_zero]

  -- Step 3: Evaluate the second half of the sum using h5
  have h2 : (∑ j ∈ range 199, ∑ k ∈ range 5, (((4 * j : ℕ) : R) * x^(5 * j)) * x^(199 * k)) = 0 := by
    simp_rw [← mul_sum, h5, mul_zero]
    simp
    
  -- Conclude the proof
  rw [h1, h2, add_zero]
