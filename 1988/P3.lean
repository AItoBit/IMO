import Mathlib

/-!
# IMO 1988, Problem 3  

This formalizes the linear recurrence deductions from Solution 1 
in "p3 1988.pdf".

Given the functional equations:
  f(2n) = f(n)
  f(4n+1) = 2f(2n+1) - f(n)
  f(4n+3) = 3f(2n+1) - 2f(n)

We prove the derived difference equations:
  f(4n+1) - f(4n) = 2(f(2n+1) - f(2n))
  f(4n+3) - f(4n+2) = 2(f(2n+1) - f(2n))
-/

namespace IMO1988P3

theorem solution1_differences
    (f : ℤ → ℤ)
    (h_even : ∀ n, f (2 * n) = f n)
    (h_mod1 : ∀ n, f (4 * n + 1) = 2 * f (2 * n + 1) - f n)
    (h_mod3 : ∀ n, f (4 * n + 3) = 3 * f (2 * n + 1) - 2 * f n)
    (n : ℤ) :
    (f (4 * n + 1) - f (4 * n) = 2 * (f (2 * n + 1) - f (2 * n))) ∧
    (f (4 * n + 3) - f (4 * n + 2) = 2 * (f (2 * n + 1) - f (2 * n))) := by
  
  constructor
  · -- Part 1: f(4n+1) - f(4n)
    have eq_4n : 4 * n = 2 * (2 * n) := by ring
    have h1 : f (4 * n) = f (2 * n) := by
      rw [eq_4n]
      exact h_even (2 * n)
      
    calc f (4 * n + 1) - f (4 * n)
      _ = (2 * f (2 * n + 1) - f n) - f (2 * n) := by rw [h_mod1 n, h1]
      _ = (2 * f (2 * n + 1) - f (2 * n)) - f (2 * n) := by rw [← h_even n]
      _ = 2 * (f (2 * n + 1) - f (2 * n)) := by ring

  · -- Part 2: f(4n+3) - f(4n+2)
    have eq_4n2 : 4 * n + 2 = 2 * (2 * n + 1) := by ring
    have h2 : f (4 * n + 2) = f (2 * n + 1) := by
      rw [eq_4n2]
      exact h_even (2 * n + 1)
      
    calc f (4 * n + 3) - f (4 * n + 2)
      _ = (3 * f (2 * n + 1) - 2 * f n) - f (2 * n + 1) := by rw [h_mod3 n, h2]
      _ = (3 * f (2 * n + 1) - 2 * f (2 * n)) - f (2 * n + 1) := by rw [← h_even n]
      _ = 2 * (f (2 * n + 1) - f (2 * n)) := by ring

end IMO1988P3
