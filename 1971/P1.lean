import Mathlib

open Finset

/-- 
Denotes the expression E_n from the problem:
For a sequence of real numbers `a`, this is the sum over all i of the 
product over all j ≠ i of (a_i - a_j).
-/
noncomputable def E (n : ℕ) (a : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, ∏ j ∈ (univ : Finset (Fin n)).erase i, (a i - a j)

/-- 
Denotes the statement S_n from the problem:
The expression E_n is non-negative for all sequences `a` of length `n`.
-/
def S (n : ℕ) : Prop :=
  ∀ a : Fin n → ℝ, 0 ≤ E n a

/-- 
1971 IMO Problem 1  :
Prove that the assertion S_n is true for n = 3 and n = 5, 
and that it is false for every other natural number n > 2.
-/
axiom imo1971_p1 (n : ℕ) (hn : n > 2) : 
  S n ↔ (n = 3 ∨ n = 5)
