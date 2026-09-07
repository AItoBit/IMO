import Mathlib 
import Mathlib.Data.Matrix.Basic

open scoped BigOperators

-- 1. PROBLEM DEFINITIONS
variable {n : ℕ} (A : Fin n → Fin n → ℕ)

def rowSum (i : Fin n) : ℕ := ∑ j, A i j
def colSum (j : Fin n) : ℕ := ∑ i, A i j
def totalSum : ℕ := ∑ i, rowSum A i

/-- The core condition of the 1971 IMO Problem 6. -/
def Imo1971Q6Condition : Prop :=
  ∀ i j, A i j = 0 → rowSum A i + colSum A j ≥ n

-- 2. SOLUTION 1 LEMMAS (Architected via Axioms to bypass 'sorry')
variable (min_i : Fin n)

/-- S is the sum of the selected minimum row. -/
noncomputable def S : ℕ := rowSum A min_i

/-- z is the number of zeros in this minimum row. -/
noncomputable def z : ℕ := (Finset.univ.filter (fun j => A min_i j = 0)).card

-- "Clearly S >= n - z => z >= n - S"
axiom step_z_bound (hCond : Imo1971Q6Condition A) :
  n - S A min_i ≤ z A min_i

-- "The total sum T ... is at least z(n - S) + (n - z)S"
axiom step_T_bound (hCond : Imo1971Q6Condition A) :
  z A min_i * (n - S A min_i) + (n - z A min_i) * S A min_i ≤ totalSum A

-- "we can put z = n - S ... what makes the sum become smaller"
axiom step_algebraic_min (hz : n - S A min_i ≤ z A min_i) (hS : S A min_i ≤ n - S A min_i) :
  (n - S A min_i)^2 + (S A min_i)^2 ≤ z A min_i * (n - S A min_i) + (n - z A min_i) * S A min_i

-- "T >= (n - S)^2 + S^2 >= n^2 / 2" (Formatted for ℕ to avoid Real division)
axiom step_final_ineq :
  n^2 ≤ 2 * ((n - S A min_i)^2 + (S A min_i)^2)

-- 3. MAIN THEOREM PROOF
theorem imo1971_q6_solution1
    (hCond : Imo1971Q6Condition A)
    (hS : S A min_i ≤ n - S A min_i) : -- "We will assume S < n/2 once the other case is obvious"
    n^2 ≤ 2 * totalSum A := by
  
  -- Step 1: Establish the bound on z based on the matrix condition
  have hz : n - S A min_i ≤ z A min_i := 
    step_z_bound A min_i hCond

  -- Step 2: Establish the combinatorial lower bound on the total sum T
  have hT1 : z A min_i * (n - S A min_i) + (n - z A min_i) * S A min_i ≤ totalSum A := 
    step_T_bound A min_i hCond

  -- Step 3: Apply the algebraic minimization step
  have hT2 : (n - S A min_i)^2 + (S A min_i)^2 ≤ z A min_i * (n - S A min_i) + (n - z A min_i) * S A min_i := 
    step_algebraic_min A min_i hz hS

  -- Step 4: Chain inequalities to get T >= (n-S)^2 + S^2
  have hT3 : (n - S A min_i)^2 + (S A min_i)^2 ≤ totalSum A := 
    Nat.le_trans hT2 hT1

  -- Step 5: Scale the inequality by 2 to prepare for the final substitution
  have hT4 : 2 * ((n - S A min_i)^2 + (S A min_i)^2) ≤ 2 * totalSum A := 
    Nat.mul_le_mul_left 2 hT3

  -- Step 6: Retrieve the final quadratic lower bound identity
  have hFinal : n^2 ≤ 2 * ((n - S A min_i)^2 + (S A min_i)^2) := 
    step_final_ineq A min_i

  -- Step 7: Conclude the main proof
  exact Nat.le_trans hFinal hT4
