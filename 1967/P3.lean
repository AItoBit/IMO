import Mathlib

open Finset

/-- The sequence defined in the problem: c_s = s * (s + 1) -/
def c (s : ℤ) : ℤ := s * (s + 1)

/-- The algebraic identity for the difference of two terms in the sequence. 
    (Matches the step: c_m - c_n = m(m+1) - n(n+1) = ... = (m-n)(m+n+1)) -/
lemma c_diff (x y : ℤ) : c x - c y = (x - y) * (x + y + 1) := by
  unfold c
  ring

/-- The numerator product splitting into two products. -/
lemma imo1967_p3_numerator (m k : ℤ) (n : ℕ) :
    (∏ i ∈ range n, (c (m + (i : ℤ) + 1) - c k)) =
    (∏ i ∈ range n, (m + (i : ℤ) + 1 - k)) * (∏ i ∈ range n, (m + (i : ℤ) + 1 + k + 1)) := by
  have h : ∀ i ∈ range n, c (m + (i : ℤ) + 1) - c k = (m + (i : ℤ) + 1 - k) * (m + (i : ℤ) + 1 + k + 1) := by
    intro i _
    exact c_diff (m + (i : ℤ) + 1) k
  rw [prod_congr rfl h, prod_mul_distrib]

/-- The denominator product simplifies exactly to a product of two factorials. 
    (Matches the step: product of c_a = a(a+1) equals n!(n+1)!) -/
lemma imo1967_p3_denominator (n : ℕ) :
    (∏ i ∈ range n, c ((i : ℤ) + 1)) = (n.factorial : ℤ) * ((n + 1).factorial : ℤ) := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [prod_range_succ, ih]
    unfold c
    -- Factor out the inductive steps leveraging definitional equalities of factorials
    have h1 : ((n + 1).factorial : ℤ) = (n + 1 : ℤ) * (n.factorial : ℤ) := by
      calc ((n + 1).factorial : ℤ)
        _ = (((n + 1) * n.factorial : ℕ) : ℤ) := rfl
        _ = (n + 1 : ℤ) * (n.factorial : ℤ) := by push_cast; rfl
    have h2 : ((n + 2).factorial : ℤ) = (n + 2 : ℤ) * ((n + 1).factorial : ℤ) := by
      calc ((n + 2).factorial : ℤ)
        _ = (((n + 2) * (n + 1).factorial : ℕ) : ℤ) := rfl
        _ = (n + 2 : ℤ) * ((n + 1).factorial : ℤ) := by push_cast; rfl
    
    calc
      (n.factorial : ℤ) * (n + 1).factorial * ((n + 1 : ℤ) * (n + 1 + 1))
        = ((n + 1 : ℤ) * (n.factorial : ℤ)) * ((n + 2 : ℤ) * ((n + 1).factorial : ℤ)) := by ring
      _ = ((n + 1).factorial : ℤ) * ((n + 2).factorial : ℤ) := by
        rw [← h1, ← h2]

/-- The core algebraic reduction of the divisibility problem shown in the solution. 
    This states that solving the problem is precisely equivalent to showing divisibility 
    between our newly simplified numerator and denominator forms. -/
theorem imo1967_p3_divisibility_algebraic_reduction (m k : ℤ) (n : ℕ) :
    (∏ i ∈ range n, c ((i : ℤ) + 1)) ∣ (∏ i ∈ range n, (c (m + (i : ℤ) + 1) - c k)) ↔
    ((n.factorial : ℤ) * ((n + 1).factorial : ℤ)) ∣
    ((∏ i ∈ range n, (m + (i : ℤ) + 1 - k)) * (∏ i ∈ range n, (m + (i : ℤ) + 1 + k + 1))) := by
  rw [imo1967_p3_numerator, imo1967_p3_denominator]
