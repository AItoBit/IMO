import Mathlib

open Real

/--
Auxiliary lemma solving the linear recurrence from the solution:
`m_{k+1} = (6/7) * m_k - (6/7) * (k+1)`
-/
lemma m_explicit (m_seq : ℕ → ℝ) (m0 : ℝ)
    (h0 : m_seq 0 = m0)
    (h_rec : ∀ k, m_seq (k + 1) = (6 / 7) * m_seq k - (6 / 7) * (k + 1 : ℝ))
    (k : ℕ) :
    m_seq k = (m0 - 36) * (6 / 7) ^ k - 6 * (k : ℝ) + 36 := by
  induction k with
  | zero =>
    simp [h0]
  | succ k ih =>
    rw [h_rec k, ih]
    push_cast
    rw [pow_succ]
    ring

/--
Formalization of the algebraic derivation in the solution for the IMO problem.
It demonstrates that the simplified recurrence relation ending with `m_{n-1} = n` 
yields the explicit algebraic identity for `m - 36`.
-/
theorem imo1967_p6_solution_identity
    (m_seq : ℕ → ℝ) (m : ℝ) (n : ℕ) (hn : 0 < n)
    (h0 : m_seq 0 = m)
    (h_rec : ∀ k, m_seq (k + 1) = (6 / 7) * m_seq k - (6 / 7) * (k + 1 : ℝ))
    (h_end : m_seq (n - 1) = (n : ℝ)) :
    m - 36 = 7 * ((n : ℝ) - 6) * (7 / 6) ^ (n - 1) := by
  -- Retrieve the explicit formula evaluated at k = n - 1
  have h_expl := m_explicit m_seq m h0 h_rec (n - 1)
  rw [h_end] at h_expl

  -- Robust casting for (n - 1 : ℝ) given that 0 < n
  have hn_cast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    have h_eq : n - 1 + 1 = n := Nat.sub_add_cancel hn
    have h_cast : ((n - 1 + 1 : ℕ) : ℝ) = (n : ℝ) := by rw [h_eq]
    push_cast at h_cast
    linarith

  rw [hn_cast] at h_expl

  -- Isolate the term containing (m - 36)
  have h2 : 7 * ((n : ℝ) - 6) = (m - 36) * (6 / 7) ^ (n - 1) := by
    calc 7 * ((n : ℝ) - 6) = (n : ℝ) + 6 * ((n : ℝ) - 1) - 36 := by ring
    _ = (m - 36) * (6 / 7) ^ (n - 1) := by linarith [h_expl]

  -- Show that multiplying the reciprocal powers cancels out to 1
  have h4 : (6 / 7 : ℝ) ^ (n - 1) * (7 / 6) ^ (n - 1) = 1 := by
    rw [← mul_pow]
    have h_mul : (6 / 7 : ℝ) * (7 / 6) = 1 := by norm_num
    rw [h_mul, one_pow]

  -- Final rearrangement to reach the target identity
  calc m - 36 = (m - 36) * 1 := by ring
    _ = (m - 36) * ((6 / 7) ^ (n - 1) * (7 / 6) ^ (n - 1)) := by rw [h4]
    _ = (m - 36) * (6 / 7) ^ (n - 1) * (7 / 6) ^ (n - 1) := by ring
    _ = 7 * ((n : ℝ) - 6) * (7 / 6) ^ (n - 1) := by rw [← h2]
