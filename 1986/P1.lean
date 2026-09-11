import Mathlib

/-!
# IMO 1986 Problem 1 (Algebraic Core of Solution 2)


Assuming that 2d - 1, 5d - 1, and 13d - 1 are all perfect squares,
we define their square roots as p, q, and r respectively.
Since p^2 = 2d - 1, p must be odd, so we write p = 2k - 1.
This implies d is odd.
Since d is odd, 5d - 1 and 13d - 1 are even, meaning q and r are even.
We write q = 2n and r = 2m.
Substituting these into r^2 - q^2 = 8d yields (m - n)(m + n) = 2d.
Because (m - n) + (m + n) = 2m, the two factors share the same parity.
This leads to a contradiction whether they are both even or both odd,
since 2d is congruent to 2 modulo 4, while the product of two numbers
of the same parity is congruent to 0 or 1 modulo 4.
-/

namespace IMO1986P1

theorem solution2_contradiction (d p q r k m n : ℤ)
    (hp1 : p^2 = 2 * d - 1)
    (hp2 : p = 2 * k - 1)
    (hq1 : q^2 = 5 * d - 1)
    (hq2 : q = 2 * n)
    (hr1 : r^2 = 13 * d - 1)
    (hr2 : r = 2 * m) :
    False := by

  -- Step 1: Prove d is odd by establishing d = 2(k^2 - k) + 1
  have hd_eq : 2 * d = 4 * k^2 - 4 * k + 2 := by
    calc 2 * d = p^2 + 1 := by linarith [hp1]
      _ = (2 * k - 1)^2 + 1 := by rw [hp2]
      _ = 4 * k^2 - 4 * k + 2 := by ring
  have hd : d = 2 * (k^2 - k) + 1 := by linarith [hd_eq]

  -- Step 2: Establish 8d = r^2 - q^2
  have h8d : 8 * d = r^2 - q^2 := by
    calc 8 * d = (13 * d - 1) - (5 * d - 1) := by ring
      _ = r^2 - q^2 := by rw [hr1, hq1]

  -- Step 3: Establish 2d = (m - n)(m + n)
  have h_m_n : 2 * d = (m - n) * (m + n) := by
    have h4 : 4 * (2 * d) = 4 * ((m - n) * (m + n)) := by
      calc 4 * (2 * d) = 8 * d := by ring
        _ = r^2 - q^2 := h8d
        _ = (2 * m)^2 - (2 * n)^2 := by rw [hr2, hq2]
        _ = 4 * ((m - n) * (m + n)) := by ring
    linarith [h4]

  -- Step 4: Define quotients to set up parity cases for (m - n) and (m + n)
  let u := (m - n) / 2
  let v := (m + n) / 2
  have h_cases : (m - n = 2 * u ∧ m + n = 2 * v) ∨
                 (m - n = 2 * u + 1 ∧ m + n = 2 * v + 1) := by
    have h_sum : (m - n) + (m + n) = 2 * m := by ring
    -- The omega tactic easily resolves the remainder bounds and equivalence
    omega

  -- Step 5: Derive the mathematical contradiction for both parity cases
  cases h_cases with
  | inl heven =>
    have h_sub : 2 * d = 4 * (u * v) := by
      calc 2 * d = (m - n) * (m + n) := h_m_n
        _ = (2 * u) * (2 * v) := by rw [heven.1, heven.2]
        _ = 4 * (u * v) := by ring
    have hd_lin : 4 * (k^2 - k) + 2 = 4 * (u * v) := by
      calc 4 * (k^2 - k) + 2 = 2 * (2 * (k^2 - k) + 1) := by ring
        _ = 2 * d := by rw [← hd]
        _ = 4 * (u * v) := h_sub
    
    -- Evaluates 4X + 2 = 4Y (which has no integer solutions)
    omega

  | inr hodd =>
    have h_sub : 2 * d = 4 * (u * v) + 2 * u + 2 * v + 1 := by
      calc 2 * d = (m - n) * (m + n) := h_m_n
        _ = (2 * u + 1) * (2 * v + 1) := by rw [hodd.1, hodd.2]
        _ = 4 * (u * v) + 2 * u + 2 * v + 1 := by ring
    have hd_lin : 4 * (k^2 - k) + 2 = 4 * (u * v) + 2 * u + 2 * v + 1 := by
      calc 4 * (k^2 - k) + 2 = 2 * (2 * (k^2 - k) + 1) := by ring
        _ = 2 * d := by rw [← hd]
        _ = 4 * (u * v) + 2 * u + 2 * v + 1 := h_sub
    
    -- Evaluates 4X + 2 = 2(2Y + u + v) + 1 (Even = Odd)
    omega

end IMO1986P1
