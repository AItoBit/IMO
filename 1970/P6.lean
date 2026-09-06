import Mathlib

/--
Formalization of the logical core of the "Solution re-written" for IMO 1970 Problem 6. 

The rewritten solution notes a key abstraction: we do not actually need to compute 
the exact overcounting factor `k = C(n-3, 2)` ("...but we don't need this"). 
We only need to know that it is strictly positive, and that it uniformly scales 
both the total number of triangles `T` and the number of acute triangles `A` 
into the lists `L₁` and `L₂`.
-/
theorem imo1970_p6_rewritten_logic (A T L1 L2 k : ℕ)
    (hk_pos : 0 < k)
    (hL1 : L1 = k * T)
    (hL2 : L2 = k * A)
    (h_ratio : 10 * L2 ≤ 7 * L1) :
    10 * A ≤ 7 * T := by
  
  -- Substitute the definitions of L1 and L2 into the ratio inequality
  -- and rearrange the terms to isolate the positive scalar k.
  have h_scaled : k * (10 * A) ≤ k * (7 * T) := by
    calc k * (10 * A)
      _ = 10 * (k * A) := by ring
      _ = 10 * L2 := by rw [← hL2]
      _ ≤ 7 * L1 := h_ratio
      _ = 7 * (k * T) := by rw [hL1]
      _ = k * (7 * T) := by ring

  -- Cancel the strictly positive overcounting factor k 
  -- to conclude the final bounds between A and T.
  exact Nat.le_of_mul_le_mul_left h_scaled hk_pos
