import Mathlib

/--
Formalization of IMO 1969 Problem 1.
Prove that there are infinitely many natural numbers a with the following property:
the number z = n^4 + a is not prime for any natural number n.

We model "infinitely many" by showing that for any arbitrary bound `m`, 
there exists an `a ≥ m` satisfying the property.
-/
theorem imo1969_p1 (m : ℕ) : ∃ a ≥ m, ∀ n : ℕ, ¬ Nat.Prime (n^4 + a) := by
  -- We choose k such that 4k^4 >= m and k > 1.
  -- Picking k = m + 2 safely guarantees both bounds robustly.
  let k := m + 2
  have hk : 1 < k := by
    dsimp [k]
    omega
    
  let a_val := 4 * k^4
  use a_val
  
  constructor
  · -- Prove a_val ≥ m
    have h_expand : 4 * (m + 2)^4 = 4 * m^4 + 32 * m^3 + 96 * m^2 + 128 * m + 64 := by ring
    dsimp [a_val, k]
    rw [h_expand]
    omega
    
  · -- Prove n^4 + a_val is never prime for any n
    intro n
    -- Base inequality to handle natural number subtraction safely
    have h_le : 2 * n * k ≤ n^2 + 2 * k^2 := by
      zify
      have h_sq : 0 ≤ ((n : ℤ) - k)^2 := sq_nonneg _
      have h_eq : (n : ℤ)^2 + 2*(k : ℤ)^2 - 2*(n : ℤ)*(k : ℤ) = ((n : ℤ) - k)^2 + (k : ℤ)^2 := by ring
      have hk2 : 0 ≤ (k : ℤ)^2 := sq_nonneg _
      linarith

    -- The factors u and v corresponding to Sophie Germain's Identity
    let u := n^2 + 2*k^2 - 2*n*k
    let v := n^2 + 2*k^2 + 2*n*k

    -- Connect u and v to integers for unconstrained ring simplification
    have hu_z : (u : ℤ) = (n : ℤ)^2 + 2*(k : ℤ)^2 - 2*(n : ℤ)*(k : ℤ) := by
      change ((n^2 + 2*k^2 - 2*n*k : ℕ) : ℤ) = _
      rw [Nat.cast_sub h_le]
      push_cast
      rfl

    have hv_z : (v : ℤ) = (n : ℤ)^2 + 2*(k : ℤ)^2 + 2*(n : ℤ)*(k : ℤ) := by
      change ((n^2 + 2*k^2 + 2*n*k : ℕ) : ℤ) = _
      push_cast
      rfl

    -- Prove that both factors are strictly greater than 1
    have hu_gt : 1 < u := by
      have : (1 : ℤ) < u := by
        rw [hu_z]
        have h_eq : (n : ℤ)^2 + 2*(k : ℤ)^2 - 2*(n : ℤ)*(k : ℤ) = ((n : ℤ) - k)^2 + (k : ℤ)^2 := by ring
        rw [h_eq]
        have h1 : 0 ≤ ((n : ℤ) - k)^2 := sq_nonneg _
        have h2 : 1 < (k : ℤ)^2 := by
          have h_k_gt_1 : 1 < (k : ℤ) := by exact_mod_cast hk
          nlinarith
        linarith
      exact_mod_cast this

    have hv_gt : 1 < v := by
      have : (1 : ℤ) < v := by
        rw [hv_z]
        have h_eq : (n : ℤ)^2 + 2*(k : ℤ)^2 + 2*(n : ℤ)*(k : ℤ) = ((n : ℤ) + k)^2 + (k : ℤ)^2 := by ring
        rw [h_eq]
        have h1 : 0 ≤ ((n : ℤ) + k)^2 := sq_nonneg _
        have h2 : 1 < (k : ℤ)^2 := by
          have h_k_gt_1 : 1 < (k : ℤ) := by exact_mod_cast hk
          nlinarith
        linarith
      exact_mod_cast this

    -- Factorize the main polynomial 
    have huv_eq : n^4 + a_val = u * v := by
      have : (n^4 + a_val : ℤ) = (u : ℤ) * (v : ℤ) := by
        rw [hu_z, hv_z]
        dsimp [a_val]
        ring
      exact_mod_cast this

    -- Conclude that it cannot be prime since it splits into factors > 1
    rw [huv_eq]
    intro hp
    have hdvd : u ∣ u * v := dvd_mul_right u v
    have h_eq_or := Nat.Prime.eq_one_or_self_of_dvd hp u hdvd
    
    cases h_eq_or with
    | inl h1 => linarith
    | inr h2 =>
      have h_lt : u < u * v := by nlinarith
      linarith
