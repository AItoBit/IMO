import Mathlib

/-!
# IMO 1985, Problem 2 (Solution Formalization)

The problem asks to prove that a specific coloring of the set {1, 2, ..., n-1}
must be monochromatic. The provided solution extends the coloring to all 
residues modulo n (i.e., a periodic function on ℤ), where the properties 
translate cleanly to modular arithmetic. 

We formalize the algebraic core of this extended problem:
Given a periodic function `c : ℤ → α` with period `n`, satisfying the 
symmetry condition `c(i) = c(-i)` and the shift condition 
`c(i) = c(i - k)` or `c(i) = c(k - i)`, we prove `c` is constant.
-/

namespace IMO1985P2

theorem imo1985_p2_solution {α : Type*}
    (n k : ℤ)
    (h_coprime : Int.gcd n k = 1)
    (c : ℤ → α)
    (h_per : ∀ i : ℤ, c (i + n) = c i)
    (h1 : ∀ i : ℤ, c i = c (-i))
    (h2 : ∀ i : ℤ, c i = c (i - k) ∨ c i = c (k - i)) :
    ∀ i j : ℤ, c i = c j := by

  -- Establish the uniform subtraction shift rule
  have h_sub : ∀ i : ℤ, c i = c (i - k) := by
    intro i
    cases h2 i with
    | inl h => exact h
    | inr h =>
      have h_symm := h1 (i - k)
      have h_neg : -(i - k) = k - i := by ring
      rw [h_neg] at h_symm
      rw [h, ← h_symm]

  -- Establish the addition shift rule
  have h_add : ∀ i : ℤ, c (i + k) = c i := by
    intro i
    have := h_sub (i + k)
    have h_simp : i + k - k = i := by ring
    rw [h_simp] at this
    exact this

  have h_sub_k : ∀ i : ℤ, c (i - k) = c i := by
    intro i
    have h_eq := h_add (i - k)
    have h_simp : i - k + k = i := by ring
    rw [h_simp] at h_eq
    exact h_eq.symm

  -- Lift the shift rule to all natural multiples of k
  have h_mul_k_nat_add : ∀ m : ℕ, ∀ i : ℤ, c (i + m * k) = c i := by
    intro m
    induction m with
    | zero =>
      intro i
      have H : i + ((0 : ℕ) : ℤ) * k = i := by push_cast; ring
      rw [H]
    | succ m ih =>
      intro i
      have H : i + ((m + 1 : ℕ) : ℤ) * k = (i + (m : ℤ) * k) + k := by push_cast; ring
      rw [H, h_add, ih]

  have h_mul_k_nat_sub : ∀ m : ℕ, ∀ i : ℤ, c (i - m * k) = c i := by
    intro m
    induction m with
    | zero =>
      intro i
      have H : i - ((0 : ℕ) : ℤ) * k = i := by push_cast; ring
      rw [H]
    | succ m ih =>
      intro i
      have H : i - ((m + 1 : ℕ) : ℤ) * k = (i - (m : ℤ) * k) - k := by push_cast; ring
      rw [H, h_sub_k, ih]

  -- Generalize to all integer multiples of k
  have h_mul_k : ∀ m : ℤ, ∀ i : ℤ, c (i + m * k) = c i := by
    intro m i
    cases m with
    | ofNat w =>
      exact h_mul_k_nat_add w i
    | negSucc w =>
      have h_eq : i + (Int.negSucc w : ℤ) * k = i - ((w + 1 : ℕ) : ℤ) * k := by 
        show i + -(↑(w + 1) : ℤ) * k = i - ↑(w + 1) * k
        ring
      rw [h_eq]
      exact h_mul_k_nat_sub (w + 1) i

  -- Establish parallel properties for the period n
  have h_sub_n : ∀ i : ℤ, c (i - n) = c i := by
    intro i
    have h_eq := h_per (i - n)
    have h_simp : i - n + n = i := by ring
    rw [h_simp] at h_eq
    exact h_eq.symm

  have h_mul_n_nat_add : ∀ m : ℕ, ∀ i : ℤ, c (i + m * n) = c i := by
    intro m
    induction m with
    | zero =>
      intro i
      have H : i + ((0 : ℕ) : ℤ) * n = i := by push_cast; ring
      rw [H]
    | succ m ih =>
      intro i
      have H : i + ((m + 1 : ℕ) : ℤ) * n = (i + (m : ℤ) * n) + n := by push_cast; ring
      rw [H, h_per, ih]

  have h_mul_n_nat_sub : ∀ m : ℕ, ∀ i : ℤ, c (i - m * n) = c i := by
    intro m
    induction m with
    | zero =>
      intro i
      have H : i - ((0 : ℕ) : ℤ) * n = i := by push_cast; ring
      rw [H]
    | succ m ih =>
      intro i
      have H : i - ((m + 1 : ℕ) : ℤ) * n = (i - (m : ℤ) * n) - n := by push_cast; ring
      rw [H, h_sub_n, ih]

  have h_mul_n : ∀ m : ℤ, ∀ i : ℤ, c (i + m * n) = c i := by
    intro m i
    cases m with
    | ofNat w =>
      exact h_mul_n_nat_add w i
    | negSucc w =>
      have h_eq : i + (Int.negSucc w : ℤ) * n = i - ((w + 1 : ℕ) : ℤ) * n := by 
        show i + -(↑(w + 1) : ℤ) * n = i - ↑(w + 1) * n
        ring
      rw [h_eq]
      exact h_mul_n_nat_sub (w + 1) i

  -- Use Bezout's identity to prove the color is invariant under shifts of 1
  have h_step_one : ∀ i : ℤ, c (i + 1) = c i := by
    intro i
    have hc : (Int.gcd n k : ℤ) = 1 := by
      rw [h_coprime]
      rfl
    have h_eq : i + 1 = i + (Int.gcd n k : ℤ) := by rw [hc]
    have h_eq2 : i + (Int.gcd n k : ℤ) = (i + Int.gcdB n k * k) + Int.gcdA n k * n := by
      have h_ab := Int.gcd_eq_gcd_ab n k
      rw [h_ab]
      ring
    rw [h_eq, h_eq2]
    rw [h_mul_n (Int.gcdA n k) (i + Int.gcdB n k * k)]
    rw [h_mul_k (Int.gcdB n k) i]

  have h_sub_one : ∀ i : ℤ, c (i - 1) = c i := by
    intro i
    have h_eq := h_step_one (i - 1)
    have h_simp : i - 1 + 1 = i := by ring
    rw [h_simp] at h_eq
    exact h_eq.symm

  -- Lift the unit shift to all integers
  have h_mul_1_nat_add : ∀ m : ℕ, ∀ i : ℤ, c (i + m) = c i := by
    intro m
    induction m with
    | zero =>
      intro i
      have H : i + ((0 : ℕ) : ℤ) = i := by push_cast; ring
      rw [H]
    | succ m ih =>
      intro i
      have H : i + ((m + 1 : ℕ) : ℤ) = (i + (m : ℤ)) + 1 := by push_cast; ring
      rw [H, h_step_one, ih]

  have h_mul_1_nat_sub : ∀ m : ℕ, ∀ i : ℤ, c (i - m) = c i := by
    intro m
    induction m with
    | zero =>
      intro i
      have H : i - ((0 : ℕ) : ℤ) = i := by push_cast; ring
      rw [H]
    | succ m ih =>
      intro i
      have H : i - ((m + 1 : ℕ) : ℤ) = (i - (m : ℤ)) - 1 := by push_cast; ring
      rw [H, h_sub_one, ih]

  have h_mul_1 : ∀ m : ℤ, ∀ i : ℤ, c (i + m) = c i := by
    intro m i
    cases m with
    | ofNat w =>
      exact h_mul_1_nat_add w i
    | negSucc w =>
      have h_eq : i + (Int.negSucc w : ℤ) = i - ((w + 1 : ℕ) : ℤ) := by 
        show i + -(↑(w + 1) : ℤ) = i - ↑(w + 1)
        ring
      rw [h_eq]
      exact h_mul_1_nat_sub (w + 1) i

  -- Conclude the function is entirely constant
  intro i j
  have H : j = i + (j - i) := by ring
  rw [H, h_mul_1 (j - i) i]

end IMO1985P2
