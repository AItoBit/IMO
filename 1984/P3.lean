import Mathlib

namespace Problem_A3

variable {Point : Type}
variable {n : ℕ}
variable (color : Point → Fin n)
variable (C : ℕ → Set Point)

/--
Formalization of the combinatorial core of the argument:
"Suppose there are n colors. Then by taking successively smaller circles 
C_2, C_3, ... , C_{n+1} we reach a contradiction, since each circle includes 
a point of different color to those on any of the larger circles."
-/
theorem contradiction_from_successively_smaller_circles
    (x : Fin (n + 1) → Point)
    (hx : ∀ (j : Fin (n + 1)), x j ∈ C j.val)
    (h_diff : ∀ (i j : Fin (n + 1)), i < j → ∀ y ∈ C i.val, color (x j) ≠ color y) :
    False := by
  
  -- Step 1: Prove that the selected points `x j` all have distinct colors.
  have h_inj : Function.Injective (color ∘ x) := by
    intro i j hij
    -- Compare the indices i and j
    rcases lt_trichotomy i j with h | h | h
    · -- Case i < j: x_j has a different color than everything in C_i (which includes x_i)
      have h_diff_ij := h_diff i j h (x i) (hx i)
      exact False.elim (h_diff_ij hij.symm)
    · -- Case i = j: Trivially true
      exact h
    · -- Case j < i: x_i has a different color than everything in C_j (which includes x_j)
      have h_diff_ji := h_diff j i h (x j) (hx j)
      exact False.elim (h_diff_ji hij)

  -- Step 2: Apply the Pigeonhole Principle.
  -- We have an injective function from a set of size n+1 to a set of size n,
  -- which necessitates a contradiction.
  have h_card := Fintype.card_le_of_injective (color ∘ x) h_inj
  
  -- Expose the cardinalities and finish by linear arithmetic (n + 1 ≤ n is False)
  simp only [Fintype.card_fin] at h_card
  omega

end Problem_A3
