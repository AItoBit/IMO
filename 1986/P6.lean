import Mathlib

/-!
# IMO 1986, Problem 6 (Algebraic Core of Solution 2) 

In the inductive step where all lines initially have an even number of points,
removing a point `P_y` leaves exactly one horizontal line `r₀` and one
vertical line `c₀` with an odd number of points. All other lines have an
even number of points, and thus their assigned colorings sum to 0.

By evaluating the total sum of the colors of all remaining points in two ways
(grouping by rows vs. grouping by columns), we prove that the sum along 
`r₀` must exactly equal the sum along `c₀`. This guarantees that a single 
new color assignment at `P_y` will perfectly balance both lines simultaneously.
-/

namespace IMO1986P6

open Finset

/-- 
Given a finite grid of points colored with integers, if all rows sum to 0 
except row `r₀` which sums to `t_h`, and all columns sum to 0 except 
column `c₀` which sums to `t_v`, then `t_h = t_v`.
-/
theorem double_counting_core
    {α : Type*} [Fintype α] [DecidableEq α]
    {β : Type*} [Fintype β] [DecidableEq β]
    (f : α → β → ℤ)
    (r₀ : α) (c₀ : β)
    (t_h t_v : ℤ)
    (h_rows : ∀ r ≠ r₀, ∑ c, f r c = 0)
    (h_r₀   : ∑ c, f r₀ c = t_h)
    (h_cols : ∀ c ≠ c₀, ∑ r, f r c = 0)
    (h_c₀   : ∑ r, f r c₀ = t_v) :
    t_h = t_v := by

  -- Evaluate the total sum of the grid by isolating the non-zero row
  have sum_by_rows : ∑ r, ∑ c, f r c = t_h := by
    calc ∑ r, ∑ c, f r c = ∑ c, f r₀ c := by
           apply sum_eq_single r₀
           · intro r _ hr_neq
             exact h_rows r hr_neq
           · intro h_not_in
             exact False.elim (h_not_in (mem_univ r₀))
         _ = t_h := h_r₀

  -- Evaluate the total sum of the grid by isolating the non-zero column
  have sum_by_cols : ∑ c, ∑ r, f r c = t_v := by
    calc ∑ c, ∑ r, f r c = ∑ r, f r c₀ := by
           apply sum_eq_single c₀
           · intro c _ hc_neq
             exact h_cols c hc_neq
           · intro h_not_in
             exact False.elim (h_not_in (mem_univ c₀))
         _ = t_v := h_c₀

  -- Swap the summation order (Fubini's theorem for finite sums)
  have swap_sum : ∑ r, ∑ c, f r c = ∑ c, ∑ r, f r c := sum_comm

  -- Combine the evaluations to prove equality
  calc t_h = ∑ r, ∑ c, f r c := sum_by_rows.symm
    _ = ∑ c, ∑ r, f r c := swap_sum
    _ = t_v := sum_by_cols

end IMO1986P6
