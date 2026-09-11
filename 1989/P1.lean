import Mathlib

open scoped BigOperators

namespace IMO1989P1

/-
We use zero-based row indices i = 0, ..., 116.

The original low element in row i is i + 1.

The swaps from the solution are

  1 ↔ 59, 2 ↔ 58, ..., 29 ↔ 31, 30 ↔ 30,

and

  60 ↔ 117, 61 ↔ 116, ..., 88 ↔ 89.

In zero-based indexing this sends

  i ↦ 58 - i       for 0 ≤ i ≤ 58,
  i ↦ 175 - i      for 59 ≤ i ≤ 116.
-/
def swapLow (i : Fin 117) : ℕ :=
  if i.val ≤ 58 then
    58 - i.val
  else
    175 - i.val

/-
Row i consists of:

* the swapped low element `swapLow i + 1`;
* the high partner `1989 - i`;
* seven untouched complementary pairs;
* one element from 937,...,1053 which compensates
  for the change caused by the swap.

There are therefore 17 elements in each row.
-/
def row (i : Fin 117) : Finset ℕ :=
  { swapLow i + 1,
    1989 - i.val,
    995 + i.val - swapLow i } ∪
  (Finset.Icc 1 7).biUnion
    (fun j =>
      let x := i.val + 1 + 117 * j
      {x, 1990 - x})

/--
IMO 1989, Problem 1.

The set {1, ..., 1989} is a disjoint union of 117 sets,
each containing 17 elements, and all 117 sets have the same sum.

In fact, every set has sum 16915.
-/
theorem imo1989_problem1 :
    ∃ A : Fin 117 → Finset ℕ,
      (∀ i, (A i).card = 17) ∧
      (∀ i, ∑ x ∈ A i, x = 16915) ∧
      (∀ i j, i ≠ j → Disjoint (A i) (A j)) ∧
      (Finset.univ.biUnion A = Finset.Icc 1 1989) := by
  refine ⟨row, ?_⟩
  native_decide

end IMO1989P1
