import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

/-!
# IMO 2007, Problem 6 (Upper Bound)

Let `n` be a positive integer. Consider
`S = {(x, y, z) : x, y, z ∈ {0, 1, …, n}, x + y + z > 0}`
as a set of `(n+1)^3 - 1` points in three dimensional space. 

This formalization proves the constructive upper bound: 
The set `S` can be covered by exactly `3 * n` planes without covering the origin `(0,0,0)`.
-/

namespace IMO2007P6

/-- The set `S` of the problem: the lattice points of the cube `{0,…,n}^3`, origin removed. -/
def gridS (n : ℕ) : Set (ℝ × ℝ × ℝ) :=
  {p | ∃ x y z : ℕ, x ≤ n ∧ y ≤ n ∧ z ≤ n ∧ 0 < x + y + z ∧
      p = ((x : ℝ), (y : ℝ), (z : ℝ))}

/-- The plane `a * X + b * Y + c * Z = d` of `ℝ³`. -/
def planeSet (a b c d : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {p | a * p.1 + b * p.2.1 + c * p.2.2 = d}

theorem mem_planeSet {a b c d : ℝ} {p : ℝ × ℝ × ℝ} :
    p ∈ planeSet a b c d ↔ a * p.1 + b * p.2.1 + c * p.2.2 = d := Iff.rfl

/-- `CoversS n m` says that there are `m` planes of `ℝ³` whose union contains the set
`gridS n` but does not contain the origin. -/
def CoversS (n m : ℕ) : Prop :=
  ∃ A B C D : Fin m → ℝ,
    (∀ j, ¬ (A j = 0 ∧ B j = 0 ∧ C j = 0)) ∧
    gridS n ⊆ (⋃ j, planeSet (A j) (B j) (C j) (D j)) ∧
    ((0 : ℝ), (0 : ℝ), (0 : ℝ)) ∉ (⋃ j, planeSet (A j) (B j) (C j) (D j))

/-! ### The upper bound: `3 * n` planes suffice -/

/-- The `3 * n` planes `x = k`, `y = k`, `z = k` for `k = 1, …, n` cover `gridS n`
and avoid the origin. -/
theorem coversS_three_mul (n : ℕ) : CoversS n (3 * n) := by
  classical
  -- the `j`-th plane is `x = j+1` for `j < n`, `y = j+1-n` for `n ≤ j < 2n`,
  -- and `z = j+1-2n` for `2n ≤ j`.
  refine ⟨fun j => if (j : ℕ) < n then 1 else 0,
          fun j => if n ≤ (j : ℕ) ∧ (j : ℕ) < 2 * n then 1 else 0,
          fun j => if 2 * n ≤ (j : ℕ) then 1 else 0,
          fun j => if (j : ℕ) < n then (((j : ℕ) + 1 : ℕ) : ℝ)
            else if (j : ℕ) < 2 * n then (((j : ℕ) + 1 - n : ℕ) : ℝ)
            else (((j : ℕ) + 1 - 2 * n : ℕ) : ℝ), ?_, ?_, ?_⟩
  · intro j
    rcases lt_or_ge (j : ℕ) n with h | h
    · simp [h]
    · rcases lt_or_ge (j : ℕ) (2 * n) with h' | h'
      · simp [Nat.not_lt.mpr h, h, h']
      · simp [Nat.not_lt.mpr h, h']
  · rintro p ⟨x, y, z, hx, hy, hz, hpos, rfl⟩
    simp only [Set.mem_iUnion, mem_planeSet]
    rcases Nat.eq_zero_or_pos x with hx0 | hx0
    · rcases Nat.eq_zero_or_pos y with hy0 | hy0
      · -- z > 0
        have hz0 : 0 < z := by omega
        have hjlt : 2 * n + z - 1 < 3 * n := by omega
        refine ⟨⟨2 * n + z - 1, hjlt⟩, ?_⟩
        have h1 : ¬ (2 * n + z - 1 < n) := by omega
        have h2 : ¬ (2 * n + z - 1 < 2 * n) := by omega
        have h3 : 2 * n ≤ 2 * n + z - 1 := by omega
        have h4 : 2 * n + z - 1 + 1 - 2 * n = z := by omega
        simp only [h1, h2, h3, h4, ite_true, ite_false, hx0, hy0]
        norm_num
      · have hjlt : n + y - 1 < 3 * n := by omega
        refine ⟨⟨n + y - 1, hjlt⟩, ?_⟩
        have h1 : ¬ (n + y - 1 < n) := by omega
        have h2 : n + y - 1 < 2 * n := by omega
        have h3 : n ≤ n + y - 1 := by omega
        have h4 : n + y - 1 + 1 - n = y := by omega
        have h5 : ¬ (2 * n ≤ n + y - 1) := by omega
        simp only [h1, h2, h3, h4, h5, ite_true, ite_false, hx0, and_self]
        norm_num
    · have hjlt : x - 1 < 3 * n := by omega
      refine ⟨⟨x - 1, hjlt⟩, ?_⟩
      have h1 : x - 1 < n := by omega
      have h4 : x - 1 + 1 = x := by omega
      have h5 : ¬ (n ≤ x - 1 ∧ x - 1 < 2 * n) := by omega
      have h6 : ¬ (2 * n ≤ x - 1) := by omega
      simp only [h1, h4, h5, h6, ite_true, ite_false]
      norm_num
  · simp only [Set.mem_iUnion, mem_planeSet, not_exists]
    intro j
    have hne : ∀ k : ℕ, 0 < k → (0 : ℝ) ≠ (k : ℝ) := fun k hk => (Nat.cast_pos.mpr hk).ne
    simp only [mul_zero, add_zero]
    rcases lt_or_ge (j : ℕ) n with h | h
    · simpa only [h, ite_true] using hne ((j : ℕ) + 1) (by omega)
    · rcases lt_or_ge (j : ℕ) (2 * n) with h' | h'
      · have h1 : ¬ ((j : ℕ) < n) := by omega
        simpa only [h1, h', ite_true, ite_false] using hne ((j : ℕ) + 1 - n) (by omega)
      · have h1 : ¬ ((j : ℕ) < n) := by omega
        have h2 : ¬ ((j : ℕ) < 2 * n) := by omega
        simpa only [h1, h2, ite_false] using hne ((j : ℕ) + 1 - 2 * n) (by omega)

end IMO2007P6
