import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-!
# IMO 2008 Problem 2

**(i)** If `x, y, z` are three real numbers, all different from `1`, such that `x * y * z = 1`,
then `x²/(x-1)² + y²/(y-1)² + z²/(z-1)² ≥ 1`.

**(ii)** Equality is achieved for infinitely many triples of rational numbers `x, y, z`
(all different from `1`, with `x * y * z = 1`).
-/

namespace Imo2008P2

/-- The key algebraic identity behind the problem: modulo the constraint `x * y * z = 1`,
the quantity `x²(y-1)²(z-1)² + y²(x-1)²(z-1)² + z²(x-1)²(y-1)² - ((x-1)(y-1)(z-1))²`
is a perfect square. -/
theorem key_identity (x y z : ℝ) (h : x * y * z = 1) :
    x ^ 2 * (y - 1) ^ 2 * (z - 1) ^ 2 + y ^ 2 * (x - 1) ^ 2 * (z - 1) ^ 2 +
        z ^ 2 * (x - 1) ^ 2 * (y - 1) ^ 2 - ((x - 1) * (y - 1) * (z - 1)) ^ 2
      = ((x - 1) * (y - 1) * (z - 1) - x * (y - 1) * (z - 1) - y * (x - 1) * (z - 1) -
          z * (x - 1) * (y - 1)) ^ 2 := by
  linear_combination (-2 * ((x - 1) * (y - 1) * (z - 1))) * h

/-- **IMO 2008, Problem 2 (i).** For real numbers `x, y, z`, all different from `1`, with
`x * y * z = 1`, we have `x²/(x-1)² + y²/(y-1)² + z²/(z-1)² ≥ 1`. -/
theorem sum_sq_div_ge_one (x y z : ℝ) (hx : x ≠ 1) (hy : y ≠ 1) (hz : z ≠ 1)
    (h : x * y * z = 1) :
    1 ≤ x ^ 2 / (x - 1) ^ 2 + y ^ 2 / (y - 1) ^ 2 + z ^ 2 / (z - 1) ^ 2 := by
  have ha : x - 1 ≠ 0 := sub_ne_zero.mpr hx
  have hb : y - 1 ≠ 0 := sub_ne_zero.mpr hy
  have hc : z - 1 ≠ 0 := sub_ne_zero.mpr hz
  have key : x ^ 2 / (x - 1) ^ 2 + y ^ 2 / (y - 1) ^ 2 + z ^ 2 / (z - 1) ^ 2 - 1
      = (((x - 1) * (y - 1) * (z - 1) - x * (y - 1) * (z - 1) - y * (x - 1) * (z - 1) -
          z * (x - 1) * (y - 1)) / ((x - 1) * (y - 1) * (z - 1))) ^ 2 := by
    rw [div_pow, eq_div_iff (by positivity)]
    field_simp
    linear_combination key_identity x y z h
  nlinarith [sq_nonneg (((x - 1) * (y - 1) * (z - 1) - x * (y - 1) * (z - 1) -
    y * (x - 1) * (z - 1) - z * (x - 1) * (y - 1)) / ((x - 1) * (y - 1) * (z - 1)))]

/-- The rational family achieving equality, parametrized by `k : ℚ` with `k ≠ ±1`. -/
def tripleOf (k : ℚ) : ℚ × ℚ × ℚ :=
  ((1 - k ^ 2) / 4, -2 * (k + 1) / (k - 1) ^ 2, 2 * (k - 1) / (k + 1) ^ 2)

/-- The set of rational triples `(x, y, z)`, all entries different from `1`, with `x * y * z = 1`
and with equality `x²/(x-1)² + y²/(y-1)² + z²/(z-1)² = 1`. -/
def equalitySet : Set (ℚ × ℚ × ℚ) :=
  {p : ℚ × ℚ × ℚ | p.1 ≠ 1 ∧ p.2.1 ≠ 1 ∧ p.2.2 ≠ 1 ∧ p.1 * p.2.1 * p.2.2 = 1 ∧
    p.1 ^ 2 / (p.1 - 1) ^ 2 + p.2.1 ^ 2 / (p.2.1 - 1) ^ 2 + p.2.2 ^ 2 / (p.2.2 - 1) ^ 2 = 1}

/-- Every member of the family `tripleOf k` (for `k ≠ ±1`) lies in `equalitySet`. -/
theorem tripleOf_mem (k : ℚ) (h1 : k ≠ 1) (h2 : k ≠ -1) : tripleOf k ∈ equalitySet := by
  have ha : k - 1 ≠ 0 := sub_ne_zero.mpr h1
  have hb : k + 1 ≠ 0 := fun h => h2 (by linarith)
  have hs : k ^ 2 + 3 ≠ 0 := by positivity
  have e1 : (1 - k ^ 2) / 4 - 1 = -(k ^ 2 + 3) / 4 := by ring
  have e2 : -2 * (k + 1) / (k - 1) ^ 2 - 1 = -(k ^ 2 + 3) / (k - 1) ^ 2 := by field_simp; ring
  have e3 : 2 * (k - 1) / (k + 1) ^ 2 - 1 = -(k ^ 2 + 3) / (k + 1) ^ 2 := by field_simp; ring
  simp only [equalitySet, tripleOf, Set.mem_setOf_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h
    apply hs
    rw [h] at e1
    field_simp at e1
    linarith
  · intro h
    apply hs
    rw [h] at e2
    field_simp at e2
    linarith
  · intro h
    apply hs
    rw [h] at e3
    field_simp at e3
    linarith
  · field_simp
    ring
  · rw [e1, e2, e3]
    field_simp
    ring

/-- **IMO 2008, Problem 2 (ii).** There are infinitely many rational triples `(x, y, z)`,
all entries different from `1`, with `x * y * z = 1`, for which equality holds. -/
theorem equalitySet_infinite : equalitySet.Infinite := by
  refine Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ => tripleOf ((n : ℚ) + 2)) ?_ ?_
  · intro m n hmn
    simp only [tripleOf, Prod.mk.injEq] at hmn
    have h : ((m : ℚ) + 2) ^ 2 = ((n : ℚ) + 2) ^ 2 := by linarith [hmn.1]
    have hm : (0 : ℚ) ≤ (m : ℚ) + 2 := by positivity
    have hn : (0 : ℚ) ≤ (n : ℚ) + 2 := by positivity
    have hmn' : (m : ℚ) = (n : ℚ) := by nlinarith
    exact_mod_cast hmn'
  · intro n
    refine tripleOf_mem _ ?_ ?_ <;>
      · intro h
        have : (0 : ℚ) ≤ (n : ℚ) := Nat.cast_nonneg n
        linarith

end Imo2008P2
