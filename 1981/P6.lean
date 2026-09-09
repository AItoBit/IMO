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

namespace IMO1981P6

/-- The power tower of twos: `tower 0 = 1`, `tower (n+1) = 2 ^ tower n`.
So `tower n = 2^2^⋯^2` with `n` twos. -/
def tower : ℕ → ℕ
  | 0 => 1
  | n + 1 => 2 ^ tower n

section
variable (f : ℕ → ℕ → ℕ)
  (h1 : ∀ y, f 0 y = y + 1)
  (h2 : ∀ x, f (x + 1) 0 = f x 1)
  (h3 : ∀ x y, f (x + 1) (y + 1) = f x (f (x + 1) y))

include h1 h2 h3

/-- `f 1 y = y + 2`. -/
theorem f_one (y : ℕ) : f 1 y = y + 2 := by
  induction y with
  | zero =>
      have e : f 1 0 = f 0 1 := h2 0
      rw [e, h1]
  | succ y ih =>
      have e : f 1 (y + 1) = f 0 (f 1 y) := h3 0 y
      rw [e, h1, ih]

/-- `f 2 y = 2 * y + 3`. -/
theorem f_two (y : ℕ) : f 2 y = 2 * y + 3 := by
  induction y with
  | zero =>
      have e : f 2 0 = f 1 1 := h2 1
      rw [e, f_one f h1 h2 h3]
  | succ y ih =>
      have e : f 2 (y + 1) = f 1 (f 2 y) := h3 1 y
      rw [e, f_one f h1 h2 h3, ih]
      ring

/-- `f 3 y + 3 = 2 ^ (y + 3)`. -/
theorem f_three (y : ℕ) : f 3 y + 3 = 2 ^ (y + 3) := by
  induction y with
  | zero =>
      have e : f 3 0 = f 2 1 := h2 2
      rw [e, f_two f h1 h2 h3]
      norm_num
  | succ y ih =>
      have e : f 3 (y + 1) = f 2 (f 3 y) := h3 2 y
      have hp : (2 : ℕ) ^ (y + 1 + 3) = 2 * 2 ^ (y + 3) := by ring
      rw [e, f_two f h1 h2 h3]
      omega

/-- `f 4 y + 3 = tower (y + 3)`. -/
theorem f_four (y : ℕ) : f 4 y + 3 = tower (y + 3) := by
  induction y with
  | zero =>
      have e : f 4 0 = f 3 1 := h2 3
      have h := f_three f h1 h2 h3 1
      rw [e]
      norm_num [tower] at h ⊢
      omega
  | succ y ih =>
      have e : f 4 (y + 1) = f 3 (f 4 y) := h3 3 y
      have h := f_three f h1 h2 h3 (f 4 y)
      have ht : tower (y + 1 + 3) = 2 ^ tower (y + 3) := rfl
      rw [e, h, ht, ih]

/-- **IMO 1981, Problem 6.** For the Ackermann-type function `f`,
`f 4 1981 = 2^2^⋯^2 - 3`, a tower of 1984 twos minus 3. -/
theorem f_four_1981 : f 4 1981 = tower 1984 - 3 := by
  have h := f_four f h1 h2 h3 1981
  norm_num at h
  omega

end

end IMO1981P6
