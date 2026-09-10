import Mathlib

/-!
# IMO 1984, Problem 2 (Solution)

Reference to the provided solution: image_092bb0.png

The solution rests on the algebraic identity:
$(a + b)^7 - a^7 - b^7 = 7ab(a + b)(a^2 + ab + b^2)^2$.

Because subtraction in `ℕ` behaves poorly (it truncates to 0), the `ring` 
tactic fails to cancel terms. By working over `ℤ` (and enforcing `0 < a`, `0 < b`),
we get a true ring where the identity is easily verified.
-/

namespace IMO1984P2

/-- The core algebraic identity from the solution, formulated over ℤ. -/
lemma identity (a b : ℤ) :
    (a + b)^7 - a^7 - b^7 = 7 * a * b * (a + b) * (a^2 + a * b + b^2)^2 := by
  ring

/-- **IMO 1984, Problem 2.**
Find one pair of positive integers a, b such that:
(i) ab(a + b) is not divisible by 7;
(ii) (a + b)^7 - a^7 - b^7 is divisible by 7^7. -/
theorem imo1984_p2 :
    ∃ a b : ℤ, 0 < a ∧ 0 < b ∧ ¬(7 ∣ a * b * (a + b)) ∧ 7^7 ∣ (a + b)^7 - a^7 - b^7 := by
  -- As found in the text, we use a = 18 and b = 1
  use 18, 1
  refine ⟨by decide, by decide, by decide, ?_⟩
  
  -- Apply the binomial expansion identity
  rw [identity]
  
  -- Substitute the inner quadratic factor with 7^3
  have h_square : (18 : ℤ)^2 + 18 * 1 + 1^2 = 7^3 := by decide
  rw [h_square]
  
  -- Rearrange the powers of 7 to explicitly show 7^7 as a factor
  have h_factor : 7 * 18 * 1 * (18 + 1) * ((7 : ℤ)^3)^2 = 7^7 * (18 * 1 * (18 + 1)) := by ring
  rw [h_factor]
  
  exact dvd_mul_right (7^7) (18 * 1 * (18 + 1))

end IMO1984P2
