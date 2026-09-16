import Mathlib

namespace IMO2003P5

/-!
### Case n = 3
For n = 3, the constant 2(n^2 - 1)/3 evaluates to 16/3.
Because the sum is taken over all pairs 1 ≤ i ≤ j ≤ n, the difference factors 
perfectly to reveal the arithmetic progression condition.
-/

lemma imo2003_p5_n3_identity (x₁ x₂ x₃ : ℝ) :
  (8 / 3 : ℝ) * ((x₂ - x₁)^2 + (x₃ - x₁)^2 + (x₃ - x₂)^2) -
  ((x₂ - x₁) + (x₃ - x₁) + (x₃ - x₂))^2 =
  (4 / 3 : ℝ) * (2 * x₂ - x₁ - x₃)^2 := by
  ring

theorem imo2003_p5_n3 (x₁ x₂ x₃ : ℝ) :
  ((x₂ - x₁) + (x₃ - x₁) + (x₃ - x₂))^2 ≤
  (8 / 3 : ℝ) * ((x₂ - x₁)^2 + (x₃ - x₁)^2 + (x₃ - x₂)^2) := by
  -- 1. Apply our exact algebraic identity
  have h_id := imo2003_p5_n3_identity x₁ x₂ x₃
  
  -- 2. Prove the remainder is non-negative since it is a squared real
  have h_sq : 0 ≤ (4 / 3 : ℝ) * (2 * x₂ - x₁ - x₃)^2 := by positivity
  
  -- 3. Conclude the inequality
  linarith

/-!
### Case n = 4
For n = 4, the constant 2(n^2 - 1)/3 evaluates to 10.
Over i ≤ j, the constant scales to 5. The remainder factors into a sum of squares 
that forces (x₂ - x₁ = x₃ - x₂) and (x₃ - x₂ = x₄ - x₃) for equality to hold.
-/

lemma imo2003_p5_n4_identity (x₁ x₂ x₃ x₄ : ℝ) :
  (5 : ℝ) * ((x₂ - x₁)^2 + (x₃ - x₁)^2 + (x₄ - x₁)^2 +
             (x₃ - x₂)^2 + (x₄ - x₂)^2 + (x₄ - x₃)^2) -
  ((x₂ - x₁) + (x₃ - x₁) + (x₄ - x₁) +
   (x₃ - x₂) + (x₄ - x₂) + (x₄ - x₃))^2 =
  2 * ((2 * x₂ - x₁ - x₃)^2 +
       (x₄ + x₂ - 2 * x₃)^2 +
       2 * (x₂ + x₃ - x₁ - x₄)^2) := by
  ring

theorem imo2003_p5_n4 (x₁ x₂ x₃ x₄ : ℝ) :
  ((x₂ - x₁) + (x₃ - x₁) + (x₄ - x₁) +
   (x₃ - x₂) + (x₄ - x₂) + (x₄ - x₃))^2 ≤
  (5 : ℝ) * ((x₂ - x₁)^2 + (x₃ - x₁)^2 + (x₄ - x₁)^2 +
             (x₃ - x₂)^2 + (x₄ - x₂)^2 + (x₄ - x₃)^2) := by
  -- 1. Apply our exact algebraic identity
  have h_id := imo2003_p5_n4_identity x₁ x₂ x₃ x₄
  
  -- 2. Prove the remainder is a sum of squares and therefore non-negative
  have h_sq : 0 ≤ 2 * ((2 * x₂ - x₁ - x₃)^2 +
                       (x₄ + x₂ - 2 * x₃)^2 +
                       2 * (x₂ + x₃ - x₁ - x₄)^2) := by positivity
  
  -- 3. Conclude the inequality
  linarith

end IMO2003P5
