import Mathlib

namespace Imo2004P2

open Polynomial

/-- Scaling the variable scales the coefficients. -/
theorem coeff_comp_C_mul_X (f : ℝ[X]) (r : ℝ) (n : ℕ) :
    (f.comp (C r * X)).coeff n = f.coeff n * r ^ n := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [add_comp, coeff_add, hp, hq, coeff_add, add_mul]
  | monomial m a =>
      have h1 : (monomial m a).comp (C r * X) = monomial m (a * r ^ m) := by
        rw [monomial_comp, mul_pow, ← C_pow, ← mul_assoc, ← C_mul, C_mul_X_pow_eq_monomial]
      rw [h1, coeff_monomial, coeff_monomial]
      split_ifs with h
      · rw [h]
      · ring

/-- `8ⁿ` overtakes `2·7ⁿ` from `n = 6` on. -/
theorem two_mul_seven_pow_lt (n : ℕ) (hn : 6 ≤ n) : 2 * 7 ^ n < 8 ^ n := by
  induction n with
  | zero => omega
  | succ m ih =>
      rcases Nat.lt_or_ge m 6 with h | h
      · have hm : m = 5 := by omega
        subst hm
        norm_num
      · have h1 := ih h
        have hpos : (0 : ℕ) < 8 ^ m := pow_pos (by norm_num) m
        have e1 : 2 * 7 ^ (m + 1) = 7 * (2 * 7 ^ m) := by ring
        have e2 : (8 : ℕ) ^ (m + 1) = 8 * 8 ^ m := by ring
        omega

/-- **IMO 2004 P2.** -/
theorem imo2004_p2 (f : ℝ[X]) :
    (∀ a b c : ℝ, a * b + b * c + c * a = 0 →
        f.eval (a - b) + f.eval (b - c) + f.eval (c - a) = 2 * f.eval (a + b + c))
      ↔ ∃ p q : ℝ, f = C p * X ^ 4 + C q * X ^ 2 := by
  constructor
  · intro h
    -- `f` is even
    have hzero0 : f.eval 0 = 0 := by
      have h0 := h 0 0 0 (by ring)
      norm_num at h0
      linarith
    have heven : ∀ x : ℝ, f.eval (-x) = f.eval x := by
      intro x
      have h1 := h x 0 0 (by ring)
      norm_num at h1
      linarith [hzero0]
    -- hence the odd coefficients vanish
    have hcompneg : f.comp (C (-1 : ℝ) * X) = f := by
      apply Polynomial.funext
      intro x
      rw [eval_comp]
      simp only [eval_mul, eval_C, eval_X]
      have : (-1 : ℝ) * x = -x := by ring
      rw [this]
      exact heven x
    have hodd : ∀ n : ℕ, Odd n → f.coeff n = 0 := by
      intro n hn
      have h1 := coeff_comp_C_mul_X f (-1) n
      rw [hcompneg, hn.neg_one_pow] at h1
      linarith
    -- the substitution `(6x, 3x, -2x)`
    have hrel : ∀ x : ℝ,
        f.eval (3 * x) + f.eval (5 * x) + f.eval ((-8 : ℝ) * x) = 2 * f.eval (7 * x) := by
      intro x
      have h2 := h (6 * x) (3 * x) (-(2 * x)) (by ring)
      rw [show 6 * x - 3 * x = 3 * x from by ring,
        show 3 * x - -(2 * x) = 5 * x from by ring,
        show -(2 * x) - 6 * x = (-8 : ℝ) * x from by ring,
        show 6 * x + 3 * x + -(2 * x) = 7 * x from by ring] at h2
      exact h2
    -- as an identity of polynomials
    have hpoly : f.comp (C (3 : ℝ) * X) + f.comp (C (5 : ℝ) * X) + f.comp (C (-8 : ℝ) * X)
        = C (2 : ℝ) * f.comp (C (7 : ℝ) * X) := by
      apply Polynomial.funext
      intro x
      simp only [eval_add, eval_mul, eval_comp, eval_C, eval_X]
      exact hrel x
    -- compare coefficients
    have hcoeff : ∀ n : ℕ,
        f.coeff n * ((3 : ℝ) ^ n + 5 ^ n + (-8 : ℝ) ^ n - 2 * 7 ^ n) = 0 := by
      intro n
      have h1 := congrArg (fun p : ℝ[X] => p.coeff n) hpoly
      simp only [coeff_add, coeff_C_mul] at h1
      rw [coeff_comp_C_mul_X, coeff_comp_C_mul_X, coeff_comp_C_mul_X, coeff_comp_C_mul_X] at h1
      linear_combination h1
    -- everything outside `{2, 4}` dies
    have hvanish : ∀ n : ℕ, n ≠ 2 → n ≠ 4 → f.coeff n = 0 := by
      intro n h2 h4
      rcases Nat.even_or_odd n with he | ho
      · have hb : ((3 : ℝ) ^ n + 5 ^ n + (-8 : ℝ) ^ n - 2 * 7 ^ n) ≠ 0 := by
          rw [he.neg_pow]
          rcases Nat.lt_or_ge n 6 with hlt | hge
          · obtain ⟨j, hj⟩ := he
            have hn0 : n = 0 := by omega
            subst hn0
            norm_num
          · have h8 : (2 : ℝ) * 7 ^ n < 8 ^ n := by
              have := two_mul_seven_pow_lt n hge
              exact_mod_cast this
            have h3 : (0 : ℝ) < 3 ^ n := by positivity
            have h5 : (0 : ℝ) < 5 ^ n := by positivity
            intro hcon
            linarith
        exact (mul_eq_zero.1 (hcoeff n)).resolve_right hb
      · exact hodd n ho
    refine ⟨f.coeff 4, f.coeff 2, ?_⟩
    ext n
    by_cases h4 : n = 4
    · subst h4; simp
    by_cases h2 : n = 2
    · subst h2; simp
    · simp [hvanish n h2 h4, h2, h4]
  · rintro ⟨p, q, rfl⟩ a b c hab
    simp only [eval_add, eval_mul, eval_pow, eval_C, eval_X]
    linear_combination
      (-6 * (p * (2 * (a ^ 2 + b ^ 2 + c ^ 2) + (a * b + b * c + c * a)) + q)) * hab

end Imo2004P2
