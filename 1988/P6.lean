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
# IMO 1988, Problem 6

Let `a` and `b` be positive integers such that `a * b + 1` divides `a ^ 2 + b ^ 2`.
Show that `(a ^ 2 + b ^ 2) / (a * b + 1)` is the square of an integer.

The proof is the classical "Vieta jumping" descent argument.
-/

namespace Imo1988Q6

/-- The descent step, stated over `ℤ`: if `a ≥ b ≥ 0` and `a ^ 2 + b ^ 2 = k * (a * b + 1)`,
then `k` is a square.  The induction is on a natural number bounding `a + b`. -/
theorem vieta_descent (n : ℕ) :
    ∀ a b k : ℤ, 0 ≤ b → b ≤ a → a + b ≤ (n : ℤ) → a ^ 2 + b ^ 2 = k * (a * b + 1) →
      ∃ m : ℤ, k = m ^ 2 := by
  induction n with
  | zero =>
      intro a b k hb hba hsum heq
      have ha : a = 0 := by omega
      have hb0 : b = 0 := by omega
      subst ha; subst hb0
      exact ⟨0, by linarith [heq]⟩
  | succ n ih =>
      intro a b k hb hba hsum heq
      rcases eq_or_lt_of_le hb with hb0 | hb1
      · -- `b = 0`, so `k = a ^ 2`
        refine ⟨a, ?_⟩
        rw [← hb0] at heq
        simpa using heq.symm
      · -- `b ≥ 1`; jump to the pair `(b, k * b - a)`
        have ha1 : 1 ≤ a := le_trans hb1 hba
        have hab : 0 < a * b + 1 := by nlinarith
        have hk : 0 < k := by
          by_contra hcon
          push_neg at hcon
          nlinarith [mul_le_mul_of_nonneg_right hcon hab.le]
        set c : ℤ := k * b - a with hc
        have hceq : c ^ 2 + b ^ 2 = k * (c * b + 1) := by
          simp only [hc]; linear_combination heq
        have hc0 : 0 ≤ c := by nlinarith [sq_nonneg c, sq_nonneg b]
        have hprod : c * a = b ^ 2 - k := by simp only [hc]; nlinarith [heq]
        have hcb : c < b := by nlinarith
        exact ih b c k hc0 (le_of_lt hcb) (by omega) (by linarith [hceq])

/-- **IMO 1988, Problem 6.**  If `a` and `b` are positive integers with `a * b + 1` dividing
`a ^ 2 + b ^ 2`, then the quotient `(a ^ 2 + b ^ 2) / (a * b + 1)` is a perfect square.

The positivity hypotheses `ha`, `hb` are part of the problem statement; the descent argument
actually works for all natural numbers `a`, `b`. -/
theorem imo1988_q6 (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hdvd : a * b + 1 ∣ a ^ 2 + b ^ 2) :
    ∃ k : ℕ, a ^ 2 + b ^ 2 = k ^ 2 * (a * b + 1) := by
  obtain ⟨q, hq⟩ := hdvd
  -- move to `ℤ`
  have hqZ : (a : ℤ) ^ 2 + (b : ℤ) ^ 2 = (q : ℤ) * ((a : ℤ) * (b : ℤ) + 1) := by
    have : ((a ^ 2 + b ^ 2 : ℕ) : ℤ) = (((a * b + 1) * q : ℕ) : ℤ) := by rw [hq]
    push_cast at this
    linarith
  have key : ∀ x y : ℤ, 0 ≤ y → y ≤ x → x ^ 2 + y ^ 2 = (q : ℤ) * (x * y + 1) →
      ∃ m : ℤ, (q : ℤ) = m ^ 2 := by
    intro x y hy hyx h
    exact vieta_descent (x + y).toNat x y q hy hyx (by omega) h
  have hex : ∃ m : ℤ, (q : ℤ) = m ^ 2 := by
    rcases le_total (b : ℤ) (a : ℤ) with h | h
    · exact key a b (by positivity) h hqZ
    · exact key b a (by positivity) h (by linarith [hqZ])
  obtain ⟨m, hm⟩ := hex
  refine ⟨m.natAbs, ?_⟩
  have : (q : ℤ) = (m.natAbs : ℤ) ^ 2 := by
    rw [hm]; exact (Int.natAbs_pow_two m).symm
  have hqnat : q = m.natAbs ^ 2 := by exact_mod_cast this
  rw [hq, hqnat]; ring

/-- Restatement in terms of the actual quotient: `(a ^ 2 + b ^ 2) / (a * b + 1)` (a natural
number division, which is exact here) is a square. -/
theorem imo1988_q6' (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hdvd : a * b + 1 ∣ a ^ 2 + b ^ 2) :
    IsSquare ((a ^ 2 + b ^ 2) / (a * b + 1)) := by
  obtain ⟨k, hk⟩ := imo1988_q6 a b ha hb hdvd
  refine ⟨k, ?_⟩
  rw [hk, Nat.mul_div_cancel _ (Nat.succ_pos _)]
  ring

end Imo1988Q6
