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
# IMO 2007, Problem 5

Let `a` and `b` be positive integers. Show that if `4ab - 1` divides `(4a² - 1)²`,
then `a = b`.
-/

namespace Imo2007P5

/-- `4ab - 1` is coprime to `4a`, since `b * (4a) - (4ab - 1) = 1`. -/
lemma isCoprime_four_mul_self (a b : ℤ) : IsCoprime (4 * a * b - 1) (4 * a) :=
  ⟨-1, b, by ring⟩

/-- If `4ab - 1` divides `(4a² - 1)²`, then it divides `(a - b)²`. -/
lemma dvd_sq_sub_of_dvd {a b : ℤ} (h : (4 * a * b - 1) ∣ (4 * a ^ 2 - 1) ^ 2) :
    (4 * a * b - 1) ∣ (a - b) ^ 2 := by
  have hmul : (4 * a * b - 1) ∣ (4 * a) ^ 2 * (a - b) ^ 2 := by
    have hid : (4 * a) ^ 2 * (a - b) ^ 2
        = (4 * a ^ 2 - 1) ^ 2 - (4 * a * b - 1) * (8 * a ^ 2 - 4 * a * b - 1) := by ring
    rw [hid]
    exact dvd_sub h (Dvd.intro _ rfl)
  exact ((isCoprime_four_mul_self a b).pow_right (n := 2)).dvd_of_dvd_mul_left hmul

/-- Vieta jumping: there is no pair of positive integers `b < a` with `4ab - 1 ∣ (a - b)²`.
Proved by strong induction on `a + b`. -/
lemma not_dvd_sq_sub_of_lt :
    ∀ n : ℕ, ∀ a b : ℤ, 0 < a → 0 < b → b < a → (a + b).toNat = n →
      ¬ ((4 * a * b - 1) ∣ (a - b) ^ 2) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rintro a b ha hb hba rfl ⟨k, hk⟩
    have hab : 1 ≤ a * b := by nlinarith
    have hpos : 0 < 4 * a * b - 1 := by nlinarith
    have hk0 : 0 < k := by nlinarith
    set a' : ℤ := 2 * b + 4 * k * b - a with ha'def
    have hprod : a * a' = b ^ 2 + k := by rw [ha'def]; linear_combination -hk
    have hsum : a + a' = 2 * b + 4 * k * b := by rw [ha'def]; ring
    have ha'pos : 0 < a' := by nlinarith
    have hklt : k < a ^ 2 - b ^ 2 := by nlinarith
    have ha'lt : a' < a := by nlinarith
    have ha'dvd : (4 * a' * b - 1) ∣ (a' - b) ^ 2 := ⟨k, by linear_combination b * hsum - hprod⟩
    have hsumlt : (a' + b).toNat < (a + b).toNat := by
      have h1 : (0 : ℤ) < a' + b := by linarith
      have h2 : a' + b < a + b := by linarith
      omega
    rcases lt_trichotomy b a' with h | h | h
    · exact ih _ hsumlt a' b ha'pos hb h rfl ha'dvd
    · -- `a' = b` forces `k = 0`, contradicting `0 < k`
      obtain ⟨k', hk'⟩ := ha'dvd
      rw [← h] at hk'
      simp at hk'
      nlinarith
    · refine ih (b + a').toNat ?_ b a' hb ha'pos h rfl ?_
      · omega
      · rcases ha'dvd with ⟨c, hc⟩
        exact ⟨c, by linear_combination hc⟩

/-- The symmetric form: for positive integers `a`, `b`, if `4ab - 1` divides `(a - b)²`
then `a = b`. -/
lemma eq_of_dvd_sq_sub {a b : ℤ} (ha : 0 < a) (hb : 0 < b)
    (h : (4 * a * b - 1) ∣ (a - b) ^ 2) : a = b := by
  rcases lt_trichotomy b a with hba | hba | hba
  · exact absurd h (not_dvd_sq_sub_of_lt _ a b ha hb hba rfl)
  · exact hba.symm
  · refine absurd ?_ (not_dvd_sq_sub_of_lt (b + a).toNat b a hb ha hba rfl)
    obtain ⟨c, hc⟩ := h
    exact ⟨c, by linear_combination hc⟩

/-- **IMO 2007, Problem 5.** For positive integers `a`, `b`, if `4ab - 1` divides `(4a² - 1)²`
then `a = b`. -/
theorem imo2007_p5 (a b : ℤ) (ha : 0 < a) (hb : 0 < b)
    (h : (4 * a * b - 1) ∣ (4 * a ^ 2 - 1) ^ 2) : a = b :=
  eq_of_dvd_sq_sub ha hb (dvd_sq_sub_of_dvd h)

end Imo2007P5
