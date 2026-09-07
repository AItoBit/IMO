/-
# IMO 1972, Problem 3

Prove that `(2m)! (2n)! / (m! n! (m+n)!)` is an integer for all `m, n ≥ 0`.

Stated as a divisibility in `ℕ`:

  `m ! * n ! * (m + n)! ∣ (2*m)! * (2*n)!`.

## Proof

Following the AoPS solution, with `f m n = (2m)!(2n)! / (m! n! (m+n)!)`:

  `f m (n+1) = 4 * f m n - f (m+1) n`,

and `f m 0 = (2m)! / (m!)² = C(2m, m)` is an integer.  Induction on `n`
(quantified over all `m`, since the step uses `f (m+1) n`) does the rest.

Because of the subtraction, the induction is carried out over `ℚ`: the statement
proved by induction is that `(2m)!(2n)!` equals an *integer* multiple of
`m! n! (m+n)!` in `ℚ`.  The two auxiliary facts driving the step, after clearing
the factorials, are

  `(2m+2)(2m+1) * (2m)!(2n)!  =  b * (m+1) m! n! (m+n+1) (m+n)!`   (from `f (m+1) n`)
  `(2m)!(2n)!                 =  a * m! n! (m+n)!`                  (from `f m n`)

which cancel down to the key identity `2(2m+1) a = b (m+n+1)`; the target for
`n+1` is then a linear combination of that identity and the one for `n`.
-/

import Mathlib

open Nat

namespace Imo1972P3

/-! ### Factorial expansions -/

private lemma fact_two_succ (k : ℕ) :
    (2 * (k + 1))! = (2 * k + 2) * ((2 * k + 1) * (2 * k)!) := by
  have h : 2 * (k + 1) = (2 * k + 1) + 1 := by ring
  rw [h, Nat.factorial_succ, Nat.factorial_succ]

private lemma fact_add_succ (m n : ℕ) : (m + (n + 1))! = (m + n + 1) * (m + n)! := by
  have h : m + (n + 1) = (m + n) + 1 := by ring
  rw [h, Nat.factorial_succ]

private lemma fact_succ_add (m n : ℕ) : (m + 1 + n)! = (m + n + 1) * (m + n)! := by
  have h : m + 1 + n = (m + n) + 1 := by ring
  rw [h, Nat.factorial_succ]

/-! ### The induction -/

private lemma key : ∀ n m : ℕ, ∃ a : ℤ,
    ((2 * m)! : ℚ) * ((2 * n)! : ℚ)
      = (a : ℚ) * ((m ! : ℚ) * (n ! : ℚ) * ((m + n)! : ℚ)) := by
  intro n
  induction n with
  | zero =>
    intro m
    refine ⟨((2 * m).choose m : ℤ), ?_⟩
    have h := Nat.choose_mul_factorial_mul_factorial (show m ≤ 2 * m by omega)
    rw [show 2 * m - m = m by omega] at h
    have h2 : ((2 * m)! : ℚ) = ((2 * m).choose m : ℚ) * (m ! : ℚ) * (m ! : ℚ) := by
      exact_mod_cast h.symm
    simp only [Nat.mul_zero, Nat.factorial_zero, Nat.add_zero]
    push_cast
    rw [h2]
    ring
  | succ n ih =>
    intro m
    obtain ⟨a, ha⟩ := ih m
    obtain ⟨b, hb⟩ := ih (m + 1)
    -- clear the factorials in the `(m+1, n)` instance
    rw [fact_two_succ m, fact_succ_add m n, Nat.factorial_succ m] at hb
    push_cast at hb
    -- nonvanishing of the denominators
    have hM : ((m ! : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
    have hN : ((n ! : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    have hK : (((m + n)! : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (m + n))
    have hm1 : ((m : ℚ) + 1) ≠ 0 := by positivity
    have hc : (((m : ℚ) + 1) * ((m ! : ℚ) * (n ! : ℚ) * ((m + n)! : ℚ))) ≠ 0 :=
      mul_ne_zero hm1 (mul_ne_zero (mul_ne_zero hM hN) hK)
    -- the key identity `2 (2m+1) a = b (m+n+1)`
    have hkey : 2 * (2 * (m : ℚ) + 1) * (a : ℚ) = (b : ℚ) * ((m : ℚ) + (n : ℚ) + 1) := by
      apply mul_left_cancel₀ hc
      linear_combination hb - ((2 * (m : ℚ) + 2) * (2 * (m : ℚ) + 1)) * ha
    -- conclude for `n + 1`
    refine ⟨4 * a - b, ?_⟩
    rw [fact_two_succ n, fact_add_succ m n, Nat.factorial_succ n]
    push_cast
    linear_combination ((2 * (n : ℚ) + 2) * (2 * (n : ℚ) + 1)) * ha
      - ((m ! : ℚ) * (n ! : ℚ) * ((m + n)! : ℚ) * ((n : ℚ) + 1)) * hkey

/-! ### The theorem -/

/-- **IMO 1972, Problem 3.**  `(2m)! (2n)!` is divisible by `m! n! (m+n)!`, i.e.
`(2m)!(2n)! / (m! n! (m+n)!)` is an integer. -/
theorem imo1972_p3 (m n : ℕ) : (m ! * n ! * (m + n)!) ∣ ((2 * m)! * (2 * n)!) := by
  obtain ⟨a, ha⟩ := key n m
  rw [← Int.natCast_dvd_natCast]
  refine ⟨a, ?_⟩
  have h : (((2 * m)! * (2 * n)! : ℕ) : ℚ)
      = ((m ! * n ! * (m + n)! : ℕ) : ℚ) * (a : ℚ) := by
    push_cast
    linear_combination ha
  exact_mod_cast h

end Imo1972P3
