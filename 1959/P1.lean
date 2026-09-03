import Mathlib

/-- IMO 1959 Problem 1: the fraction `(21n+4)/(14n+3)` is irreducible for every
natural number `n`, i.e. its numerator and denominator are coprime.

The hypothesis `0 < n` is part of the original statement; it turned out to be
unnecessary, as the result holds for every natural number `n`. -/
theorem imo_1959_p1 (n : ℕ) (_h₀ : 0 < n) : Nat.gcd (21 * n + 4) (14 * n + 3) = 1 := by
  have h1 : Nat.gcd (21 * n + 4) (14 * n + 3) ∣ 3 * (14 * n + 3) :=
    Dvd.dvd.mul_left (Nat.gcd_dvd_right _ _) 3
  have h2 : Nat.gcd (21 * n + 4) (14 * n + 3) ∣ 2 * (21 * n + 4) :=
    Dvd.dvd.mul_left (Nat.gcd_dvd_left _ _) 2
  have h3 : Nat.gcd (21 * n + 4) (14 * n + 3) ∣ 1 := by
    have h4 := Nat.dvd_sub h1 h2
    have h5 : 3 * (14 * n + 3) - 2 * (21 * n + 4) = 1 := by omega
    rwa [h5] at h4
  exact Nat.dvd_one.mp h3
