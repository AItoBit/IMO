import Mathlib

/-!
# IMO 1989, Problem 5

Prove that for each positive integer `n` there exist `n` consecutive positive integers none of
which is an integral power of a prime number.

## Proof

This is the  idea, with `((n+1)!)²` in place of `(2n+3)!` (the square makes the
divisibility `k² ∣ N` immediate).

Put `N = ((n+1)!)²` and take the block `N + 2, N + 3, …, N + (n+1)`.
For `2 ≤ k ≤ n+1` we have `k ∣ (n+1)!`, say `(n+1)! = k·d`, hence

  `N + k = k²d² + k = k·(k d² + 1)`.

Any prime `p ∣ k` and any prime `q ∣ k d² + 1` both divide `N + k`, and `p ≠ q` because a common
prime would divide `1`. Two distinct prime divisors mean `N + k` is not a prime power.
-/

namespace Imo1989P5

/-- A number with two distinct prime divisors is not a prime power. -/
theorem not_isPrimePow_of_two_primes {x p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hpd : p ∣ x) (hqd : q ∣ x) : ¬ IsPrimePow x := by
  rintro ⟨r, k, hr, hk, hrk⟩
  have hrp : r.Prime := Nat.prime_iff.2 hr
  have h1 : p ∣ r ^ k := by rw [hrk]; exact hpd
  have h2 : q ∣ r ^ k := by rw [hrk]; exact hqd
  have hp' : p = r := (Nat.prime_dvd_prime_iff_eq hp hrp).1 (hp.dvd_of_dvd_pow h1)
  have hq' : q = r := (Nat.prime_dvd_prime_iff_eq hq hrp).1 (hq.dvd_of_dvd_pow h2)
  exact hpq (hp'.trans hq'.symm)

/-- **IMO 1989 P5.** -/
theorem imo1989_p5 (n : ℕ) (hn : 0 < n) :
    ∃ m : ℕ, 0 < m ∧ ∀ i < n, ¬ IsPrimePow (m + i) := by
  refine ⟨(Nat.factorial (n + 1)) ^ 2 + 2, by positivity, ?_⟩
  intro i hi
  -- `k = 2 + i` divides `(n+1)!`
  obtain ⟨d, hd⟩ : (2 + i) ∣ Nat.factorial (n + 1) :=
    Nat.dvd_factorial (by omega) (by omega)
  have hd0 : 0 < d := by
    rcases Nat.eq_zero_or_pos d with rfl | h
    · rw [mul_zero] at hd
      exact absurd hd (Nat.factorial_pos (n + 1)).ne'
    · exact h
  -- the factorisation `N + k = k (k d² + 1)`
  have hfac : (Nat.factorial (n + 1)) ^ 2 + 2 + i = (2 + i) * ((2 + i) * d ^ 2 + 1) := by
    rw [hd]; ring
  -- the two prime factors
  have hkne : (2 + i) ≠ 1 := by omega
  have hcne : (2 + i) * d ^ 2 + 1 ≠ 1 := by
    have h1 : 0 < (2 + i) * d ^ 2 := Nat.mul_pos (by omega) (pow_pos hd0 2)
    omega
  have hpp : ((2 + i).minFac).Prime := Nat.minFac_prime hkne
  have hqp : (((2 + i) * d ^ 2 + 1).minFac).Prime := Nat.minFac_prime hcne
  have hne : (2 + i).minFac ≠ ((2 + i) * d ^ 2 + 1).minFac := by
    intro h
    have h1 : ((2 + i) * d ^ 2 + 1).minFac ∣ (2 + i) := h ▸ Nat.minFac_dvd (2 + i)
    have h2 : ((2 + i) * d ^ 2 + 1).minFac ∣ (2 + i) * d ^ 2 + 1 := Nat.minFac_dvd _
    have h3 : ((2 + i) * d ^ 2 + 1).minFac ∣ (2 + i) * d ^ 2 := h1.mul_right _
    exact hqp.ne_one (Nat.dvd_one.mp ((Nat.dvd_add_right h3).mp h2))
  refine not_isPrimePow_of_two_primes hpp hqp hne ?_ ?_
  · rw [hfac]; exact (Nat.minFac_dvd _).mul_right _
  · rw [hfac]; exact (Nat.minFac_dvd _).mul_left _

end Imo1989P5
