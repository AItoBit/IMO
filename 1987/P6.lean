import Mathlib

/-!
# IMO 1987, Problem 6

Let `n ≥ 2`. If `k² + k + n` is prime for all `0 ≤ k ≤ √(n/3)`, then `k² + k + n` is prime
for all `0 ≤ k ≤ n - 2`.

Proof (strong induction on `k`; this is the classical argument, a streamlined form of the
AoPS solution). Write `f k = k² + k + n`. Take `y ≤ n - 2` with `f x` prime for all `x < y`,
and suppose `f y` is not prime. Let `p = minFac (f y)`, so `p² ≤ f y`.

* If `p ≤ 2y`, there is `x < y` with `p ∣ f x`, because `f y - f x = (y - x)(y + x + 1)`:
  take `x = y - p` if `p ≤ y`, and `x = p - y - 1` if `y < p`.
  Then `p = f x ≥ n` (both prime), so `n² ≤ p² ≤ f y ≤ f (n - 2) < n²`. Contradiction.
* So `p ≥ 2y + 1`, hence `(2y + 1)² ≤ f y`, i.e. `3y² + 3y + 1 ≤ n`.
  Then `y ≤ √(n/3)`, so `f y` is prime by hypothesis. Contradiction.
-/

namespace Imo1987P6

theorem imo1987_p6 (n : ℕ) (hn : 2 ≤ n)
    (h : ∀ k : ℕ, (k : ℝ) ≤ Real.sqrt (n / 3) → Nat.Prime (k ^ 2 + k + n)) :
    ∀ k : ℕ, k ≤ n - 2 → Nat.Prime (k ^ 2 + k + n) := by
  -- The hypothesis without square roots: `3 k² ≤ n`.
  have h' : ∀ k : ℕ, 3 * k ^ 2 ≤ n → Nat.Prime (k ^ 2 + k + n) := by
    intro k hk
    apply h
    have hsq : (k : ℝ) ^ 2 ≤ n / 3 := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 3)]
      exact_mod_cast (by linarith : k ^ 2 * 3 ≤ n)
    exact (le_abs_self _).trans (Real.abs_le_sqrt hsq)
  intro k
  refine Nat.strong_induction_on k ?_
  intro y ih hy
  by_contra hnp
  -- `p` : the least prime factor of `f y`.
  have hX1 : 1 < y ^ 2 + y + n := lt_of_lt_of_le (by omega) (Nat.le_add_left n _)
  have hp : (y ^ 2 + y + n).minFac.Prime := Nat.minFac_prime hX1.ne'
  have hpdvd : (y ^ 2 + y + n).minFac ∣ y ^ 2 + y + n := Nat.minFac_dvd _
  have hpsq : (y ^ 2 + y + n).minFac ^ 2 ≤ y ^ 2 + y + n :=
    Nat.minFac_sq_le_self (Nat.zero_lt_one.trans hX1) hnp
  obtain ⟨p, hpdef⟩ : ∃ p, p = (y ^ 2 + y + n).minFac := ⟨_, rfl⟩
  rw [← hpdef] at hp hpdvd hpsq
  -- Key step: `2 y < p`.
  have hbig : 2 * y < p := by
    by_contra hle
    push_neg at hle
    obtain ⟨x, hxy, hdiv⟩ : ∃ x, x < y ∧ p ∣ x ^ 2 + x + n := by
      rcases le_or_gt p y with h1 | h1
      · -- `x = y - p`
        obtain ⟨x, hx⟩ : ∃ x, y = x + p := ⟨y - p, by omega⟩
        have hp0 := hp.pos
        refine ⟨x, by omega, ?_⟩
        have heq : y ^ 2 + y + n = x ^ 2 + x + n + p * (2 * x + p + 1) := by
          rw [hx]
          ring
        rw [heq] at hpdvd
        exact (Nat.dvd_add_left (dvd_mul_right p _)).mp hpdvd
      · -- `x = p - y - 1`
        obtain ⟨x, hx⟩ : ∃ x, p = x + y + 1 := ⟨p - y - 1, by omega⟩
        obtain ⟨d, hd⟩ : ∃ d, y = x + d := ⟨y - x, by omega⟩
        refine ⟨x, by omega, ?_⟩
        have heq : y ^ 2 + y + n = x ^ 2 + x + n + d * p := by
          rw [hx, hd]
          ring
        rw [heq] at hpdvd
        exact (Nat.dvd_add_left (dvd_mul_left p d)).mp hpdvd
    have hfx : Nat.Prime (x ^ 2 + x + n) := ih x hxy (by omega)
    have hpeq : p = x ^ 2 + x + n := (Nat.prime_dvd_prime_iff_eq hp hfx).mp hdiv
    have hpn : n ≤ p := by
      rw [hpeq]
      exact Nat.le_add_left n _
    have hy2 : y + 2 ≤ n := by omega
    nlinarith [Nat.mul_le_mul hpn hpn, Nat.mul_le_mul hy2 (le_refl (n + y))]
  -- Hence `3 y² ≤ n`, so `f y` is prime by hypothesis.
  have h3 : 3 * y ^ 2 ≤ n := by
    have h2 : 2 * y + 1 ≤ p := hbig
    nlinarith [Nat.mul_le_mul h2 h2]
  exact hnp (h' y h3)

end Imo1987P6
