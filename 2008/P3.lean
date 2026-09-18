import Mathlib

/-!
# IMO 2008, Problem 3

There are infinitely many positive integers `n` such that `n² + 1` has a prime divisor greater
than `2n + √(2n)`.

## Proof

This is Solution 2, which is much shorter to formalize than Solution 1 (whose Gaussian-integer
argument needs the `ad + bc = 1` reduction, a case split on `c = ±a/2`, and an asymptotic
"for large enough `p`" step).

Fix a prime `p ≡ 1 (mod 4)` with `p > 20`. Since `-1` is a square mod `p`, there is `x < p` with
`p ∣ x² + 1`; replacing `x` by `p - x` if necessary, we get `n` with `0 < n`, `2n < p` and
`p ∣ n² + 1`. Put `k = p - 2n ≥ 1`. Then modulo `p`,

  `k² + 4 ≡ (-2n)² + 4 = 4(n² + 1) ≡ 0`,

so `p ∣ k² + 4`, hence `p ≤ k² + 4`. With `p > 20` this forces `k > 4`, and then

  `2n = p - k ≤ k² + 4 - k < k²`,

so `√(2n) < k` and therefore `2n + √(2n) < 2n + k = p`.

Finally `p ∣ n² + 1` gives `p ≤ n² + 1`, so choosing `p` large forces `n` large: the set is
unbounded, hence infinite.
-/

namespace Imo2008P3

/-- For a prime `p ≡ 1 (mod 4)` with `p > 20`, some `n` with `p ∣ n² + 1` beats the bound. -/
theorem key (p : ℕ) (hp : p.Prime) (hp4 : p % 4 = 1) (hp20 : 20 < p) :
    ∃ n : ℕ, 0 < n ∧ p ∣ n ^ 2 + 1 ∧ (2 * (n : ℝ) + Real.sqrt (2 * (n : ℝ)) < p) := by
  haveI : Fact p.Prime := ⟨hp⟩
  -- a square root of `-1` modulo `p`
  obtain ⟨y, hy⟩ : IsSquare (-1 : ZMod p) := ZMod.exists_sq_eq_neg_one_iff.2 (by omega)
  have hcast : ((y.val : ℕ) : ZMod p) = y := by simp
  obtain ⟨x, hxlt, hxdvd⟩ : ∃ x : ℕ, x < p ∧ p ∣ x ^ 2 + 1 := by
    refine ⟨y.val, ZMod.val_lt y, ?_⟩
    refine (ZMod.natCast_eq_zero_iff _ _).1 ?_
    push_cast
    rw [hcast]
    linear_combination -hy
  have hx0 : x ≠ 0 := by
    intro h0
    rw [h0] at hxdvd
    norm_num at hxdvd
    omega
  -- fold into the range `2n < p`
  obtain ⟨n, hn0, hn2p, hndvd⟩ : ∃ n, 0 < n ∧ 2 * n < p ∧ p ∣ n ^ 2 + 1 := by
    rcases Nat.lt_or_ge (2 * x) p with hlt | hge
    · exact ⟨x, by omega, hlt, hxdvd⟩
    · refine ⟨p - x, by omega, by omega, ?_⟩
      refine (ZMod.natCast_eq_zero_iff _ _).1 ?_
      have hxp : x ≤ p := le_of_lt hxlt
      have hx : (((x : ℕ) ^ 2 + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hxdvd
      push_cast at hx ⊢
      rw [Nat.cast_sub hxp, ZMod.natCast_self]
      linear_combination hx
  -- `k = p - 2n`
  obtain ⟨k, hk⟩ : ∃ k, p = 2 * n + k := ⟨p - 2 * n, by omega⟩
  have hkdvd : p ∣ k ^ 2 + 4 := by
    refine (ZMod.natCast_eq_zero_iff _ _).1 ?_
    have hkk : ((k : ℕ) : ZMod p) = -(2 * (n : ZMod p)) := by
      have h0 : (((2 * n + k : ℕ)) : ZMod p) = 0 := by rw [← hk]; exact ZMod.natCast_self p
      push_cast at h0
      linear_combination h0
    have hn : (((n : ℕ) ^ 2 + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hndvd
    push_cast at hn ⊢
    rw [hkk]
    linear_combination 4 * hn
  have hkge : p ≤ k ^ 2 + 4 := Nat.le_of_dvd (by positivity) hkdvd
  have hk4 : 4 < k := by nlinarith
  have h2nk : 2 * n < k ^ 2 := by omega
  refine ⟨n, hn0, hndvd, ?_⟩
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hlt : 2 * (n : ℝ) < (k : ℝ) ^ 2 := by exact_mod_cast h2nk
  have hsq : Real.sqrt (2 * (n : ℝ)) < (k : ℝ) := (Real.sqrt_lt' hkR).2 hlt
  have hpR : (p : ℝ) = 2 * (n : ℝ) + (k : ℝ) := by exact_mod_cast hk
  rw [hpR]
  linarith

/-- **IMO 2008 P3.** -/
theorem imo2008_p3 :
    {n : ℕ | 0 < n ∧ ∃ p : ℕ, p.Prime ∧ p ∣ n ^ 2 + 1 ∧
      (2 * (n : ℝ) + Real.sqrt (2 * (n : ℝ)) < p)}.Infinite := by
  intro hfin
  obtain ⟨N, hN⟩ := hfin.bddAbove
  obtain ⟨p, hp, hpgt, hpmod⟩ :=
    Nat.exists_prime_gt_modEq_one (k := 4) (max 20 (N ^ 2 + 1)) (by norm_num)
  have hp4 : p % 4 = 1 := by
    have h := hpmod
    unfold Nat.ModEq at h
    omega
  have hp20 : 20 < p := lt_of_le_of_lt (le_max_left _ _) hpgt
  obtain ⟨n, hn0, hndvd, hreal⟩ := key p hp hp4 hp20
  have hmem : n ∈ {n : ℕ | 0 < n ∧ ∃ p : ℕ, p.Prime ∧ p ∣ n ^ 2 + 1 ∧
      (2 * (n : ℝ) + Real.sqrt (2 * (n : ℝ)) < p)} := ⟨hn0, p, hp, hndvd, hreal⟩
  have hnN : n ≤ N := hN hmem
  have h1 : p ≤ n ^ 2 + 1 := Nat.le_of_dvd (by positivity) hndvd
  have h2 : N ^ 2 + 1 < p := lt_of_le_of_lt (le_max_right _ _) hpgt
  nlinarith

end Imo2008P3
