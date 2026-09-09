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

set_option grind.warning false

namespace Imo1981P3

/-- Every pair of positive naturals `(m, n)` with `(n² - mn - m²)² = 1` is a pair of
consecutive Fibonacci numbers. -/
theorem solutions_are_fib :
    ∀ N m n : ℕ, m + n ≤ N → 1 ≤ m → 1 ≤ n → ((n : ℤ) ^ 2 - m * n - m ^ 2) ^ 2 = 1 →
      ∃ k, m = Nat.fib k ∧ n = Nat.fib (k + 1) := by
  intro N
  induction N with
  | zero => intro m n hN hm _ _; omega
  | succ N ih =>
    intro m n hN hm hn h
    rcases lt_trichotomy m n with hmn | hmn | hmn
    · -- descend to `(n - m, m)`
      have hmn' : (((n - m : ℕ) : ℤ)) = (n : ℤ) - m := by
        push_cast [Nat.cast_sub hmn.le]; ring
      have h' : ((m : ℤ) ^ 2 - ((n - m : ℕ) : ℤ) * m - ((n - m : ℕ) : ℤ) ^ 2) ^ 2 = 1 := by
        rw [hmn']
        nlinarith [h]
      obtain ⟨k, hk1, hk2⟩ := ih (n - m) m (by omega) (by omega) hm h'
      refine ⟨k + 1, hk2, ?_⟩
      have hfib : Nat.fib (k + 1 + 1) = Nat.fib k + Nat.fib (k + 1) := Nat.fib_add_two
      omega
    · subst hmn
      have hm1 : m = 1 := by
        by_contra hne
        have h2 : 2 ≤ m := by omega
        have h2' : (2 : ℤ) ≤ (m : ℤ) := by exact_mod_cast h2
        have hm4 : (m : ℤ) ^ 4 = 1 := by linear_combination h
        nlinarith [hm4, h2', sq_nonneg ((m : ℤ) - 2)]
      subst hm1
      exact ⟨1, rfl, rfl⟩
    · exfalso
      have h1 : (1 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
      have h2 : (n : ℤ) + 1 ≤ (m : ℤ) := by exact_mod_cast hmn
      have hnm : (1 : ℤ) ≤ (m : ℤ) - n := by linarith
      have hprod : (1 : ℤ) ≤ (n : ℤ) * ((m : ℤ) - n) := by nlinarith
      have he : (n : ℤ) ^ 2 - m * n - m ^ 2 ≤ -2 := by nlinarith
      nlinarith [he, h]

theorem fib_index_le (k : ℕ) (h : Nat.fib (k + 1) ≤ 1981) : k ≤ 16 := by
  by_contra hk
  have h17 : 17 ≤ k := by omega
  have : Nat.fib 18 ≤ Nat.fib (k + 1) := Nat.fib_mono (by omega)
  have h18 : Nat.fib 18 = 2584 := by decide
  omega

/-- **IMO 1981, Problem 3.** The maximum value of `m² + n²` for integers
`m, n ∈ {1, 2, …, 1981}` satisfying `(n² - mn - m²)² = 1` is `3524578 = 987² + 1597²`. -/
theorem imo1981_p3 :
    IsGreatest {s : ℤ | ∃ m n : ℤ, 1 ≤ m ∧ m ≤ 1981 ∧ 1 ≤ n ∧ n ≤ 1981 ∧
      (n ^ 2 - m * n - m ^ 2) ^ 2 = 1 ∧ s = m ^ 2 + n ^ 2} 3524578 := by
  constructor
  · exact ⟨987, 1597, by norm_num⟩
  · rintro s ⟨m, n, hm1, hm2, hn1, hn2, hmn, rfl⟩
    lift m to ℕ using (by linarith : (0 : ℤ) ≤ m) with M
    lift n to ℕ using (by linarith : (0 : ℤ) ≤ n) with N
    have hM1 : 1 ≤ M := by exact_mod_cast hm1
    have hN1 : 1 ≤ N := by exact_mod_cast hn1
    have hN2 : N ≤ 1981 := by exact_mod_cast hn2
    obtain ⟨k, hk1, hk2⟩ := solutions_are_fib (M + N) M N le_rfl hM1 hN1 hmn
    have hk : k ≤ 16 := fib_index_le k (by omega)
    have hb1 : Nat.fib k ≤ 987 := by
      have := Nat.fib_mono (show k ≤ 16 from hk)
      have h16 : Nat.fib 16 = 987 := by decide
      omega
    have hb2 : Nat.fib (k + 1) ≤ 1597 := by
      have := Nat.fib_mono (show k + 1 ≤ 17 by omega)
      have h17 : Nat.fib 17 = 1597 := by decide
      omega
    have hM : M ≤ 987 := by omega
    have hN : N ≤ 1597 := by omega
    have hM' : (M : ℤ) ≤ 987 := by exact_mod_cast hM
    have hN' : (N : ℤ) ≤ 1597 := by exact_mod_cast hN
    have hM0 : (0 : ℤ) ≤ (M : ℤ) := Int.natCast_nonneg M
    have hN0 : (0 : ℤ) ≤ (N : ℤ) := Int.natCast_nonneg N
    nlinarith [hM', hN', hM0, hN0]

end Imo1981P3
