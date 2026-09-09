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

/-!
# IMO 1979, Problem 1

If `p` and `q` are natural numbers so that

`p / q = 1 - 1/2 + 1/3 - 1/4 + ... - 1/1318 + 1/1319`,

prove that `p` is divisible by `1979`.
-/

namespace IMO1979Q1

/-- The index set `{660, 661, ..., 1319}`. -/
def I : Finset ℕ := Finset.Icc 660 1319

/-- The product of all elements of `I`. -/
def D : ℤ := ∏ k ∈ I, (k : ℤ)

/-- `A = ∑_{k ∈ I} ∏_{m ∈ I, m ≠ k} m`, i.e. the numerator of `∑_{k ∈ I} 1/k`
over the common denominator `D`. -/
def A : ℤ := ∑ k ∈ I, ∏ m ∈ I.erase k, (m : ℤ)

/-- The alternating harmonic sum `1 - 1/2 + ... + 1/(2n+1)` equals `∑_{j<n+1} 1/(n+1+j)`. -/
theorem alt_harmonic_eq_shifted (n : ℕ) :
    ∑ i ∈ Finset.range (2 * n + 1), (-1 : ℚ) ^ i / (i + 1)
      = ∑ j ∈ Finset.range (n + 1), (1 : ℚ) / (n + 1 + j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : 2 * (n + 1) + 1 = 2 * n + 1 + 1 + 1 := by ring
    rw [h1, Finset.sum_range_succ, Finset.sum_range_succ, ih]
    have key : ∑ j ∈ Finset.range (n + 1 + 1), (1 : ℚ) / (n + 1 + 1 + j)
        = (∑ i ∈ Finset.range (n + 1 + 2), (1 : ℚ) / (n + 1 + i)) - (1 : ℚ) / (n + 1) := by
      have h := Finset.sum_range_succ' (fun i => (1 : ℚ) / (n + 1 + i)) (n + 2)
      push_cast at h ⊢
      rw [h]
      ring_nf
    have key2 : ∑ i ∈ Finset.range (n + 1 + 2), (1 : ℚ) / (n + 1 + i)
        = (∑ j ∈ Finset.range (n + 1), (1 : ℚ) / (n + 1 + j)) + 1 / (2 * n + 2)
          + 1 / (2 * n + 3) := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      push_cast
      ring_nf
    push_cast
    rw [key, key2]
    have h2 : ((-1 : ℚ)) ^ (2 * n + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
    have h3 : ((-1 : ℚ)) ^ (2 * n + 2) = 1 := by rw [pow_succ, pow_succ, pow_mul]; norm_num
    rw [h2, h3]
    have hn : (n : ℚ) + 1 ≠ 0 := by positivity
    have hn2 : (2 * (n : ℚ) + 2) ≠ 0 := by positivity
    have hn3 : (2 * (n : ℚ) + 3) ≠ 0 := by positivity
    field_simp
    ring

/-- The shifted sum is a sum over `Icc (n+1) (2n+1)`. -/
theorem shifted_eq_Icc_sum (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), (1 : ℚ) / (n + 1 + j)
      = ∑ k ∈ Finset.Icc (n + 1) (2 * n + 1), (1 : ℚ) / k := by
  refine (Finset.sum_nbij' (i := fun k => k - (n + 1)) (j := fun j => n + 1 + j)
    ?_ ?_ ?_ ?_ ?_).symm <;> intros <;> simp_all <;> omega

/-- The sum in the problem equals `∑_{k=660}^{1319} 1/k`. -/
theorem problem_sum_eq :
    ∑ i ∈ Finset.range 1319, (-1 : ℚ) ^ i / (i + 1) = ∑ k ∈ I, (1 : ℚ) / k := by
  have h : (1319 : ℕ) = 2 * 659 + 1 := by norm_num
  rw [h, alt_harmonic_eq_shifted 659, shifted_eq_Icc_sum 659]
  norm_num [I]

/-- Pairing `k` with `1979 - k` : the two corresponding terms of `A` sum to a
multiple of `1979`. -/
theorem pair_term (k : ℕ) (hk : k ∈ Finset.Ioc 659 989) :
    (∏ m ∈ I.erase k, (m : ℤ)) + (∏ m ∈ I.erase (1979 - k), (m : ℤ))
      = 1979 * ∏ m ∈ (I.erase k).erase (1979 - k), (m : ℤ) := by
  simp only [Finset.mem_Ioc] at hk
  have hkI : k ∈ I := by simp only [I, Finset.mem_Icc]; omega
  have hkI' : 1979 - k ∈ I := by simp only [I, Finset.mem_Icc]; omega
  have hne : 1979 - k ≠ k := by omega
  have h1 : 1979 - k ∈ I.erase k := Finset.mem_erase.2 ⟨hne, hkI'⟩
  have h2 : k ∈ I.erase (1979 - k) := Finset.mem_erase.2 ⟨fun h => hne h.symm, hkI⟩
  rw [← Finset.mul_prod_erase _ _ h1, ← Finset.mul_prod_erase _ _ h2,
    Finset.erase_right_comm (a := 1979 - k) (b := k)]
  have hcast : ((1979 - k : ℕ) : ℤ) = 1979 - (k : ℤ) := by
    have : (k : ℤ) ≤ 1979 := by exact_mod_cast (by omega : k ≤ 1979)
    push_cast [Nat.cast_sub (by omega : k ≤ 1979)]
    ring
  rw [hcast]
  ring

/-- `A` is divisible by `1979`. -/
theorem dvd_A : (1979 : ℤ) ∣ A := by
  have hsplit : A = (∑ k ∈ Finset.Ioc 659 989, ∏ m ∈ I.erase k, (m : ℤ))
      + ∑ k ∈ Finset.Ioc 989 1319, ∏ m ∈ I.erase k, (m : ℤ) := by
    rw [Finset.sum_Ioc_consecutive _ (by norm_num) (by norm_num)]
    rfl
  have hbij : (∑ k ∈ Finset.Ioc 989 1319, ∏ m ∈ I.erase k, (m : ℤ))
      = ∑ k ∈ Finset.Ioc 659 989, ∏ m ∈ I.erase (1979 - k), (m : ℤ) := by
    refine (Finset.sum_nbij' (i := fun k => 1979 - k) (j := fun k => 1979 - k)
      ?_ ?_ ?_ ?_ ?_)
    · intro a ha
      simp only [Finset.mem_Ioc] at ha ⊢
      omega
    · intro a ha
      simp only [Finset.mem_Ioc] at ha ⊢
      omega
    · intro a ha
      simp only [Finset.mem_Ioc] at ha
      omega
    · intro a ha
      simp only [Finset.mem_Ioc] at ha
      omega
    · intro a ha
      simp only [Finset.mem_Ioc] at ha
      have : 1979 - (1979 - a) = a := by omega
      simp only [this]
  rw [hsplit, hbij, ← Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl pair_term, ← Finset.mul_sum]
  exact Dvd.intro _ rfl

/-- `1979` does not divide `D`. -/
theorem not_dvd_D : ¬ (1979 : ℤ) ∣ D := by
  intro hdvd
  have hp : Prime (1979 : ℤ) := by
    rw [Int.prime_iff_natAbs_prime]
    norm_num
  rw [D, hp.dvd_finsetProd_iff] at hdvd
  obtain ⟨k, hk, hkd⟩ := hdvd
  simp only [I, Finset.mem_Icc] at hk
  have hk0 : (0 : ℤ) < (k : ℤ) := by exact_mod_cast (by omega : 0 < k)
  have := Int.le_of_dvd hk0 hkd
  have : (k : ℤ) ≤ 1319 := by exact_mod_cast hk.2
  omega

/-- `A` is the numerator of `∑_{k ∈ I} 1/k` over the common denominator `D`. -/
theorem A_eq : (A : ℚ) = (D : ℚ) * ∑ k ∈ I, (1 : ℚ) / k := by
  rw [A, Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl ?_
  intro k hk
  have hk0 : (k : ℚ) ≠ 0 := by
    simp only [I, Finset.mem_Icc] at hk
    have : k ≠ 0 := by omega
    exact_mod_cast this
  have hD : (D : ℚ) = (k : ℚ) * ∏ m ∈ I.erase k, (m : ℚ) := by
    rw [D]
    push_cast
    exact (Finset.mul_prod_erase _ _ hk).symm
  rw [hD]
  field_simp

/-- **IMO 1979, Problem 1.**  If `p / q = 1 - 1/2 + 1/3 - ... - 1/1318 + 1/1319`
for natural numbers `p, q` with `q ≠ 0`, then `1979 ∣ p`. -/
theorem imo1979_q1 (p q : ℕ) (hq : q ≠ 0)
    (h : (p : ℚ) / q = ∑ i ∈ Finset.range 1319, (-1 : ℚ) ^ i / (i + 1)) :
    1979 ∣ p := by
  have hq0 : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hq
  rw [problem_sum_eq, div_eq_iff hq0] at h
  -- `p * D = q * A` over the integers
  have hQ : ((p * D : ℤ) : ℚ) = ((q * A : ℤ) : ℚ) := by
    push_cast
    rw [A_eq, h]
    ring
  have hZ : (p : ℤ) * D = (q : ℤ) * A := by exact_mod_cast hQ
  have hp : Prime (1979 : ℤ) := by
    rw [Int.prime_iff_natAbs_prime]
    norm_num
  have hdvd : (1979 : ℤ) ∣ (p : ℤ) * D := by
    rw [hZ]
    exact Dvd.dvd.mul_left dvd_A _
  rcases hp.dvd_mul.1 hdvd with h1 | h2
  · exact_mod_cast h1
  · exact absurd h2 not_dvd_D

end IMO1979Q1
