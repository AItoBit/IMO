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
# IMO 2000 Problem 5

Does there exist a positive integer `n` such that `n` has exactly 2000 prime divisors
and `n` divides `2 ^ n + 1`?  The answer is **yes**.

We prove the more general statement that for every `k` there is a positive integer `n`
divisible by `3`, with exactly `k + 1` distinct prime divisors, such that `n ∣ 2 ^ n + 1`.
-/

namespace Imo2000P5

/-- For odd `t`, `x + 1` divides `x ^ t + 1` (over the naturals). -/
theorem nat_add_one_dvd_pow_add_one (x t : ℕ) (ht : Odd t) : x + 1 ∣ x ^ t + 1 := by
  have h : ((x : ℤ) + 1) ∣ (x : ℤ) ^ t + 1 ^ t := Odd.add_dvd_pow_add_pow (x : ℤ) 1 ht
  simp only [one_pow] at h
  exact_mod_cast h

/-- If `m ∣ 2 ^ m + 1` and `t` is odd, then `2 ^ m + 1 ∣ 2 ^ (m * t) + 1`. -/
theorem pow_add_one_dvd_pow_mul_add_one (m t : ℕ) (ht : Odd t) :
    2 ^ m + 1 ∣ 2 ^ (m * t) + 1 := by
  have := nat_add_one_dvd_pow_add_one (2 ^ m) t ht
  rwa [← pow_mul] at this

/-- The factorisation `A ^ 3 + 1 = (A + 1) * (A * (A - 1) + 1)` over the naturals. -/
theorem cube_add_one_factor (A : ℕ) (hA : 1 ≤ A) :
    A ^ 3 + 1 = (A + 1) * (A * (A - 1) + 1) := by
  obtain ⟨B, rfl⟩ : ∃ B, A = B + 1 := ⟨A - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  ring

/-- A number dividing `2 ^ n + 1` is odd. -/
theorem odd_of_dvd_two_pow_add_one {n : ℕ} (h : n ∣ 2 ^ n + 1) (hn : 0 < n) : Odd n := by
  rcases Nat.even_or_odd n with he | ho
  · exfalso
    have h2 : 2 ∣ n := he.two_dvd
    have : (2 : ℕ) ∣ 2 ^ n + 1 := h2.trans h
    have h2n : (2 : ℕ) ∣ 2 ^ n := dvd_pow_self 2 hn.ne'
    omega
  · exact ho

/-- If `n` is odd and `n ≥ 3`, then `2 ^ n = 3 * d + 2` for some `d ≥ 2`. -/
theorem exists_repr {n : ℕ} (hodd : Odd n) (hn : 3 ≤ n) : ∃ d, 2 ≤ d ∧ 2 ^ n = 3 * d + 2 := by
  have h3 : (3 : ℕ) ∣ 2 ^ n + 1 := by
    have := nat_add_one_dvd_pow_add_one 2 n hodd
    norm_num at this ⊢
    exact this
  have h8 : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨c, hc⟩ := h3
  refine ⟨c - 1, by omega, by omega⟩

/-- With `2 ^ n = 3 * d + 2`, the second factor of `2 ^ (3 * n) + 1` equals `3 * q`
with `q = 3 * d ^ 2 + 3 * d + 1`. -/
theorem second_factor_eq {n d : ℕ} (hd : 2 ^ n = 3 * d + 2) :
    2 ^ n * (2 ^ n - 1) + 1 = 3 * (3 * d ^ 2 + 3 * d + 1) := by
  rw [hd]
  have : 3 * d + 2 - 1 = 3 * d + 1 := by omega
  rw [this]
  ring

/-- The basic factorisation `2 ^ (3 * n) + 1 = (2 ^ n + 1) * (2 ^ n * (2 ^ n - 1) + 1)`. -/
theorem two_pow_three_mul_factor (n : ℕ) :
    2 ^ (3 * n) + 1 = (2 ^ n + 1) * (2 ^ n * (2 ^ n - 1) + 1) := by
  have h : (2 : ℕ) ^ (3 * n) = (2 ^ n) ^ 3 := by
    rw [← pow_mul, mul_comm]
  rw [h]
  exact cube_add_one_factor (2 ^ n) (Nat.one_le_two_pow)

/-- If `3 ∣ n`, `0 < n` and `n ∣ 2 ^ n + 1`, then `3 * n ∣ 2 ^ (3 * n) + 1`. -/
theorem three_mul_dvd {n : ℕ} (h3 : 3 ∣ n) (hn : 0 < n) (hdvd : n ∣ 2 ^ n + 1) :
    3 * n ∣ 2 ^ (3 * n) + 1 := by
  have hodd : Odd n := odd_of_dvd_two_pow_add_one hdvd hn
  have hn3 : 3 ≤ n := Nat.le_of_dvd hn h3
  obtain ⟨d, -, hd⟩ := exists_repr hodd hn3
  have hq : 2 ^ n * (2 ^ n - 1) + 1 = 3 * (3 * d ^ 2 + 3 * d + 1) := second_factor_eq hd
  have h1 : n * 3 ∣ (2 ^ n + 1) * (2 ^ n * (2 ^ n - 1) + 1) :=
    mul_dvd_mul hdvd ⟨3 * d ^ 2 + 3 * d + 1, hq⟩
  rw [two_pow_three_mul_factor n]
  rwa [mul_comm 3 n]

/-- Key step: if `3 ∣ n`, `0 < n` and `n ∣ 2 ^ n + 1`, then there is a prime `p` with
`p ∣ 2 ^ (3 * n) + 1` and `p ∤ 2 ^ n + 1`. -/
theorem exists_new_prime {n : ℕ} (h3 : 3 ∣ n) (hn : 0 < n) (hdvd : n ∣ 2 ^ n + 1) :
    ∃ p : ℕ, p.Prime ∧ p ∣ 2 ^ (3 * n) + 1 ∧ ¬ p ∣ 2 ^ n + 1 := by
  have hodd : Odd n := odd_of_dvd_two_pow_add_one hdvd hn
  have hn3 : 3 ≤ n := Nat.le_of_dvd hn h3
  obtain ⟨d, hd2, hd⟩ := exists_repr hodd hn3
  set q : ℕ := 3 * d ^ 2 + 3 * d + 1 with hqdef
  have hq1 : q ≠ 1 := by
    have : 2 ≤ d := hd2
    simp only [hqdef]
    nlinarith
  set p : ℕ := q.minFac with hpdef
  have hp : p.Prime := Nat.minFac_prime hq1
  have hpq : p ∣ q := Nat.minFac_dvd q
  refine ⟨p, hp, ?_, ?_⟩
  · rw [two_pow_three_mul_factor n]
    refine Dvd.dvd.mul_left ?_ _
    rw [second_factor_eq hd]
    exact hpq.mul_left 3
  · intro hcon
    -- `p ∣ 2 ^ n + 1 = 3 * d + 3` and `p ∣ q` force `p ∣ 3`, i.e. `p = 3`, contradicting `3 ∤ q`.
    have h1 : p ∣ 3 * d + 3 := by rw [hd] at hcon; simpa [Nat.add_assoc] using hcon
    have h2 : p ∣ 3 * q := hpq.mul_left 3
    have h3' : p ∣ 3 := by
      have hsub : 3 * q = (3 * d + 3) * (3 * d) + 3 := by simp only [hqdef]; ring
      rw [hsub] at h2
      exact (Nat.dvd_add_right (Dvd.dvd.mul_right h1 (3 * d))).mp h2
    have hp3 : p = 3 := ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h3')
    rw [hp3] at hpq
    obtain ⟨e, he⟩ := hpq
    simp only [hqdef] at he
    omega

/-- The main induction: for every `k` there is a positive `n` divisible by `3`, with exactly
`k + 1` distinct prime factors, such that `n ∣ 2 ^ n + 1`. -/
theorem exists_witness (k : ℕ) :
    ∃ n : ℕ, 0 < n ∧ 3 ∣ n ∧ n ∣ 2 ^ n + 1 ∧ n.primeFactors.card = k + 1 := by
  induction k with
  | zero =>
    refine ⟨3, by norm_num, dvd_rfl, by norm_num, ?_⟩
    rw [Nat.Prime.primeFactors (by norm_num)]
    simp
  | succ k ih =>
    obtain ⟨n, hpos, h3, hdvd, hcard⟩ := ih
    obtain ⟨p, hp, hpdvd, hpndvd⟩ := exists_new_prime h3 hpos hdvd
    have hNdvd : 3 * n ∣ 2 ^ (3 * n) + 1 := three_mul_dvd h3 hpos hdvd
    have hpn : ¬ p ∣ n := fun h => hpndvd (h.trans hdvd)
    have hp3 : p ≠ 3 := by
      rintro rfl
      exact hpn h3
    have hp2 : p ≠ 2 := by
      rintro rfl
      have h2 : (2 : ℕ) ∣ 2 ^ (3 * n) := dvd_pow_self 2 (Nat.mul_ne_zero (by norm_num) hpos.ne')
      omega
    have hpodd : Odd p := hp.odd_of_ne_two hp2
    have hcop : Nat.Coprime (3 * n) p := by
      refine (Nat.Prime.coprime_iff_not_dvd hp).mpr ?_ |>.symm
      intro hcon
      rcases (Nat.Prime.dvd_mul hp).mp hcon with h | h
      · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h)
      · exact hpn h
    refine ⟨3 * n * p, Nat.mul_pos (by omega) hp.pos, Dvd.dvd.mul_right ⟨n, rfl⟩ p, ?_, ?_⟩
    · have hstep : 2 ^ (3 * n) + 1 ∣ 2 ^ (3 * n * p) + 1 :=
        pow_add_one_dvd_pow_mul_add_one (3 * n) p hpodd
      exact hcop.mul_dvd_of_dvd_of_dvd (hNdvd.trans hstep) (hpdvd.trans hstep)
    · have hfac : (3 * n * p).primeFactors = n.primeFactors ∪ {p} := by
        rw [Nat.primeFactors_mul (Nat.mul_ne_zero (by norm_num) hpos.ne') hp.ne_zero, hp.primeFactors]
        congr 1
        rw [Nat.primeFactors_mul (by norm_num) hpos.ne']
        have : (3 : ℕ) ∈ n.primeFactors :=
          Nat.mem_primeFactors.mpr ⟨by norm_num, h3, hpos.ne'⟩
        rw [Nat.Prime.primeFactors (by norm_num : Nat.Prime 3)]
        simpa using Finset.singleton_subset_iff.mpr this
      rw [hfac, Finset.union_comm, Finset.card_union_of_disjoint, hcard]
      · simp; omega
      · simp only [Finset.disjoint_singleton_left, Nat.mem_primeFactors]
        rintro ⟨-, hdvd', -⟩
        exact hpn hdvd'

/-- **IMO 2000, Problem 5.**  There exists a positive integer `n` with exactly `2000`
distinct prime divisors such that `n ∣ 2 ^ n + 1`. -/
theorem imo2000_p5 :
    ∃ n : ℕ, 0 < n ∧ n.primeFactors.card = 2000 ∧ n ∣ 2 ^ n + 1 := by
  obtain ⟨n, hpos, -, hdvd, hcard⟩ := exists_witness 1999
  exact ⟨n, hpos, hcard, hdvd⟩

end Imo2000P5
