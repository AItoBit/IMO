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
# IMO 1990 Problem 3

Determine all integers `n > 1` such that `(2 ^ n + 1) / n ^ 2` is an integer.

The answer is `n = 3`.
-/

namespace Imo1990P3

/-- If `0 < k < n.minFac` then `n` and `k` are coprime: any prime dividing both would be
a prime factor of `n` no larger than `k`, hence smaller than the least prime factor of `n`. -/
theorem coprime_of_lt_minFac {n k : ℕ} (hk0 : 0 < k) (hk : k < n.minFac) :
    Nat.Coprime n k := by
  by_contra hc
  set g : ℕ := Nat.gcd n k with hg
  have hgk : g ∣ k := Nat.gcd_dvd_right n k
  have hgn : g ∣ n := Nat.gcd_dvd_left n k
  have hg1 : g ≠ 1 := hc
  have hr : (g.minFac) ∣ n := dvd_trans (Nat.minFac_dvd g) hgn
  have hrk : (g.minFac) ∣ k := dvd_trans (Nat.minFac_dvd g) hgk
  have hg2 : 2 ≤ g.minFac := (Nat.minFac_prime hg1).two_le
  have h1 : n.minFac ≤ g.minFac := Nat.minFac_le_of_dvd hg2 hr
  have h2 : g.minFac ≤ k := Nat.le_of_dvd hk0 hrk
  omega

/-- If an odd prime `q` divides `2 ^ n + 1` then the multiplicative order of `2` modulo `q`
divides `2 * n`. -/
theorem orderOf_two_dvd_two_mul {q : ℕ} [Fact q.Prime] {n : ℕ} (h : q ∣ 2 ^ n + 1) :
    orderOf (2 : ZMod q) ∣ 2 * n := by
  apply orderOf_dvd_of_pow_eq_one
  have h0 : ((2 ^ n + 1 : ℕ) : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h
  push_cast at h0
  have : (2 : ZMod q) ^ n = -1 := by linear_combination h0
  rw [two_mul, pow_add, this]
  ring

/-- The multiplicative order of `2` modulo an odd prime `q` divides `q - 1`. -/
theorem orderOf_two_dvd_sub_one {q : ℕ} [hq : Fact q.Prime] (hq2 : q ≠ 2) :
    orderOf (2 : ZMod q) ∣ q - 1 := by
  apply orderOf_dvd_of_pow_eq_one
  apply ZMod.pow_card_sub_one_eq_one
  intro h
  have : ((2 : ℕ) : ZMod q) = 0 := by exact_mod_cast h
  have := (ZMod.natCast_eq_zero_iff _ _).mp this
  have := (Nat.prime_dvd_prime_iff_eq hq.out Nat.prime_two).mp this
  exact hq2 this

/-- If the multiplicative order of `2` modulo a prime `q` divides `k`, then `q ∣ 2 ^ k - 1`. -/
theorem dvd_two_pow_sub_one {q k : ℕ} [Fact q.Prime] (h : orderOf (2 : ZMod q) ∣ k) :
    q ∣ 2 ^ k - 1 := by
  have h1 : (2 : ZMod q) ^ k = 1 := orderOf_dvd_iff_pow_eq_one.mp h
  have hk : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have : ((2 ^ k - 1 : ℕ) : ZMod q) = 0 := by
    push_cast [hk]
    rw [h1]
    ring
  exact (ZMod.natCast_eq_zero_iff _ _).mp this

/-- `2 ^ n + 1` is odd, so a solution `n` of `n ^ 2 ∣ 2 ^ n + 1` must be odd. -/
theorem odd_of_dvd {n : ℕ} (hn : 1 < n) (h : n ^ 2 ∣ 2 ^ n + 1) : Odd n := by
  rcases Nat.even_or_odd n with he | ho
  · exfalso
    have h2 : (2 : ℕ) ∣ 2 ^ n + 1 := dvd_trans (dvd_trans he.two_dvd (dvd_pow_self n two_ne_zero))
      h
    have : (2 : ℕ) ∣ 2 ^ n := dvd_pow_self 2 (by omega)
    omega
  · exact ho

/-- The least prime factor of a solution is `3`. -/
theorem minFac_eq_three {n : ℕ} (hn : 1 < n) (h : n ^ 2 ∣ 2 ^ n + 1) : n.minFac = 3 := by
  set p := n.minFac with hp
  have hpp : p.Prime := Nat.minFac_prime (by omega)
  haveI : Fact p.Prime := ⟨hpp⟩
  have hodd : Odd n := odd_of_dvd hn h
  have hp2 : p ≠ 2 := by
    intro h2
    have : (2 : ℕ) ∣ n := h2 ▸ Nat.minFac_dvd n
    rcases hodd with ⟨k, hk⟩
    omega
  have hpn : p ∣ n := Nat.minFac_dvd n
  have hpd : p ∣ 2 ^ n + 1 := dvd_trans hpn (dvd_trans (dvd_pow_self n two_ne_zero) h)
  have hd1 : orderOf (2 : ZMod p) ∣ 2 * n := orderOf_two_dvd_two_mul hpd
  have hd2 : orderOf (2 : ZMod p) ∣ p - 1 := orderOf_two_dvd_sub_one hp2
  have hcop : Nat.Coprime n (p - 1) := by
    apply coprime_of_lt_minFac
    · have := hpp.two_le; omega
    · have := hpp.two_le; omega
  have hcop2 : Nat.Coprime (orderOf (2 : ZMod p)) n :=
    (Nat.Coprime.coprime_dvd_right hd2 hcop).symm
  have hdvd2 : orderOf (2 : ZMod p) ∣ 2 := (Nat.Coprime.dvd_of_dvd_mul_right hcop2 hd1)
  have h3 : p ∣ 2 ^ 2 - 1 := dvd_two_pow_sub_one hdvd2
  norm_num at h3
  exact (Nat.prime_dvd_prime_iff_eq hpp (by norm_num)).mp h3

/-- The `3`-adic valuation of a solution is exactly `1`. -/
theorem padicValNat_three_eq_one {n : ℕ} (hn : 1 < n) (h : n ^ 2 ∣ 2 ^ n + 1) :
    padicValNat 3 n = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hodd : Odd n := odd_of_dvd hn h
  have h3n : (3 : ℕ) ∣ n := by
    have := minFac_eq_three hn h
    exact this ▸ Nat.minFac_dvd n
  have hval : padicValNat 3 (2 ^ n + 1 ^ n) = padicValNat 3 (2 + 1) + padicValNat 3 n :=
    padicValNat.pow_add_pow (by norm_num) (by norm_num) (by norm_num) hodd
  simp only [one_pow] at hval
  have h31 : padicValNat 3 3 = 1 := by simp
  norm_num [h31] at hval
  set v := padicValNat 3 n with hv
  have hv1 : 1 ≤ v := by
    rw [hv]
    exact one_le_padicValNat_of_dvd (by omega) h3n
  have hpow : (3 : ℕ) ^ v ∣ n := pow_padicValNat_dvd
  have hpow2 : (3 : ℕ) ^ (2 * v) ∣ 2 ^ n + 1 := by
    calc (3 : ℕ) ^ (2 * v) = (3 ^ v) ^ 2 := by ring
    _ ∣ n ^ 2 := pow_dvd_pow_of_dvd hpow 2
    _ ∣ 2 ^ n + 1 := h
  have hne : 2 ^ n + 1 ≠ 0 := by positivity
  have hle : 2 * v ≤ padicValNat 3 (2 ^ n + 1) := (padicValNat_dvd_iff_le hne).mp hpow2
  omega

/-- **IMO 1990, Problem 3.** For an integer `n > 1`, `n ^ 2` divides `2 ^ n + 1`
if and only if `n = 3`. -/
theorem imo1990_p3 (n : ℕ) (hn : 1 < n) : n ^ 2 ∣ 2 ^ n + 1 ↔ n = 3 := by
  constructor
  · intro h
    by_contra hne
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    have hodd : Odd n := odd_of_dvd hn h
    have h3n : (3 : ℕ) ∣ n := by
      have := minFac_eq_three hn h
      exact this ▸ Nat.minFac_dvd n
    obtain ⟨m, hm⟩ := h3n
    have hv := padicValNat_three_eq_one hn h
    have h3m : ¬ (3 : ℕ) ∣ m := by
      intro ⟨k, hk⟩
      have h9 : (3 : ℕ) ^ 2 ∣ n := ⟨k, by rw [hm, hk]; ring⟩
      have : 2 ≤ padicValNat 3 n := (padicValNat_dvd_iff_le (by omega)).mp h9
      omega
    have hm1 : 1 < m := by
      rcases Nat.lt_or_ge m 2 with hlt | hge
      · interval_cases m <;> omega
      · omega
    set q := m.minFac with hq
    have hqp : q.Prime := Nat.minFac_prime (by omega)
    haveI : Fact q.Prime := ⟨hqp⟩
    have hqm : q ∣ m := Nat.minFac_dvd m
    have hqn : q ∣ n := hm ▸ Dvd.dvd.mul_left hqm 3
    have hqd : q ∣ 2 ^ n + 1 := dvd_trans hqn (dvd_trans (dvd_pow_self n two_ne_zero) h)
    have hq3 : q ≠ 3 := fun hc => h3m (hc ▸ hqm)
    have hd1 : orderOf (2 : ZMod q) ∣ 2 * n := orderOf_two_dvd_two_mul hqd
    have hq2 : q ≠ 2 := by
      intro h2
      have : (2 : ℕ) ∣ n := h2 ▸ hqn
      rcases hodd with ⟨k, hk⟩
      omega
    have hd2 : orderOf (2 : ZMod q) ∣ q - 1 := orderOf_two_dvd_sub_one hq2
    have hcop : Nat.Coprime m (q - 1) := by
      apply coprime_of_lt_minFac
      · have := hqp.two_le; omega
      · have := hqp.two_le; omega
    have hcop2 : Nat.Coprime (orderOf (2 : ZMod q)) m :=
      (Nat.Coprime.coprime_dvd_right hd2 hcop).symm
    have hd6 : orderOf (2 : ZMod q) ∣ 6 := by
      have h6m : orderOf (2 : ZMod q) ∣ 6 * m := by
        rw [show 6 * m = 2 * n by rw [hm]; ring]
        exact hd1
      exact hcop2.dvd_of_dvd_mul_right h6m
    have h63 : q ∣ 2 ^ 6 - 1 := dvd_two_pow_sub_one hd6
    norm_num at h63
    -- `63 = 7 * 9`, and `q ≠ 3`, so `q = 7`
    have hq9 : ¬ q ∣ 9 := by
      intro hdd
      have : q ∣ 3 ^ 2 := by norm_num at hdd ⊢; exact hdd
      have := hqp.dvd_of_dvd_pow this
      exact hq3 ((Nat.prime_dvd_prime_iff_eq hqp (by norm_num)).mp this)
    have hcq : Nat.Coprime q 9 := (Nat.Prime.coprime_iff_not_dvd hqp).mpr hq9
    have hq7 : q ∣ 7 := by
      have : q ∣ 7 * 9 := by norm_num; exact h63
      exact hcq.dvd_of_dvd_mul_right this
    have hq7' : q = 7 := (Nat.prime_dvd_prime_iff_eq hqp (by norm_num)).mp hq7
    -- but `7 ∣ 2 ^ n + 1` is impossible when `3 ∣ n`
    have h7 : (7 : ℕ) ∣ 2 ^ n + 1 := hq7' ▸ hqd
    have hpow : 2 ^ n % 7 = 1 := by
      have : (2 : ℕ) ^ n = 8 ^ (n / 3) := by
        rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_mul]
        congr 1
        omega
      rw [this]
      have : (8 : ℕ) ^ (n / 3) % 7 = 1 ^ (n / 3) % 7 := Nat.pow_mod 8 (n / 3) 7 ▸ by
        norm_num [Nat.pow_mod]
      simpa using this
    omega
  · rintro rfl
    norm_num

end Imo1990P3
