import Mathlib

/-!
# IMO 1999, Problem 4

Determine all pairs `(n, p)` of positive integers with `p` prime, `n ≤ 2p` and
`n^(p-1) ∣ (p-1)^n + 1`.

Answer: `(1, p)` for every prime `p`, together with `(2, 2)` and `(3, 3)`.

## Proof

* `n = 1` always works; `p = 2` forces `n ∣ 2`.
* For `p ≥ 3`, `p - 1` is even so `(p-1)^n + 1` is odd, hence `n` is odd.
* `p ∣ n` (`p_dvd_n`): let `q` be the least prime factor of `n`. Then `(p-1)^n ≡ -1 (mod q)`, so
  the order `d` of `p-1` mod `q` divides `2n` but not `n`; writing `g = gcd d n` gives `d = 2g`
  with `g ∣ n` and `g ∣ q - 1 < q`, so `g = 1` by minimality of `q`. Hence `d = 2`, and since `n`
  is odd, `p - 1 ≡ -1`, i.e. `q ∣ p`, so `q = p`.
* With `p ∣ n`, `n ≤ 2p` and `n` odd, `n = p`. Lifting the exponent gives
  `v_p((p-1)^p + 1) = v_p(p) + v_p(p) = 2`, so `p^(p-1) ∣ (p-1)^p + 1` forces `p - 1 ≤ 2`.
-/

namespace Imo1999P4

/-- The least prime factor argument: for `p ≥ 3` and `n` odd, `p ∣ n`. -/
theorem p_dvd_n {p n : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hn2 : 2 ≤ n) (hnodd : Odd n)
    (hdvd : n ^ (p - 1) ∣ (p - 1) ^ n + 1) : p ∣ n := by
  have hqp : (n.minFac).Prime := Nat.minFac_prime (by omega)
  have hqn : n.minFac ∣ n := Nat.minFac_dvd n
  have : Fact (n.minFac).Prime := ⟨hqp⟩
  set q := n.minFac with hqdef
  have hq2' : 2 ≤ q := hqp.two_le
  have hq2 : q ≠ 2 := by
    intro h
    rw [h] at hqn
    rw [Nat.odd_iff] at hnodd
    omega
  have hqdvd : q ∣ (p - 1) ^ n + 1 :=
    dvd_trans (dvd_trans hqn (dvd_pow_self n (by omega))) hdvd
  -- pass to `ZMod q`
  have hx : ((p - 1 : ℕ) : ZMod q) ^ n = -1 := by
    have h0 : (((p - 1) ^ n + 1 : ℕ) : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hqdvd
    push_cast at h0
    linear_combination h0
  have hxne : ((p - 1 : ℕ) : ZMod q) ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega : n ≠ 0)] at hx
    exact one_ne_zero (α := ZMod q) (by linear_combination hx)
  -- the order of `p-1` mod `q`
  have hdvd2n : orderOf ((p - 1 : ℕ) : ZMod q) ∣ 2 * n := by
    refine orderOf_dvd_of_pow_eq_one ?_
    rw [mul_comm, pow_mul, hx]
    ring
  have hnotdvdn : ¬ orderOf ((p - 1 : ℕ) : ZMod q) ∣ n := by
    intro hdn
    have h1 : ((p - 1 : ℕ) : ZMod q) ^ n = 1 := orderOf_dvd_iff_pow_eq_one.1 hdn
    rw [hx] at h1
    have h2 : ((2 : ℕ) : ZMod q) = 0 := by push_cast; linear_combination -h1
    have h3 : q ∣ 2 := (ZMod.natCast_eq_zero_iff 2 q).1 h2
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hqp Nat.prime_two).1 h3)
  have hdvdq1 : orderOf ((p - 1 : ℕ) : ZMod q) ∣ q - 1 :=
    orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one hxne)
  set d := orderOf ((p - 1 : ℕ) : ZMod q) with hddef
  have hdpos : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · exfalso
      rw [h] at hdvd2n
      have := Nat.eq_zero_of_zero_dvd hdvd2n
      omega
    · exact h
  set g := Nat.gcd d n with hgdef
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left n hdpos
  have hgd : g ∣ d := Nat.gcd_dvd_left d n
  have hgn : g ∣ n := Nat.gcd_dvd_right d n
  have hcop : Nat.Coprime (d / g) (n / g) := Nat.coprime_div_gcd_div_gcd hgpos
  have hstep : (d / g) ∣ 2 * (n / g) := by
    have h1 : g * (d / g) ∣ g * (2 * (n / g)) := by
      rw [Nat.mul_div_cancel' hgd]
      have h2 : g * (2 * (n / g)) = 2 * n := by
        rw [← mul_assoc, mul_comm g 2, mul_assoc, Nat.mul_div_cancel' hgn]
      rw [h2]
      exact hdvd2n
    exact (mul_dvd_mul_iff_left (by omega : g ≠ 0)).1 h1
  have hd2 : d / g = 2 := by
    have h1 : (d / g) ∣ 2 := hcop.dvd_of_dvd_mul_right hstep
    have h2 : d / g ≠ 1 := by
      intro h
      apply hnotdvdn
      have hde : d = g := by
        have h5 := Nat.div_mul_cancel hgd
        rw [h, one_mul] at h5
        omega
      rw [hde]
      exact hgn
    have h3 : d / g ≤ 2 := Nat.le_of_dvd (by omega) h1
    have h4 : 0 < d / g := Nat.div_pos (Nat.le_of_dvd hdpos hgd) hgpos
    omega
  have hdg : d = 2 * g := by
    have h5 := Nat.div_mul_cancel hgd
    rw [hd2] at h5
    omega
  have hg1 : g = 1 := by
    by_contra hg
    have hmf : (g.minFac) ∣ n := dvd_trans (Nat.minFac_dvd g) hgn
    have hmfp : (g.minFac).Prime := Nat.minFac_prime hg
    have h1 : q ≤ g.minFac := Nat.minFac_le_of_dvd hmfp.two_le hmf
    have h2 : g.minFac ≤ g := Nat.minFac_le (by omega)
    have h3 : d ≤ q - 1 := Nat.le_of_dvd (by omega) hdvdq1
    have h5 : 2 * g ≤ q - 1 := by rw [← hdg]; exact h3
    omega
  have hd : d = 2 := by omega
  -- conclude `q = p`
  have hsq : ((p - 1 : ℕ) : ZMod q) ^ 2 = 1 := by
    rw [← hd, hddef]
    exact pow_orderOf_eq_one _
  obtain ⟨k, hk⟩ := hnodd
  have hxn : ((p - 1 : ℕ) : ZMod q) ^ n = ((p - 1 : ℕ) : ZMod q) := by
    rw [hk, pow_add, pow_mul, hsq, one_pow, one_mul, pow_one]
  rw [hxn] at hx
  have hpz : ((p : ℕ) : ZMod q) = 0 := by
    have h1 : ((p : ℕ) : ZMod q) = ((p - 1 : ℕ) : ZMod q) + 1 := by
      have h6 : (p - 1) + 1 = p := by omega
      rw [← h6]
      push_cast
      ring
    rw [h1, hx]
    ring
  have hqp' : q ∣ p := (ZMod.natCast_eq_zero_iff p q).1 hpz
  have heq : q = p := (Nat.prime_dvd_prime_iff_eq hqp hp).1 hqp'
  rw [← heq]
  exact hqn

/-- Lifting the exponent: `p^(p-1) ∣ (p-1)^p + 1` forces `p = 3`. -/
theorem p_eq_three {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (h : p ^ (p - 1) ∣ (p - 1) ^ p + 1) : p = 3 := by
  by_contra hne
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have hp5 : 5 ≤ p := by
    rw [Nat.odd_iff] at hodd
    rcases Nat.lt_or_ge p 5 with hlt | hge
    · interval_cases p <;> omega
    · exact hge
  have hxy : p ∣ (p - 1) + 1 := by
    rw [Nat.sub_add_cancel (by omega)]
  have hx : ¬ p ∣ (p - 1) := Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  have hem := Nat.emultiplicity_pow_add_pow hp (by omega) hxy hx hodd
  have hself : emultiplicity p p = 1 := by
    refine emultiplicity_eq_coe.2 ⟨by simp, ?_⟩
    have h1 : p < p ^ 2 := by nlinarith [hp.two_le]
    exact Nat.not_dvd_of_pos_of_lt (by omega) h1
  have hsum : (p - 1) + 1 = p := by omega
  rw [one_pow, hsum, hself] at hem
  have hem2 : emultiplicity p ((p - 1) ^ p + 1) = 2 := by
    rw [hem]
    decide
  have h3 : p ^ 3 ∣ (p - 1) ^ p + 1 :=
    dvd_trans (pow_dvd_pow p (by omega)) h
  have hle : (3 : ℕ∞) ≤ emultiplicity p ((p - 1) ^ p + 1) :=
    pow_dvd_iff_le_emultiplicity.1 h3
  rw [hem2] at hle
  exact absurd hle (by decide)

/-- **IMO 1999 P4.** -/
theorem imo1999_p4 (n p : ℕ) (hp : p.Prime) (hn : 0 < n) (hle : n ≤ 2 * p) :
    n ^ (p - 1) ∣ (p - 1) ^ n + 1 ↔
      (n = 1 ∨ (n = 2 ∧ p = 2) ∨ (n = 3 ∧ p = 3)) := by
  constructor
  · intro hdvd
    rcases Nat.lt_or_ge n 2 with h1 | hn2
    · exact Or.inl (by omega)
    rcases Nat.lt_or_ge p 3 with hp2 | hp3
    · have hpe : p = 2 := by have := hp.two_le; omega
      subst hpe
      refine Or.inr (Or.inl ⟨?_, rfl⟩)
      have hd : n ∣ 2 := by simpa using hdvd
      have := Nat.le_of_dvd (by omega) hd
      interval_cases n <;> simp_all
    · have hnodd : Odd n := by
        rcases Nat.even_or_odd n with he | ho
        · exfalso
          have h2n : (2 : ℕ) ∣ n := he.two_dvd
          have h2 : (2 : ℕ) ∣ (p - 1) ^ n + 1 :=
            dvd_trans (dvd_trans h2n (dvd_pow_self n (by omega))) hdvd
          have hpm : Even (p - 1) := by
            have hpo := hp.odd_of_ne_two (by omega)
            rw [Nat.odd_iff] at hpo
            rw [Nat.even_iff]
            omega
          have hevp : Even ((p - 1) ^ n) := Nat.even_pow.2 ⟨hpm, by omega⟩
          rw [Nat.even_iff] at hevp
          rw [Nat.dvd_iff_mod_eq_zero] at h2
          omega
        · exact ho
      have hpn : p ∣ n := p_dvd_n hp hp3 hn2 hnodd hdvd
      have hnp : n = p := by
        obtain ⟨c, hc⟩ := hpn
        have hc2 : c ≤ 2 := by
          by_contra hcon
          have : 3 * p ≤ n := by rw [hc]; nlinarith
          omega
        interval_cases c
        · omega
        · omega
        · exfalso
          rw [Nat.odd_iff] at hnodd
          have hpodd := hp.odd_of_ne_two (by omega)
          rw [Nat.odd_iff] at hpodd
          omega
      subst hnp
      have h3 := p_eq_three hp hp3 hdvd
      exact Or.inr (Or.inr ⟨h3, h3⟩)
  · rintro (rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · simp
    · decide
    · decide

end Imo1999P4
