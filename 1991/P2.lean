import Mathlib

namespace IMO1991P2

private theorem dvd_nat_sub
    {d a b : ℕ}
    (ha : d ∣ a)
    (hb : d ∣ b) :
    d ∣ a - b := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  refine ⟨x - y, ?_⟩
  rw [Nat.mul_sub_left_distrib]

private theorem divisor_eight_eq_one
    (g r : ℕ)
    (hgr : g ∣ r)
    (hg8 : g ∣ 8)
    (hodd : r % 2 = 1) :
    g = 1 := by
  have hg : g ≤ 8 :=
    Nat.le_of_dvd (by norm_num) hg8
  interval_cases g <;>
    norm_num [Nat.dvd_iff_mod_eq_zero] at * <;>
    omega

/--
An odd number `r` is coprime to `n` if `n - 2*r`
divides 8.
-/
private theorem coprime_small_difference
    (n r : ℕ)
    (hodd : r % 2 = 1)
    (hdiff : (n - 2 * r) ∣ 8) :
    Nat.Coprime r n := by
  have hgr : Nat.gcd r n ∣ r :=
    Nat.gcd_dvd_left r n
  have hgn : Nat.gcd r n ∣ n :=
    Nat.gcd_dvd_right r n
  have hg2r : Nat.gcd r n ∣ 2 * r :=
    dvd_mul_of_dvd_right hgr 2
  have hgd : Nat.gcd r n ∣ n - 2 * r :=
    dvd_nat_sub hgn hg2r
  change Nat.gcd r n = 1
  exact divisor_eight_eq_one
    (Nat.gcd r n) r hgr (dvd_trans hgd hdiff) hodd

private theorem coprime_predecessor
    (n : ℕ)
    (hn : 1 ≤ n) :
    Nat.Coprime (n - 1) n := by
  have h :
      Nat.gcd (n - 1) n ∣ n - (n - 1) :=
    dvd_nat_sub
      (Nat.gcd_dvd_right (n - 1) n)
      (Nat.gcd_dvd_left (n - 1) n)
  have heq : n - (n - 1) = 1 := by
    omega
  rw [heq] at h
  change Nat.gcd (n - 1) n = 1
  exact Nat.dvd_one.mp h

private theorem coprime_two_of_odd
    (n : ℕ)
    (hodd : n % 2 = 1) :
    Nat.Coprime 2 n := by
  have hg8 : Nat.gcd 2 n ∣ 8 :=
    dvd_trans (Nat.gcd_dvd_left 2 n) (by norm_num)
  change Nat.gcd 2 n = 1
  exact divisor_eight_eq_one
    (Nat.gcd 2 n) n
    (Nat.gcd_dvd_right 2 n) hg8 hodd

/--
If every positive number below `n` coprime to `n`
is congruent to 1 modulo `d`, then `d` divides 2.
-/
private theorem common_difference_dvd_two
    (n d : ℕ)
    (hn : 6 < n)
    (hall :
      ∀ r : ℕ, 0 < r → r < n →
        Nat.Coprime r n → d ∣ r - 1) :
    d ∣ 2 := by
  have hend : d ∣ n - 2 := by
    have h :=
      hall (n - 1) (by omega) (by omega)
        (coprime_predecessor n (by omega))
    have heq : n - 1 - 1 = n - 2 := by
      omega
    rwa [heq] at h

  by_cases hnEven : n % 2 = 0
  · let m := n / 2
    have hnm : n = 2 * m := by
      dsimp [m]
      omega

    by_cases hmEven : m % 2 = 0
    · have hm : 4 ≤ m := by
        omega

      have hcop : Nat.Coprime (m - 1) n := by
        apply coprime_small_difference
        · omega
        · have heq : n - 2 * (m - 1) = 2 := by
            omega
          rw [heq]
          norm_num

      have hd : d ∣ m - 2 := by
        have h :=
          hall (m - 1) (by omega) (by omega) hcop
        have heq : m - 1 - 1 = m - 2 := by
          omega
        rwa [heq] at h

      have h :
          d ∣ (n - 2) - 2 * (m - 2) :=
        dvd_nat_sub hend (dvd_mul_of_dvd_right hd 2)
      have heq :
          (n - 2) - 2 * (m - 2) = 2 := by
        omega
      rwa [heq] at h

    · have hmOdd : m % 2 = 1 := by
        omega
      have hm : 5 ≤ m := by
        omega

      have hcop₁ : Nat.Coprime (m - 2) n := by
        apply coprime_small_difference
        · omega
        · have heq : n - 2 * (m - 2) = 4 := by
            omega
          rw [heq]
          norm_num

      have hcop₂ : Nat.Coprime (m - 4) n := by
        apply coprime_small_difference
        · omega
        · have heq : n - 2 * (m - 4) = 8 := by
            omega
          rw [heq]

      have hd₁ : d ∣ (m - 2) - 1 :=
        hall (m - 2) (by omega) (by omega) hcop₁
      have hd₂ : d ∣ (m - 4) - 1 :=
        hall (m - 4) (by omega) (by omega) hcop₂

      have h :
          d ∣ ((m - 2) - 1) - ((m - 4) - 1) :=
        dvd_nat_sub hd₁ hd₂
      have heq :
          ((m - 2) - 1) - ((m - 4) - 1) = 2 := by
        omega
      rwa [heq] at h

  · have hnOdd : n % 2 = 1 := by
      omega
    have hd1 : d ∣ 1 := by
      simpa using
        hall 2 (by omega) (by omega)
          (coprime_two_of_odd n hnOdd)
    exact dvd_trans hd1 (by norm_num)

/-- A divisor coprime to its multiple must equal 1. -/
private theorem eq_one_of_dvd_of_coprime
    {r n : ℕ}
    (hd : r ∣ n)
    (hc : Nat.Coprime r n) :
    r = 1 := by
  have h : r ∣ Nat.gcd r n :=
    Nat.dvd_gcd (dvd_refl r) hd
  change Nat.gcd r n = 1 at hc
  rw [hc] at h
  exact Nat.dvd_one.mp h

private theorem prime_of_all_coprime
    (n : ℕ)
    (hn : 2 ≤ n)
    (hall :
      ∀ r : ℕ, 0 < r → r < n →
        Nat.Coprime r n) :
    Nat.Prime n := by
  apply Nat.prime_def_lt.mpr
  refine ⟨hn, ?_⟩
  intro r hr hd
  have hrpos : 0 < r := by
    by_contra h
    have hr0 : r = 0 := by
      omega
    subst r
    have hn0 : n = 0 := by
      simpa using hd
    omega
  exact eq_one_of_dvd_of_coprime hd (hall r hrpos hr)

/--
A positive natural number with no odd divisor other than 1
is a power of 2.
-/
private theorem power_two_of_odd_divisors
    (n : ℕ) :
    0 < n →
    (∀ r : ℕ, r ∣ n → r % 2 = 1 → r = 1) →
    ∃ e : ℕ, n = 2 ^ e := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hn hdiv
      by_cases hodd : n % 2 = 1
      · have hn1 : n = 1 :=
          hdiv n (dvd_refl n) hodd
        exact ⟨0, by simpa using hn1⟩
      · have heven : n % 2 = 0 := by
          omega
        have hhalf : n / 2 ∣ n := by
          refine ⟨2, ?_⟩
          omega
        obtain ⟨e, he⟩ :=
          ih (n / 2) (by omega) (by omega)
            (by
              intro r hr hro
              exact hdiv r (dvd_trans hr hhalf) hro)
        refine ⟨e + 1, ?_⟩
        rw [pow_succ, ← he]
        omega

/--
Classification from the exact arithmetic-progression
description of the reduced residues.
-/
theorem classification_of_residue_progression
    (n d : ℕ)
    (hn : 6 < n)
    (hd : 0 < d)
    (hres :
      ∀ r : ℕ, 0 < r → r < n →
        (Nat.Coprime r n ↔ d ∣ r - 1)) :
    Nat.Prime n ∨ ∃ e : ℕ, n = 2 ^ e := by
  have hd2 : d ∣ 2 :=
    common_difference_dvd_two n d hn
      (by
        intro r hr hrn hc
        exact (hres r hr hrn).mp hc)

  have hdle : d ≤ 2 :=
    Nat.le_of_dvd (by norm_num) hd2
  have hcases : d = 1 ∨ d = 2 := by
    omega

  rcases hcases with hd1 | hd2
  · left
    apply prime_of_all_coprime n (by omega)
    intro r hr hrn
    apply (hres r hr hrn).mpr
    simp [hd1]

  · right
    have hend : 2 ∣ (n - 1) - 1 := by
      have h :=
        (hres (n - 1) (by omega) (by omega)).mp
          (coprime_predecessor n (by omega))
      simpa [hd2] using h

    have hnEven : n % 2 = 0 := by
      obtain ⟨t, ht⟩ := hend
      omega

    apply power_two_of_odd_divisors n (by omega)
    intro r hrdiv hrodd

    have hrpos : 0 < r := by
      omega
    have hrle : r ≤ n :=
      Nat.le_of_dvd (by omega) hrdiv
    have hrlt : r < n := by
      omega

    have hstep : d ∣ r - 1 := by
      rw [hd2]
      refine ⟨r / 2, ?_⟩
      omega

    have hcop : Nat.Coprime r n :=
      (hres r hrpos hrlt).mpr hstep
    exact eq_one_of_dvd_of_coprime hrdiv hcop

/--
IMO 1991 Problem 2.

`a 0, ..., a (k-1)` list exactly the positive integers
less than `n` that are coprime to `n`.

Their successive differences equal the positive integer `d`.
-/
theorem imo1991_problem2
    (n k d : ℕ)
    (a : ℕ → ℕ)
    (hn : 6 < n)
    (hd : 0 < d)
    (hset :
      ∀ r : ℕ,
        (0 < r ∧ r < n ∧ Nat.Coprime r n) ↔
          ∃ i : ℕ, i < k ∧ a i = r)
    (hstep :
      ∀ i : ℕ, i + 1 < k →
        a (i + 1) = a i + d) :
    Nat.Prime n ∨ ∃ e : ℕ, n = 2 ^ e := by

  have hformula :
      ∀ i : ℕ, i < k → a i = a 0 + i * d := by
    intro i
    induction i with
    | zero =>
        intro _
        simp
    | succ i ih =>
        intro hi
        rw [hstep i hi, ih (by omega)]
        ring

  obtain ⟨i₁, hi₁, hai₁⟩ :=
    (hset 1).mp
      ⟨by omega, by omega, by simp⟩

  have hk : 0 < k := by
    omega

  have ha0pos : 0 < a 0 :=
    ((hset (a 0)).mpr ⟨0, hk, rfl⟩).1

  have hfirst : a 0 = 1 := by
    have h := hformula i₁ hi₁
    rw [hai₁] at h
    omega

  obtain ⟨j, hj, haj⟩ :=
    (hset (n - 1)).mp
      ⟨by omega, by omega,
        coprime_predecessor n (by omega)⟩

  have hend : n - 1 = 1 + j * d := by
    have h := hformula j hj
    rw [haj, hfirst] at h
    exact h

  apply classification_of_residue_progression n d hn hd
  intro r hr hrn
  constructor

  · intro hcop
    obtain ⟨i, hi, hai⟩ :=
      (hset r).mp ⟨hr, hrn, hcop⟩

    have hvalue : r = 1 + i * d := by
      have h := hformula i hi
      rw [hai, hfirst] at h
      exact h

    refine ⟨i, ?_⟩
    rw [Nat.mul_comm d i]
    omega

  · intro hdiv
    obtain ⟨i, hi⟩ := hdiv

    have hi' : r - 1 = i * d := by
      simpa only [Nat.mul_comm] using hi

    have hvalue : r = 1 + i * d := by
      omega

    have hik : i < k := by
      by_contra hnot
      have hji : j + 1 ≤ i := by
        omega
      have hmul : (j + 1) * d ≤ i * d :=
        Nat.mul_le_mul_right d hji
      rw [Nat.add_mul, Nat.one_mul] at hmul
      omega

    have hai : a i = r := by
      rw [hformula i hik, hfirst]
      exact hvalue.symm

    exact ((hset r).mpr ⟨i, hik, hai⟩).2.2

end IMO1991P2
