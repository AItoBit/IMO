import Mathlib

open scoped BigOperators

namespace IMO1998P3

def d (n : ℕ) : ℕ :=
  n.divisors.card

def ratio (n : ℕ) : ℚ :=
  (d (n ^ 2) : ℚ) / d n

def factor (e : ℕ) : ℚ :=
  (2 * (e : ℚ) + 1) / ((e : ℚ) + 1)

lemma d_pos {n : ℕ} (hn : 0 < n) :
    0 < d n := by
  apply Finset.card_pos.mpr
  exact ⟨1, Nat.one_mem_divisors.mpr (Nat.ne_of_gt hn)⟩

lemma d_prime_pow {p : ℕ} (hp : p.Prime) (e : ℕ) :
    d (p ^ e) = e + 1 := by
  simp [d, Nat.divisors_prime_pow hp]

lemma ratio_mul {m n : ℕ} (h : m.Coprime n) :
    ratio (m * n) = ratio m * ratio n := by
  unfold ratio d
  rw [
    mul_pow,
    (h.pow_left 2 |>.pow_right 2).card_divisors_mul,
    h.card_divisors_mul
  ]
  push_cast
  ring

lemma ratio_prime_pow {p : ℕ}
    (hp : p.Prime) (e : ℕ) :
    ratio (p ^ e) = factor e := by
  unfold ratio
  rw [← pow_mul, d_prime_pow hp, d_prime_pow hp]
  unfold factor
  push_cast
  ring

lemma realize_list (es : List ℕ) :
    ∃ n : ℕ, 0 < n ∧
      ratio n = (es.map factor).prod := by
  induction es with
  | nil =>
      exact ⟨1, by norm_num, by simp [ratio, d]⟩
  | cons e es ih =>
      obtain ⟨n, hn, he⟩ := ih
      obtain ⟨p, hnp, hp⟩ :=
        Nat.exists_infinite_primes (n + 1)
      have hcop : n.Coprime (p ^ e) := by
        apply hp.coprime_pow_of_not_dvd
        intro hdvd
        have := Nat.le_of_dvd hn hdvd
        omega
      refine ⟨n * p ^ e,
        Nat.mul_pos hn (pow_pos hp.pos _), ?_⟩
      rw [ratio_mul hcop, ratio_prime_pow hp, he]
      simp [mul_comm]

def chain (x : ℕ) : ℕ → List ℕ
  | 0 => []
  | t + 1 => x :: chain (2 * x) t

lemma chain_prod (t x : ℕ) :
    ((chain x t).map factor).prod =
      ((2 : ℚ) ^ t * (x : ℚ) + 1) / ((x : ℚ) + 1) := by
  induction t generalizing x with
  | zero =>
      have hx : (x : ℚ) + 1 ≠ 0 := by positivity
      simp [chain, hx]
  | succ t ih =>
      simp only [chain, List.map_cons, List.prod_cons]
      rw [ih]
      unfold factor
      push_cast
      have hx : (x : ℚ) + 1 ≠ 0 := by positivity
      have hx2 : 2 * (x : ℚ) + 1 ≠ 0 := by positivity
      rw [pow_succ]
      field_simp
      ring

lemma odd_list (k : ℕ) (hk : Odd k) :
    ∃ es : List ℕ, (es.map factor).prod = (k : ℚ) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
      by_cases hk1 : k = 1
      · subst k
        exact ⟨[], by simp⟩

      obtain ⟨z, y, hy, hpow⟩ :=
        Nat.exists_eq_two_pow_mul_odd (Nat.succ_ne_zero k)

      have hkpos : 0 < k := hk.pos
      have hypos : 0 < y := hy.pos

      have hz : 0 < z := by
        by_contra h
        have hz0 : z = 0 := by omega
        simp only [hz0, pow_zero, one_mul] at hpow
        obtain ⟨u, hu⟩ := hk
        obtain ⟨v, hv⟩ := hy
        omega

      have htwo : 2 ≤ 2 ^ z := by
        obtain ⟨t, rfl⟩ :=
          Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hz)
        have ht : 0 < (2 : ℕ) ^ t :=
          pow_pos (by decide) t
        rw [pow_succ]
        omega

      have hylt : y < k := by
        have hk3 : 3 ≤ k := by
          obtain ⟨u, hu⟩ := hk
          omega
        nlinarith

      obtain ⟨es, hes⟩ := ih y hylt hy

      let x := k - y

      have hsum : x + y = k :=
        Nat.sub_add_cancel (Nat.le_of_lt hylt)

      have hsumR :
          (x : ℚ) + (y : ℚ) = (k : ℚ) := by
        exact_mod_cast hsum

      have hpowR :
          (k : ℚ) + 1 = (2 : ℚ) ^ z * (y : ℚ) := by
        exact_mod_cast hpow

      refine ⟨es ++ chain x z, ?_⟩
      rw [
        List.map_append,
        List.prod_append,
        hes,
        chain_prod
      ]

      have hx : (x : ℚ) + 1 ≠ 0 := by positivity
      rw [← mul_div_assoc]
      apply (div_eq_iff hx).2
      nlinarith [
        congrArg (fun q : ℚ => q * (x : ℚ)) hpowR
      ]

lemma odd_d_square {n : ℕ} (hn : 0 < n) :
    Odd (d (n ^ 2)) := by
  unfold d
  rw [Nat.card_divisors (pow_ne_zero 2 (Nat.ne_of_gt hn))]
  apply Finset.prod_induction _ Odd
  · intro a b ha hb
    exact ha.mul hb
  · exact ⟨0, by norm_num⟩
  · intro p hp
    rw [Nat.factorization_pow]
    change Odd (2 * n.factorization p + 1)
    exact ⟨n.factorization p, rfl⟩

/-- Exactly the odd natural numbers occur as integer divisor-count ratios. -/
theorem imo1998_p3 (k : ℕ) :
    (∃ n : ℕ, 0 < n ∧
      (d (n ^ 2) : ℚ) / d n = (k : ℚ)) ↔ Odd k := by
  constructor
  · rintro ⟨n, hn, he⟩

    have hd : (d n : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (d_pos hn))

    have heR :
        (d (n ^ 2) : ℚ) = (k : ℚ) * (d n : ℚ) :=
      (div_eq_iff hd).mp he

    have heN : d (n ^ 2) = k * d n := by
      exact_mod_cast heR

    have ho := odd_d_square hn
    rw [heN] at ho
    exact (Nat.odd_mul.mp ho).1

  · intro hk
    obtain ⟨es, hes⟩ := odd_list k hk
    obtain ⟨n, hn, he⟩ := realize_list es
    exact ⟨n, hn, he.trans hes⟩

end IMO1998P3
