/-
# IMO 1971, Problem 3

Prove that the set of integers of the form `2 ^ k - 3` (`k = 2, 3, …`) contains
an infinite subset in which every two members are relatively prime.

## Strategy

Instead of the (slightly hand-waved) induction of the AoPS write-up, we build a
sequence of exponents `K 0, K 1, K 2, …` together with the running product

  `Q n = ∏ i < n, (2 ^ K i - 3)`,

and we make every new term coprime to the *whole* product at once, which gives
pairwise coprimality directly:

* `K 0 = 3`, `Q 0 = 1`;
* `Q (n+1) = Q n * (2 ^ K n - 3)` and `K (n+1) = (K n + 1) * φ (Q (n+1))`.

Every `2 ^ K i - 3` is odd, so `Q n` is odd, so `2` is coprime to `Q n` and
Euler's theorem gives `2 ^ φ (Q (n+1)) ≡ 1 [MOD Q (n+1)]`.  Since
`φ (Q (n+1)) ∣ K (n+1)` we get `2 ^ K (n+1) ≡ 1 [MOD Q (n+1)]`.  Now if
`d ∣ 2 ^ K (n+1) - 3` and `d ∣ Q (n+1)`, then `d` divides both
`2 ^ K (n+1) - 1` and `2 ^ K (n+1) - 3`, hence `d ∣ 2`; but `d` divides the odd
number `Q (n+1)`, so `d = 1`.

Finally `2 ^ K i - 3 ∣ Q j` whenever `i < j`, so all the terms are pairwise
coprime; each of them is `≥ 5`, so they are pairwise distinct and the range is
infinite.
-/

import Mathlib

namespace Imo1971P3

/-- One step of the construction: from `(k, Q)` to
`((k + 1) * φ (Q * (2 ^ k - 3)), Q * (2 ^ k - 3))`. -/
private def step (p : ℕ × ℕ) : ℕ × ℕ :=
  ((p.1 + 1) * Nat.totient (p.2 * (2 ^ p.1 - 3)), p.2 * (2 ^ p.1 - 3))

private def seq : ℕ → ℕ × ℕ
  | 0 => (3, 1)
  | n + 1 => step (seq n)

/-- The exponents. -/
private def K (n : ℕ) : ℕ := (seq n).1

/-- The running product `∏ i < n, (2 ^ K i - 3)`. -/
private def Q (n : ℕ) : ℕ := (seq n).2

/-- The terms of the infinite subset. -/
private def f (n : ℕ) : ℕ := 2 ^ K n - 3

private lemma K_zero : K 0 = 3 := rfl
private lemma Q_zero : Q 0 = 1 := rfl
private lemma f_def (n : ℕ) : f n = 2 ^ K n - 3 := rfl
private lemma Q_succ (n : ℕ) : Q (n + 1) = Q n * f n := rfl
private lemma K_succ (n : ℕ) : K (n + 1) = (K n + 1) * Nat.totient (Q (n + 1)) := rfl

/-- The invariant carried along the construction. -/
private lemma inv (n : ℕ) : 3 ≤ K n ∧ 0 < Q n ∧ ¬ (2 ∣ Q n) := by
  induction n with
  | zero => refine ⟨by norm_num [K_zero], by norm_num [Q_zero], by norm_num [Q_zero]⟩
  | succ m ih =>
    obtain ⟨hK, hQ, hQ2⟩ := ih
    have hx : 8 ≤ 2 ^ K m := by
      calc (8 : ℕ) = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ K m := Nat.pow_le_pow_right (by norm_num) hK
    have hxe : (2 : ℕ) ∣ 2 ^ K m := dvd_pow_self 2 (by omega)
    have hfdef : f m = 2 ^ K m - 3 := f_def m
    have hf5 : 5 ≤ f m := by omega
    have hf2 : ¬ (2 ∣ f m) := by omega
    have hQ' : 0 < Q (m + 1) := by
      rw [Q_succ]; exact Nat.mul_pos hQ (by omega)
    have hQ2' : ¬ (2 ∣ Q (m + 1)) := by
      rw [Q_succ]
      intro hcon
      rcases (Nat.Prime.dvd_mul Nat.prime_two).mp hcon with h | h
      · exact hQ2 h
      · exact hf2 h
    have hphi : 0 < Nat.totient (Q (m + 1)) := Nat.totient_pos.mpr hQ'
    refine ⟨?_, hQ', hQ2'⟩
    rw [K_succ]
    have h4 : 4 * 1 ≤ (K m + 1) * Nat.totient (Q (m + 1)) :=
      Nat.mul_le_mul (by omega) hphi
    omega

private lemma eight_le (n : ℕ) : 8 ≤ 2 ^ K n := by
  calc (8 : ℕ) = 2 ^ 3 := by norm_num
    _ ≤ 2 ^ K n := Nat.pow_le_pow_right (by norm_num) (inv n).1

private lemma five_le_f (n : ℕ) : 5 ≤ f n := by
  have h := eight_le n
  have hfdef : f n = 2 ^ K n - 3 := f_def n
  omega

/-- Each new term is coprime to the whole product of the previous ones. -/
private lemma coprime_f_Q (n : ℕ) : Nat.Coprime (f n) (Q n) := by
  cases n with
  | zero => rw [Q_zero]; exact Nat.coprime_one_right _
  | succ m =>
    obtain ⟨hK, hQ, hQ2⟩ := inv (m + 1)
    -- Euler: `2 ^ φ (Q (m+1)) ≡ 1 [MOD Q (m+1)]`.
    have hc2 : Nat.Coprime 2 (Q (m + 1)) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hQ2
    have hmod : (2 : ℕ) ^ Nat.totient (Q (m + 1)) ≡ 1 [MOD Q (m + 1)] :=
      Nat.ModEq.pow_totient hc2
    -- and `φ (Q (m+1)) ∣ K (m+1)`, so `2 ^ K (m+1) ≡ 1 [MOD Q (m+1)]`.
    have hmod2 : (2 : ℕ) ^ K (m + 1) ≡ 1 [MOD Q (m + 1)] := by
      rw [K_succ, Nat.mul_comm, pow_mul]
      simpa using hmod.pow (K m + 1)
    have hx8 : 8 ≤ 2 ^ K (m + 1) := eight_le (m + 1)
    -- Any common divisor of `f (m+1)` and `Q (m+1)` divides `2`, hence is `1`.
    have key : ∀ d : ℕ, d ∣ f (m + 1) → d ∣ Q (m + 1) → d = 1 := by
      intro d hd1 hd2
      have hmodd : (2 : ℕ) ^ K (m + 1) ≡ 1 [MOD d] := Nat.ModEq.of_dvd hd2 hmod2
      have hdvd1 : d ∣ 2 ^ K (m + 1) - 1 :=
        (Nat.modEq_iff_dvd' (by omega)).mp hmodd.symm
      have hdvd2 : d ∣ 2 ^ K (m + 1) - 3 := hd1
      have hd2' : d ∣ 2 := by
        -- `Nat.dvd_sub'` no longer exists; cancel the common summand instead.
        have heq : 2 ^ K (m + 1) - 1 = (2 ^ K (m + 1) - 3) + 2 := by omega
        rw [heq] at hdvd1
        exact (Nat.dvd_add_right hdvd2).mp hdvd1
      rcases (Nat.dvd_prime Nat.prime_two).mp hd2' with h1 | h1
      · exact h1
      · subst h1; exact absurd hd2 hQ2
    exact key _ (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _)

private lemma Q_dvd_Q : ∀ i j : ℕ, i ≤ j → Q i ∣ Q j := by
  intro i j
  induction j with
  | zero =>
    intro h
    rw [Nat.le_zero.mp h]
  | succ m ih =>
    intro h
    rcases Nat.eq_or_lt_of_le h with h' | h'
    · rw [h']
    · exact (ih (by omega)).trans ⟨f m, Q_succ m⟩

private lemma f_dvd_Q {i j : ℕ} (h : i < j) : f i ∣ Q j := by
  -- the type ascription must be on a `have`, otherwise the anonymous
  -- constructor stays an `Exists` and `.trans` resolves to `Exists.trans`.
  have h1 : f i ∣ Q (i + 1) := ⟨Q i, by rw [Q_succ i, Nat.mul_comm]⟩
  exact h1.trans (Q_dvd_Q _ _ h)

private lemma coprime_lt {i j : ℕ} (h : i < j) : Nat.Coprime (f i) (f j) :=
  (Nat.Coprime.coprime_dvd_right (f_dvd_Q h) (coprime_f_Q j)).symm

private lemma f_ne {i j : ℕ} (h : i < j) : f i ≠ f j := by
  intro hij
  have hc := coprime_lt h
  rw [hij] at hc
  have h1 : Nat.gcd (f j) (f j) = 1 := hc
  rw [Nat.gcd_self] at h1
  have h5 := five_le_f j
  omega

private lemma f_inj : Function.Injective f := by
  intro i j hij
  by_contra hne
  rcases Nat.lt_or_ge i j with h | h
  · exact f_ne h hij
  · exact f_ne (by omega : j < i) hij.symm

/-- **IMO 1971, Problem 3.**  The set of integers of the form `2 ^ k - 3`
(`k ≥ 2`) contains an infinite subset whose members are pairwise coprime. -/
theorem imo1971_p3 :
    ∃ S : Set ℕ,
      S.Infinite ∧
      S ⊆ {n : ℕ | ∃ k : ℕ, 2 ≤ k ∧ n = 2 ^ k - 3} ∧
      ∀ x ∈ S, ∀ y ∈ S, x ≠ y → Nat.Coprime x y := by
  refine ⟨Set.range f, Set.infinite_range_of_injective f_inj, ?_, ?_⟩
  · rintro _ ⟨n, rfl⟩
    exact ⟨K n, by have := (inv n).1; omega, f_def n⟩
  · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hne
    have hij : i ≠ j := fun hh => hne (by rw [hh])
    rcases Nat.lt_or_ge i j with h | h
    · exact coprime_lt h
    · exact (coprime_lt (by omega : j < i)).symm

end Imo1971P3
