import Mathlib

/-!
# IMO 2005, Problem 4

Determine all positive integers relatively prime to every term of

  aₙ = 2ⁿ + 3ⁿ + 6ⁿ - 1,   n ≥ 1.

Answer: only `1`.

The main observation is that every prime `p` divides at least one term.

* `p = 2`: use `n = 1`.
* `p = 3`: use `n = 2`.
* `p ≥ 5`: use `n = p - 2`.

For `p ≥ 5`, Fermat's little theorem in `ZMod p` gives

  2^(p-1) = 1,
  3^(p-1) = 1,
  6^(p-1) = 1.

Since `p - 1 = (p - 2) + 1`, these become

  2^(p-2) * 2 = 1,
  3^(p-2) * 3 = 1,
  6^(p-2) * 6 = 1.

Hence

  6 * (2^(p-2) + 3^(p-2) + 6^(p-2) - 1) = 0

in `ZMod p`. Since `6 ≠ 0`, the desired term itself is zero mod `p`.
-/

namespace Imo2005P4

/--
**IMO 2005 P4.**

The only positive natural number coprime to every number

`2^n + 3^n + 6^n - 1`, for `n ≥ 1`,

is `1`.
-/
theorem imo2005_p4 (k : ℕ) (hk : 0 < k) :
    (∀ n : ℕ, 1 ≤ n →
      Nat.Coprime k (2 ^ n + 3 ^ n + 6 ^ n - 1)) ↔
      k = 1 := by
  constructor

  · intro hcop
    by_contra hk1

    -- Since `k ≠ 1`, it has a prime divisor.
    obtain ⟨p, hp, hpk⟩ :
        ∃ p : ℕ, p.Prime ∧ p ∣ k :=
      Nat.exists_prime_and_dvd hk1

    /-
    Every prime divides at least one term of the sequence.
    -/
    have hex :
        ∃ n : ℕ,
          1 ≤ n ∧
          p ∣ (2 ^ n + 3 ^ n + 6 ^ n - 1) := by

      rcases Nat.lt_or_ge p 5 with hlt | hge

      /-
      Small primes.

      Since `p` is prime and `p < 5`, it is either `2` or `3`.
      -/
      · have hp2 : 2 ≤ p := hp.two_le

        interval_cases p

        · -- p = 2, choose n = 1
          exact ⟨1, by norm_num, by norm_num⟩

        · -- p = 3, choose n = 2
          exact ⟨2, by norm_num, by norm_num⟩

        · -- p = 4, impossible
          norm_num at hp

      /-
      Main case: p ≥ 5.

      Take n = p - 2.
      -/
      · letI : Fact p.Prime := ⟨hp⟩

        refine ⟨p - 2, ?_, ?_⟩

        · omega

        /-
        First prove that p does not divide 2, 3, or 6.
        -/

        have hd2 : ¬ p ∣ 2 := by
          intro hd
          have hle : p ≤ 2 :=
            Nat.le_of_dvd (by norm_num) hd
          omega

        have hd3 : ¬ p ∣ 3 := by
          intro hd
          have hle : p ≤ 3 :=
            Nat.le_of_dvd (by norm_num) hd
          omega

        have hd6 : ¬ p ∣ 6 := by
          intro hd

          have hd' : p ∣ 2 * 3 := by
            simpa using hd

          rcases (hp.dvd_mul.mp hd') with hd2' | hd3'

          · exact hd2 hd2'

          · exact hd3 hd3'

        /-
        Therefore 2, 3, 6 are nonzero in ZMod p.
        -/

        have h2ne : (2 : ZMod p) ≠ 0 := by
          intro hz
          exact hd2 ((ZMod.natCast_eq_zero_iff 2 p).mp hz)

        have h3ne : (3 : ZMod p) ≠ 0 := by
          intro hz
          exact hd3 ((ZMod.natCast_eq_zero_iff 3 p).mp hz)

        have h6ne : (6 : ZMod p) ≠ 0 := by
          intro hz
          exact hd6 ((ZMod.natCast_eq_zero_iff 6 p).mp hz)

        /-
        Fermat's little theorem.
        -/

        have h2F :
            (2 : ZMod p) ^ (p - 1) = 1 :=
          ZMod.pow_card_sub_one_eq_one h2ne

        have h3F :
            (3 : ZMod p) ^ (p - 1) = 1 :=
          ZMod.pow_card_sub_one_eq_one h3ne

        have h6F :
            (6 : ZMod p) ^ (p - 1) = 1 :=
          ZMod.pow_card_sub_one_eq_one h6ne

        /-
        Rewrite p - 1 as (p - 2) + 1.

        These forms are exactly what we need for the final algebraic
        calculation.
        -/

        have hm :
            p - 2 + 1 = p - 1 := by
          omega

        have h2 :
            (2 : ZMod p) ^ (p - 2) * 2 = 1 := by
          rw [← pow_succ, hm]
          exact h2F

        have h3 :
            (3 : ZMod p) ^ (p - 2) * 3 = 1 := by
          rw [← pow_succ, hm]
          exact h3F

        have h6 :
            (6 : ZMod p) ^ (p - 2) * 6 = 1 := by
          rw [← pow_succ, hm]
          exact h6F

        /-
        Now show the sequence term vanishes in ZMod p.
        -/

        have h6X :
            (6 : ZMod p) *
                ((2 : ZMod p) ^ (p - 2) +
                 (3 : ZMod p) ^ (p - 2) +
                 (6 : ZMod p) ^ (p - 2) -
                 1) = 0 := by
          calc
            (6 : ZMod p) *
                ((2 : ZMod p) ^ (p - 2) +
                 (3 : ZMod p) ^ (p - 2) +
                 (6 : ZMod p) ^ (p - 2) -
                 1)
                =
                3 * ((2 : ZMod p) ^ (p - 2) * 2) +
                2 * ((3 : ZMod p) ^ (p - 2) * 3) +
                ((6 : ZMod p) ^ (p - 2) * 6) -
                6 := by
                  ring
            _ = 0 := by
                  rw [h2, h3, h6]
                  norm_num

        have hX :
            ((2 : ZMod p) ^ (p - 2) +
             (3 : ZMod p) ^ (p - 2) +
             (6 : ZMod p) ^ (p - 2) -
             1) = 0 := by
          exact (mul_eq_zero.mp h6X).resolve_left h6ne

        /-
        Transfer the equality in ZMod p back to divisibility in ℕ.
        -/

        have hge1 :
            1 ≤
              2 ^ (p - 2) +
              3 ^ (p - 2) +
              6 ^ (p - 2) := by
          positivity

        have hcast :
            ((2 ^ (p - 2) +
                3 ^ (p - 2) +
                6 ^ (p - 2) -
                1 : ℕ) : ZMod p) = 0 := by
          rw [Nat.cast_sub hge1]
          push_cast
          exact hX

        exact
          (ZMod.natCast_eq_zero_iff
            (2 ^ (p - 2) +
             3 ^ (p - 2) +
             6 ^ (p - 2) -
             1)
            p).mp hcast

    /-
    Let n be a term divisible by p.

    But p also divides k, contradicting the assumption that
    k is coprime to every sequence term.
    -/
    obtain ⟨n, hn, hpn⟩ := hex

    have hgcd :
        Nat.gcd k (2 ^ n + 3 ^ n + 6 ^ n - 1) = 1 :=
      hcop n hn

    have hp1 : p ∣ 1 := by
      rw [← hgcd]
      exact Nat.dvd_gcd hpk hpn

    have hp_le_one : p ≤ 1 :=
      Nat.le_of_dvd (by norm_num) hp1

    have hp_ge_two : 2 ≤ p :=
      hp.two_le

    omega

  · rintro rfl
    intro n hn
    exact Nat.coprime_one_left _

end Imo2005P4
