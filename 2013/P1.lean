import Mathlib

namespace IMO2013P1

open scoped BigOperators

/-!
# IMO 2013 Problem 1

For all positive integers `k,n`, prove that there exist positive
integers `m₁,...,mₖ` such that

    1 + (2^k - 1)/n
      =
    ∏ᵢ (1 + 1/mᵢ).

We formalize the product over `ℚ`.
-/

/-- A factor of the required product. -/
noncomputable def factor (m : ℕ) : ℚ :=
  1 + 1 / (m : ℚ)

/-- Left-hand side of the IMO identity. -/
noncomputable def target (k n : ℕ) : ℚ :=
  1 + ((2 : ℚ) ^ k - 1) / (n : ℚ)

/--
`Works k n` means there are exactly `k` positive denominators
whose corresponding factors multiply to `target k n`.
-/
def Works (k n : ℕ) : Prop :=
  ∃ ms : List ℕ,
    ms.length = k ∧
    (∀ m ∈ ms, 0 < m) ∧
    (ms.map factor).prod = target k n

/-!
## Algebraic identities
-/

/--
Even case identity.

If `n = 2c`, then

    target (k+1) (2c)
      =
    target k c *
      (1 + 1/(2(c+2^k-1))).
-/
lemma even_identity_rat
    (k : ℕ)
    (c : ℚ)
    (hc : c ≠ 0)
    (hd :
      c + (2 : ℚ) ^ k - 1 ≠ 0) :
    1 + ((2 : ℚ) ^ (k + 1) - 1) / (2 * c)
      =
    (1 + ((2 : ℚ) ^ k - 1) / c) *
      (1 +
        1 /
          (2 * (c + (2 : ℚ) ^ k - 1))) := by

  field_simp [hc, hd]
  ring

/--
Odd case identity.

If `n = 2c+1`, then

    target (k+1) (2c+1)
      =
    target k (c+1) *
      (1 + 1/(2c+1)).
-/
lemma odd_identity_rat
    (k : ℕ)
    (c : ℚ)
    (hc :
      c + 1 ≠ 0)
    (hd :
      2 * c + 1 ≠ 0) :
    1 + ((2 : ℚ) ^ (k + 1) - 1) /
          (2 * c + 1)
      =
    (1 + ((2 : ℚ) ^ k - 1) / (c + 1)) *
      (1 + 1 / (2 * c + 1)) := by

  field_simp [hc, hd]
  ring

/-!
## Base case k = 1
-/

/--
For `k = 1`, take the single denominator `n`.
-/
lemma works_one
    (n : ℕ)
    (hn : 0 < n) :
    Works 1 n := by

  refine ⟨[n], ?_, ?_, ?_⟩

  · simp

  · intro m hm
    simp only [List.mem_singleton] at hm
    subst m
    exact hn

  · norm_num [factor, target]

/-!
## Parity decomposition
-/

/--
Every natural number is either `2*c` or `2*c+1`.
-/
lemma even_or_odd_form
    (n : ℕ) :
    ∃ c : ℕ,
      n = 2 * c ∨
      n = 2 * c + 1 := by

  let c : ℕ := n / 2

  have hdiv :
      n % 2 + 2 * (n / 2) = n := by
    simpa [Nat.mul_comm] using Nat.mod_add_div n 2

  have hmod :
      n % 2 < 2 := by
    exact Nat.mod_lt n (by norm_num)

  have hcases :
      n % 2 = 0 ∨ n % 2 = 1 := by
    omega

  refine ⟨c, ?_⟩

  rcases hcases with h0 | h1

  · left
    dsimp [c]
    omega

  · right
    dsimp [c]
    omega

/-!
## Inductive step
-/

/--
If the theorem holds for `k` for all positive `n`,
then it holds for `k+1`.
-/
lemma works_succ
    (k : ℕ)
    (ih :
      ∀ n : ℕ,
        0 < n →
        Works k n) :
    ∀ n : ℕ,
      0 < n →
      Works (k + 1) n := by

  intro n hn

  obtain ⟨c, hcEven | hcOdd⟩ :=
    even_or_odd_form n

  /- ============================================================
     Even case: n = 2*c
     ============================================================ -/
  · subst n

    have hcpos :
        0 < c := by
      omega

    obtain ⟨ms, hlen, hpositive, hprod⟩ :=
      ih c hcpos

    /-
    New denominator:

      d = 2 * (c + 2^k - 1).
    -/
    let d : ℕ :=
      2 * (c + 2 ^ k - 1)

    have hpowpos :
        0 < 2 ^ k := by
      positivity

    have hsumone :
        1 ≤ c + 2 ^ k := by
      omega

    have hinnerpos :
        0 < c + 2 ^ k - 1 := by
      omega

    have hdpos :
        0 < d := by
      dsimp [d]
      omega

    have hcQ :
        (c : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hcpos)

    have hinnerCast :
        (((c + 2 ^ k - 1 : ℕ) : ℚ))
          =
        (c : ℚ) + (2 : ℚ) ^ k - 1 := by

      rw [Nat.cast_sub hsumone]

      norm_num

    have hinnerQ :
        (c : ℚ) + (2 : ℚ) ^ k - 1 ≠ 0 := by

      have hp :
          0 <
            (((c + 2 ^ k - 1 : ℕ) : ℚ)) := by
        exact_mod_cast hinnerpos

      rw [hinnerCast] at hp

      exact ne_of_gt hp

    have hdcast :
        (d : ℚ)
          =
        2 *
          ((c : ℚ) +
            (2 : ℚ) ^ k - 1) := by

      dsimp [d]

      rw [Nat.cast_mul]
      rw [Nat.cast_sub hsumone]

      norm_num

    have hid :
        target (k + 1) (2 * c)
          =
        target k c * factor d := by

      unfold target factor

      push_cast

      rw [hdcast]

      exact
        even_identity_rat
          k
          (c : ℚ)
          hcQ
          hinnerQ

    refine
      ⟨ms ++ [d], ?_, ?_, ?_⟩

    · simp [hlen]

    · intro x hx

      simp only [
        List.mem_append,
        List.mem_singleton
      ] at hx

      rcases hx with hx | hx

      · exact hpositive x hx

      · subst x
        exact hdpos

    · rw [
        List.map_append,
        List.prod_append
      ]

      simp only [
        List.map_singleton,
        List.prod_singleton
      ]

      rw [hprod]

      exact hid.symm

  /- ============================================================
     Odd case: n = 2*c+1
     ============================================================ -/
  · subst n

    have hc1pos :
        0 < c + 1 := by
      omega

    obtain ⟨ms, hlen, hpositive, hprod⟩ :=
      ih (c + 1) hc1pos

    let d : ℕ :=
      2 * c + 1

    have hdpos :
        0 < d := by
      dsimp [d]
      omega

    have hc1Q :
        (c : ℚ) + 1 ≠ 0 := by

      have h :
          0 < (c : ℚ) + 1 := by
        positivity

      exact ne_of_gt h

    have hdQ :
        2 * (c : ℚ) + 1 ≠ 0 := by

      have h :
          0 < 2 * (c : ℚ) + 1 := by
        positivity

      exact ne_of_gt h

    have hdcast :
        (d : ℚ) =
          2 * (c : ℚ) + 1 := by

      dsimp [d]
      norm_num

    have hid :
        target (k + 1) (2 * c + 1)
          =
        target k (c + 1) *
          factor d := by

      unfold target factor

      push_cast

      rw [hdcast]

      exact
        odd_identity_rat
          k
          (c : ℚ)
          hc1Q
          hdQ

    refine
      ⟨ms ++ [d], ?_, ?_, ?_⟩

    · simp [hlen]

    · intro x hx

      simp only [
        List.mem_append,
        List.mem_singleton
      ] at hx

      rcases hx with hx | hx

      · exact hpositive x hx

      · subst x
        exact hdpos

    · rw [
        List.map_append,
        List.prod_append
      ]

      simp only [
        List.map_singleton,
        List.prod_singleton
      ]

      rw [hprod]

      exact hid.symm

/-!
## Main induction
-/

/--
For every positive `k,n`, the required list of denominators exists.
-/
theorem imo2013_p1
    (k n : ℕ)
    (hk : 0 < k)
    (hn : 0 < n) :
    Works k n := by

  have hmain :
      ∀ r : ℕ,
        ∀ n : ℕ,
          0 < n →
          Works (r + 1) n := by

    intro r

    induction r with

    | zero =>

        intro n hn

        simpa using
          works_one n hn

    | succ r ihr =>

        intro n hn

        have ih' :
            ∀ t : ℕ,
              0 < t →
              Works (r + 1) t := by

          intro t ht

          exact ihr t ht

        have hs :
            Works ((r + 1) + 1) n :=
          works_succ
            (r + 1)
            ih'
            n
            hn

        simpa [Nat.add_assoc] using hs

  cases k with

  | zero =>
      omega

  | succ r =>

      have h :
          Works (r + 1) n :=
        hmain r n hn

      simpa [Nat.succ_eq_add_one] using h

/-!
## Literal statement with the product written out
-/

/--
Expanded form of the IMO statement.

There is a list of exactly `k` positive integers and

    ∏ (1 + 1/m) =
      1 + (2^k - 1)/n.
-/
theorem imo2013_p1_explicit
    (k n : ℕ)
    (hk : 0 < k)
    (hn : 0 < n) :
    ∃ ms : List ℕ,
      ms.length = k ∧
      (∀ m ∈ ms, 0 < m) ∧
      (ms.map
          (fun m : ℕ =>
            (1 : ℚ) + 1 / (m : ℚ))).prod
        =
      1 +
        ((2 : ℚ) ^ k - 1) /
          (n : ℚ) := by

  obtain ⟨ms, hlen, hpos, hprod⟩ :=
    imo2013_p1
      k
      n
      hk
      hn

  refine
    ⟨ms, hlen, hpos, ?_⟩

  change
    (ms.map factor).prod =
      target k n

  exact hprod

end IMO2013P1
