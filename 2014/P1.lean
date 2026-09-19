import Mathlib

namespace IMO2014P1

open Finset
open scoped BigOperators

def partialSum
    (a : ℕ → ℕ)
    (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1), a i

def F
    (a : ℕ → ℕ)
    (n : ℕ) : ℤ :=
  (partialSum a n : ℤ) -
    (n : ℤ) * (a (n + 1) : ℤ)

def G
    (a : ℕ → ℕ)
    (n : ℕ) : ℤ :=
  (partialSum a n : ℤ) -
    (n : ℤ) * (a n : ℤ)

def GoodIndex
    (a : ℕ → ℕ)
    (n : ℕ) : Prop :=
  0 < n ∧
  (n : ℤ) * (a n : ℤ) <
      (partialSum a n : ℤ) ∧
  (partialSum a n : ℤ) ≤
      (n : ℤ) * (a (n + 1) : ℤ)

lemma F_succ
    (a : ℕ → ℕ)
    (n : ℕ) :
    F a (n + 1)
      =
    F a n -
      ((n + 1 : ℕ) : ℤ) *
        ((a (n + 2) : ℤ) -
         (a (n + 1) : ℤ)) := by
  unfold F partialSum
  rw [Finset.sum_range_succ]
  push_cast
  ring

lemma G_succ_eq_F
    (a : ℕ → ℕ)
    (n : ℕ) :
    G a (n + 1) = F a n := by
  unfold G F partialSum
  rw [Finset.sum_range_succ]
  push_cast
  ring

lemma F_zero
    (a : ℕ → ℕ) :
    F a 0 = (a 0 : ℤ) := by
  simp [F, partialSum]

lemma integer_gap_ge_one
    (a : ℕ → ℕ)
    (hinc :
      ∀ n : ℕ,
        a n < a (n + 1))
    (n : ℕ) :
    (1 : ℤ) ≤
      (a (n + 2) : ℤ) -
      (a (n + 1) : ℤ) := by

  have hlt :
      a (n + 1) < a (n + 2) :=
    hinc (n + 1)

  have hltZ :
      (a (n + 1) : ℤ) <
        (a (n + 2) : ℤ) := by
    exact_mod_cast hlt

  omega

lemma F_succ_le_sub_one
    (a : ℕ → ℕ)
    (hinc :
      ∀ n : ℕ,
        a n < a (n + 1))
    (n : ℕ) :
    F a (n + 1) ≤ F a n - 1 := by

  have hgap :
      (1 : ℤ) ≤
        (a (n + 2) : ℤ) -
        (a (n + 1) : ℤ) :=
    integer_gap_ge_one
      a hinc n

  have hn :
      (1 : ℤ) ≤
        ((n + 1 : ℕ) : ℤ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)

  have hnonneg :
      (0 : ℤ) ≤
        ((n + 1 : ℕ) : ℤ) := by
    exact_mod_cast Nat.zero_le (n + 1)

  have hprod :
      (1 : ℤ) ≤
        ((n + 1 : ℕ) : ℤ) *
          ((a (n + 2) : ℤ) -
           (a (n + 1) : ℤ)) := by

    calc
      (1 : ℤ)
          = 1 * 1 := by
              norm_num

      _ ≤
        ((n + 1 : ℕ) : ℤ) * 1 := by
          exact
            mul_le_mul_of_nonneg_right
              hn
              (by norm_num)

      _ ≤
        ((n + 1 : ℕ) : ℤ) *
          ((a (n + 2) : ℤ) -
           (a (n + 1) : ℤ)) := by
          exact
            mul_le_mul_of_nonneg_left
              hgap
              hnonneg

  rw [F_succ]

  linarith

lemma F_succ_le
    (a : ℕ → ℕ)
    (hinc :
      ∀ n : ℕ,
        a n < a (n + 1))
    (n : ℕ) :
    F a (n + 1) ≤ F a n := by

  have h :=
    F_succ_le_sub_one
      a hinc n

  linarith

lemma F_le_start_sub
    (a : ℕ → ℕ)
    (hinc :
      ∀ n : ℕ,
        a n < a (n + 1)) :
    ∀ n : ℕ,
      F a n ≤
        (a 0 : ℤ) - (n : ℤ) := by

  intro n

  induction n with

  | zero =>
      rw [F_zero]
      norm_num

  | succ n ih =>

      have hs :
          F a (n + 1)
            ≤
          F a n - 1 :=
        F_succ_le_sub_one
          a hinc n

      calc
        F a (n + 1)
            ≤
          F a n - 1 :=
            hs

        _ ≤
          ((a 0 : ℤ) - (n : ℤ)) - 1 := by
            exact
              sub_le_sub_right
                ih
                1

        _ =
          (a 0 : ℤ) -
            ((n + 1 : ℕ) : ℤ) := by
              push_cast
              ring

lemma F_antitone
    (a : ℕ → ℕ)
    (hinc :
      ∀ n : ℕ,
        a n < a (n + 1))
    {n m : ℕ}
    (hnm :
      n ≤ m) :
    F a m ≤ F a n := by

  induction hnm with

  | refl =>
      exact le_rfl

  | @step m hnm ih =>
      have hs :
          F a (m + 1) ≤ F a m :=
        F_succ_le
          a
          hinc
          m

      exact
        le_trans
          hs
          ih

lemma G_pos_of_good
    {a : ℕ → ℕ}
    {n : ℕ}
    (h :
      GoodIndex a n) :
    0 < G a n := by

  rcases h with
    ⟨_hn, hleft, _hright⟩

  unfold G

  linarith

lemma F_nonpos_of_good
    {a : ℕ → ℕ}
    {n : ℕ}
    (h :
      GoodIndex a n) :
    F a n ≤ 0 := by

  rcases h with
    ⟨_hn, _hleft, hright⟩

  unfold F

  linarith

lemma goodIndex_unique
    (a : ℕ → ℕ)
    (hinc :
      ∀ n : ℕ,
        a n < a (n + 1))
    {n m : ℕ}
    (hn :
      GoodIndex a n)
    (hm :
      GoodIndex a m) :
    n = m := by

  by_contra hne

  rcases lt_or_gt_of_ne hne with hnm | hmn

  · have hFn :
        F a n ≤ 0 :=
      F_nonpos_of_good hn

    have hGm :
        0 < G a m :=
      G_pos_of_good hm

    have hmpos :
        0 < m :=
      hm.1

    obtain ⟨r, hr⟩ :
        ∃ r : ℕ,
          m = r + 1 := by

      cases m with

      | zero =>
          omega

      | succ r =>
          exact ⟨r, rfl⟩

    have hnr :
        n ≤ r := by
      omega

    have hFrn :
        F a r ≤ F a n :=
      F_antitone
        a
        hinc
        hnr

    rw [hr, G_succ_eq_F] at hGm

    linarith

  · have hFm :
        F a m ≤ 0 :=
      F_nonpos_of_good hm

    have hGn :
        0 < G a n :=
      G_pos_of_good hn

    have hnpos :
        0 < n :=
      hn.1

    obtain ⟨r, hr⟩ :
        ∃ r : ℕ,
          n = r + 1 := by

      cases n with

      | zero =>
          omega

      | succ r =>
          exact ⟨r, rfl⟩

    have hmr :
        m ≤ r := by
      omega

    have hFrm :
        F a r ≤ F a m :=
      F_antitone
        a
        hinc
        hmr

    rw [hr, G_succ_eq_F] at hGn

    linarith

lemma exists_F_nonpos
    (a : ℕ → ℕ)
    (hinc :
      ∀ n : ℕ,
        a n < a (n + 1)) :
    ∃ n : ℕ,
      F a n ≤ 0 := by

  refine ⟨a 0, ?_⟩

  have h :
      F a (a 0) ≤
        (a 0 : ℤ) - (a 0 : ℤ) :=
    F_le_start_sub
      a
      hinc
      (a 0)

  norm_num at h ⊢

  exact h

theorem imo2014_p1
    (a : ℕ → ℕ)
    (hpos :
      ∀ n : ℕ,
        0 < a n)
    (hinc :
      ∀ n : ℕ,
        a n < a (n + 1)) :
    ∃! n : ℕ,
      GoodIndex a n := by

  have hex :
      ∃ n : ℕ,
        F a n ≤ 0 :=
    exists_F_nonpos
      a
      hinc

  let N : ℕ :=
    Nat.find hex

  have hFN :
      F a N ≤ 0 := by

    dsimp [N]

    exact
      Nat.find_spec hex

  have hNpos :
      0 < N := by

    by_contra hnot

    have hNzero :
        N = 0 := by
      omega

    have hFzero :
        F a 0 = (a 0 : ℤ) :=
      F_zero a

    have ha0 :
        (0 : ℤ) < (a 0 : ℤ) := by
      exact_mod_cast hpos 0

    rw [hNzero, hFzero] at hFN

    linarith

  have hFpred :
      0 < F a (N - 1) := by

    by_contra hnot

    have hp :
        F a (N - 1) ≤ 0 := by
      exact le_of_not_gt hnot

    have hmin :
        N ≤ N - 1 := by

      dsimp [N]

      exact
        Nat.find_min'
          hex
          hp

    omega

  have hNsucc :
      N = (N - 1) + 1 := by
    omega

  have hG :
      0 < G a N := by

    rw [hNsucc]
    rw [G_succ_eq_F]

    exact hFpred

  have hGood :
      GoodIndex a N := by

    refine ⟨hNpos, ?_, ?_⟩

    · unfold G at hG

      linarith

    · unfold F at hFN

      linarith

  refine ⟨N, hGood, ?_⟩

  intro m hm

  exact
    goodIndex_unique
      a
      hinc
      hm
      hGood

end IMO2014P1
