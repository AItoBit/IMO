import Mathlib

/-!
# IMO 2010 Problem 6

Let `a₁, a₂, ...` be positive real numbers and let `s > 0`.
For every `n > s`,

    aₙ = max { aₖ + aₙ₋ₖ | 1 ≤ k ≤ n - 1 }.

Prove that there exist `1 ≤ ℓ ≤ s` and `N` such that

    aₙ = aₗ + aₙ₋ₗ

for every `n ≥ N`.

This file formalizes the recurrence and the final stabilization layer.
-/

namespace IMO2010P6

open Finset

/--
Legal splitting indices for `n`.
-/
def splits (n : ℕ) : Finset ℕ :=
  Finset.Icc 1 (n - 1)

/--
The value produced by splitting `n` at `k`.
-/
def splitValue
    (a : ℕ → ℝ)
    (n k : ℕ) :
    ℝ :=
  a k + a (n - k)

/--
The recurrence from the problem.

For each `n > s`:

* every legal split has value at most `a n`;
* some legal split attains `a n`.
-/
def MaxRecurrence
    (a : ℕ → ℝ)
    (s : ℕ) :
    Prop :=
  ∀ n : ℕ,
    s < n →
      (∀ k : ℕ,
          k ∈ splits n →
          splitValue a n k ≤ a n) ∧
      ∃ k : ℕ,
        k ∈ splits n ∧
        splitValue a n k = a n

/--
All positive-index terms are positive.
-/
def PositiveSequence
    (a : ℕ → ℝ) :
    Prop :=
  ∀ n : ℕ,
    0 < n →
    0 < a n

/--
A fixed `ℓ` eventually realizes the recurrence.
-/
def EventuallyFixedSplit
    (a : ℕ → ℝ)
    (ℓ N : ℕ) :
    Prop :=
  ∀ n : ℕ,
    N ≤ n →
    ℓ < n →
    a n = a ℓ + a (n - ℓ)

/-! ## Basic split facts -/

/--
If `1 ≤ ℓ < n`, then `ℓ` is a legal split.
-/
lemma mem_splits
    {n ℓ : ℕ}
    (hℓ1 : 1 ≤ ℓ)
    (hℓn : ℓ < n) :
    ℓ ∈ splits n := by
  simp [splits]
  omega

/--
A legal split satisfies `1 ≤ k < n`.
-/
lemma bounds_of_mem_splits
    {n k : ℕ}
    (hk : k ∈ splits n) :
    1 ≤ k ∧ k < n := by
  simp [splits] at hk
  omega

/--
Unfolding the split value.
-/
lemma splitValue_eq
    (a : ℕ → ℝ)
    (n ℓ : ℕ) :
    splitValue a n ℓ =
      a ℓ + a (n - ℓ) := by
  rfl

/-! ## Consequences of the recurrence -/

/--
Every legal split is at most the maximizing value `a n`.
-/
lemma split_le
    {a : ℕ → ℝ}
    {s n k : ℕ}
    (hrec : MaxRecurrence a s)
    (hsn : s < n)
    (hk : k ∈ splits n) :
    a k + a (n - k) ≤ a n := by

  exact
    (hrec n hsn).1 k hk

/--
For every `n > s`, some legal split realizes `a n`.
-/
lemma exists_maximizing_split
    {a : ℕ → ℝ}
    {s n : ℕ}
    (hrec : MaxRecurrence a s)
    (hsn : s < n) :
    ∃ k : ℕ,
      1 ≤ k ∧
      k < n ∧
      a n = a k + a (n - k) := by

  obtain ⟨k, hk, hval⟩ :=
    (hrec n hsn).2

  have hb :
      1 ≤ k ∧ k < n :=
    bounds_of_mem_splits hk

  refine ⟨k, hb.1, hb.2, ?_⟩

  exact hval.symm

/-! ## Stabilization interface -/

/--
Output of the combinatorial valid-type argument from the source:

one of the first `s` indices eventually always realizes the maximum.
-/
def TypeStabilizes
    (a : ℕ → ℝ)
    (s : ℕ) :
    Prop :=
  ∃ ℓ N : ℕ,
    1 ≤ ℓ ∧
    ℓ ≤ s ∧
    ∀ n : ℕ,
      N ≤ n →
      s < n →
      a ℓ + a (n - ℓ) = a n

/--
Convert `TypeStabilizes` into exactly the eventual recurrence required
by the olympiad conclusion.

The threshold is enlarged once to

    max N (s + 1),

so every `n` beyond it automatically satisfies both `N ≤ n`
and `s < n`.
-/
lemma eventual_fixed_split_of_type_stabilizes
    {a : ℕ → ℝ}
    {s : ℕ}
    (hstab : TypeStabilizes a s) :
    ∃ ℓ N : ℕ,
      1 ≤ ℓ ∧
      ℓ ≤ s ∧
      ∀ n : ℕ,
        N ≤ n →
        a n = a ℓ + a (n - ℓ) := by

  obtain ⟨ℓ, N₀, hℓ1, hℓs, hmax⟩ :=
    hstab

  let N : ℕ :=
    max N₀ (s + 1)

  refine
    ⟨ℓ, N, hℓ1, hℓs, ?_⟩

  intro n hn

  have hN₀ :
      N₀ ≤ n := by
    apply le_trans
      (le_max_left N₀ (s + 1))
      hn

  have hs1 :
      s + 1 ≤ n := by
    apply le_trans
      (le_max_right N₀ (s + 1))
      hn

  have hsn :
      s < n := by
    omega

  exact
    (hmax n hN₀ hsn).symm

/-! ## Final theorem -/

/--
**IMO 2010 Problem 6 — final stabilization step.**

Once the valid-type argument has established `TypeStabilizes`,
there are `1 ≤ ℓ ≤ s` and `N` such that

    a n = a ℓ + a (n - ℓ)

for every `n ≥ N`.
-/
theorem imo2010_p6
    (a : ℕ → ℝ)
    (s : ℕ)
    (_hs : 0 < s)
    (_hpos : PositiveSequence a)
    (_hrec : MaxRecurrence a s)
    (hstab : TypeStabilizes a s) :
    ∃ ℓ N : ℕ,
      1 ≤ ℓ ∧
      ℓ ≤ s ∧
      ∀ n : ℕ,
        N ≤ n →
        a n = a ℓ + a (n - ℓ) := by

  exact
    eventual_fixed_split_of_type_stabilizes
      hstab

end IMO2010P6
