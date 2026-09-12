import Mathlib

/-!
# IMO 1992, Problem 6

For a positive integer `n`, `S n` is the greatest integer such that for every `k ≤ S n`, `n²` is
a sum of `k` positive squares.

* (a) `S n ≤ n² - 14` for `n ≥ 4`.
* (b) find `n` with `S n = n² - 14`.
* (c) there are infinitely many such `n`.

## What is in this file

Part (a) is proved in full, with no `sorry`, as `part_a`. The construction lemma
`rep_of_two_three` — which supplies the positive direction for most `k` — is also proved.

Parts (b) and (c) are **not** proved here; see the note at the end of the file for exactly what
is missing.

## Part (a)

If `n² = a₁² + ⋯ + a_k²` with every `aᵢ ≥ 1`, then `n² - k = Σ (aᵢ² - 1)`, a sum of elements of
`{x² - 1 : x ≥ 2} = {3, 8, 15, 24, …}`. For `k = n² - 13` this would make `13` such a sum. Every
term is at most `13`, hence lies in `{0, 3, 8}`, and `3a + 8b = 13` has no solution in
non-negative integers. So `n²` is not a sum of `n² - 13` positive squares, and since `S n`
requires *every* `k ≤ S n` to work, `S n < n² - 13`.
-/

open Finset

namespace Imo1992P6

/-- `n²` is a sum of exactly `k` positive squares. -/
def Rep (n k : ℕ) : Prop :=
  ∃ f : ℕ → ℕ, (∀ i < k, 0 < f i) ∧ ∑ i ∈ Finset.range k, (f i) ^ 2 = n ^ 2

/-- `m` is a valid value for the "greatest" in the definition of `S n`. -/
def Good (n m : ℕ) : Prop := ∀ k, 1 ≤ k → k ≤ m → Rep n k

/-! ### The numerical semigroup step -/

/-- A sum whose terms all lie in `{0, 3, 8}` is a non-negative combination of `3` and `8`. -/
theorem sum_semigroup (s : Finset ℕ) (g : ℕ → ℕ) :
    (∀ i ∈ s, g i = 0 ∨ g i = 3 ∨ g i = 8) → ∃ a b : ℕ, ∑ i ∈ s, g i = 3 * a + 8 * b := by
  classical
  refine Finset.induction_on s ?_ ?_
  · intro _
    exact ⟨0, 0, by simp⟩
  · intro x t hx ih hall
    obtain ⟨a, b, hab⟩ := ih fun i hi => hall i (Finset.mem_insert_of_mem hi)
    rw [Finset.sum_insert hx]
    rcases hall x (Finset.mem_insert_self x t) with h0 | h3 | h8
    · exact ⟨a, b, by rw [h0, hab]; ring⟩
    · exact ⟨a + 1, b, by rw [h3, hab]; ring⟩
    · exact ⟨a, b + 1, by rw [h8, hab]; ring⟩

/-! ### `n²` is not a sum of `n² - 13` positive squares -/

theorem not_rep_thirteen (n k : ℕ) (hk : k + 13 = n ^ 2) : ¬ Rep n k := by
  rintro ⟨f, hpos, hsum⟩
  -- rewrite the sum of squares as `Σ (aᵢ² - 1) + k`
  have hstep : ∑ i ∈ Finset.range k, (f i) ^ 2
      = (∑ i ∈ Finset.range k, ((f i) ^ 2 - 1)) + k := by
    have hcongr : ∑ i ∈ Finset.range k, (f i) ^ 2
        = ∑ i ∈ Finset.range k, (((f i) ^ 2 - 1) + 1) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have h1 := hpos i (Finset.mem_range.1 hi)
      have h2 : 1 ≤ (f i) ^ 2 := Nat.one_le_pow 2 (f i) h1
      omega
    rw [hcongr, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
  have hG : ∑ i ∈ Finset.range k, ((f i) ^ 2 - 1) = 13 := by omega
  -- every term is at most 13, hence lies in `{0, 3, 8}`
  have hmem : ∀ i ∈ Finset.range k, ((f i) ^ 2 - 1) = 0 ∨ ((f i) ^ 2 - 1) = 3
      ∨ ((f i) ^ 2 - 1) = 8 := by
    intro i hi
    have hle : (f i) ^ 2 - 1 ≤ 13 := by
      have := Finset.single_le_sum (f := fun j => (f j) ^ 2 - 1) (fun j _ => Nat.zero_le _) hi
      omega
    have h1 := hpos i (Finset.mem_range.1 hi)
    have hf3 : f i ≤ 3 := by
      by_contra hcon
      rw [Nat.not_le] at hcon
      have : 4 ^ 2 ≤ (f i) ^ 2 := Nat.pow_le_pow_left hcon 2
      omega
    interval_cases h : f i <;> simp_all
  obtain ⟨a, b, hab⟩ := sum_semigroup _ _ hmem
  omega

/-! ### Part (a) -/

theorem part_a (n : ℕ) (hn : 4 ≤ n) (m : ℕ) (hm : Good n m) : m ≤ n ^ 2 - 14 := by
  by_contra hcon
  rw [Nat.not_le] at hcon
  have hn2 : 16 ≤ n ^ 2 := by nlinarith
  exact not_rep_thirteen n (n ^ 2 - 13) (by omega) (hm _ (by omega) (by omega))

/-! ### The construction supplying most `k` -/

/-- Merging `a` groups of four `1`s into `2`s and `b` groups of nine `1`s into `3`s turns the
representation `n² = 1² + ⋯ + 1²` into one with `n² - (3a + 8b)` positive squares. -/
theorem rep_of_two_three (n a b : ℕ) (h : 4 * a + 9 * b ≤ n ^ 2) :
    Rep n (n ^ 2 - (3 * a + 8 * b)) := by
  classical
  set k : ℕ := n ^ 2 - (3 * a + 8 * b) with hk
  have hab : a + b ≤ k := by omega
  refine ⟨fun i => if i < a then 2 else if i < a + b then 3 else 1, ?_, ?_⟩
  · intro i _
    dsimp only
    split_ifs <;> omega
  · have hsplit : ∑ i ∈ Finset.range k,
        ((if i < a then 2 else if i < a + b then 3 else 1) : ℕ) ^ 2
        = (∑ i ∈ Finset.Ico 0 a, ((if i < a then 2 else if i < a + b then 3 else 1) : ℕ) ^ 2)
          + (∑ i ∈ Finset.Ico a (a + b), ((if i < a then 2 else if i < a + b then 3 else 1) : ℕ) ^ 2)
          + (∑ i ∈ Finset.Ico (a + b) k,
              ((if i < a then 2 else if i < a + b then 3 else 1) : ℕ) ^ 2) := by
      rw [Finset.range_eq_Ico]
      rw [← Finset.sum_Ico_consecutive _ (Nat.zero_le a) (le_trans (Nat.le_add_right a b) hab),
        ← Finset.sum_Ico_consecutive _ (Nat.le_add_right a b) hab]
      ring
    have h1 : ∑ i ∈ Finset.Ico 0 a,
        ((if i < a then 2 else if i < a + b then 3 else 1) : ℕ) ^ 2 = 4 * a := by
      have hc : ∀ i ∈ Finset.Ico 0 a,
          ((if i < a then 2 else if i < a + b then 3 else 1) : ℕ) ^ 2 = 4 := by
        intro i hi
        rw [Finset.mem_Ico] at hi
        simp [hi.2]
      calc ∑ i ∈ Finset.Ico 0 a, ((if i < a then 2 else if i < a + b then 3 else 1) : ℕ) ^ 2
          = ∑ _i ∈ Finset.Ico 0 a, (4 : ℕ) := Finset.sum_congr rfl hc
        _ = 4 * a := by rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul]; omega
    have h2 : ∑ i ∈ Finset.Ico a (a + b),
        ((if i < a then 2 else if i < a + b then 3 else 1) : ℕ) ^ 2 = 9 * b := by
      have hc : ∀ i ∈ Finset.Ico a (a + b),
          ((if i < a then 2 else if i < a + b then 3 else 1) : ℕ) ^ 2 = 9 := by
        intro i hi
        rw [Finset.mem_Ico] at hi
        have hia : ¬ i < a := by omega
        simp [hia, hi.2]
      calc ∑ i ∈ Finset.Ico a (a + b),
            ((if i < a then 2 else if i < a + b then 3 else 1) : ℕ) ^ 2
          = ∑ _i ∈ Finset.Ico a (a + b), (9 : ℕ) := Finset.sum_congr rfl hc
        _ = 9 * b := by rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul]; omega
    have h3 : ∑ i ∈ Finset.Ico (a + b) k,
        ((if i < a then 2 else if i < a + b then 3 else 1) : ℕ) ^ 2 = k - (a + b) := by
      have hc : ∀ i ∈ Finset.Ico (a + b) k,
          ((if i < a then 2 else if i < a + b then 3 else 1) : ℕ) ^ 2 = 1 := by
        intro i hi
        rw [Finset.mem_Ico] at hi
        have hia : ¬ i < a := by omega
        have hib : ¬ i < a + b := by omega
        simp [hia, hib]
      calc ∑ i ∈ Finset.Ico (a + b) k,
            ((if i < a then 2 else if i < a + b then 3 else 1) : ℕ) ^ 2
          = ∑ _i ∈ Finset.Ico (a + b) k, (1 : ℕ) := Finset.sum_congr rfl hc
        _ = k - (a + b) := by rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul]; omega
    rw [hsplit, h1, h2, h3]
    omega

/-!
### Status of parts (b) and (c)

Both remaining parts need the *positive* direction: that `n²` really is a sum of `k` positive
squares for every `k ≤ n² - 14`.

`rep_of_two_three` handles every `k` for which `n² - k` can be written as `3a + 8b` with
`4a + 9b ≤ n²`. Since `13` is the Frobenius number of `⟨3, 8⟩`, each `Δ = n² - k ≥ 14` is
`3a + 8b` for some `a, b`; the constraint `4a + 9b ≤ n²`, i.e. `Δ + a + b ≤ n²`, holds once
`Δ ≲ (8/9) n²`, that is for all but the smallest values of `k`.

What is missing is exactly the small-`k` range, where `n²` must be a sum of very few positive
squares:

* `k = 2` needs `n²` to be a sum of two positive squares, so `n` needs a prime factor `≡ 1 mod 4`;
* `k = 3` needs `n²` to be a sum of three positive squares. The AoPS argument invokes Legendre's
  **three-square theorem**, which Mathlib does not have. (Mathlib has Lagrange's four-square
  theorem, `Nat.sum_four_squares`, but no three-square theorem.)

For part (b) with `n = 13` the small range is finite — the `k ≤ 18` cases — so it can be closed
by exhibiting eighteen explicit representations of `169`. For part (c) the small range must be
handled uniformly in `n`; picking `n` in a family such as `n = 15m` gives `k = 2` and `k = 3`
directly, via `(15m)² = (9m)² + (12m)²` and `(15m)² = (10m)² + (10m)² + (5m)²`, avoiding the
three-square theorem, but the intermediate `k` still need a chain of splitting steps.
-/

end Imo1992P6
