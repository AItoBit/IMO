/-
# IMO 1972, Problem 1

Prove that from a set of ten distinct two-digit numbers it is possible to select
two disjoint (nonempty) subsets whose members have the same sum.

## Modelling

A set of ten distinct two-digit numbers is a `S : Finset ℕ` with `S.card = 10`
and `10 ≤ n ≤ 99` for every `n ∈ S`.

## Proof

Pigeonhole on `T ↦ ∑ x ∈ T, x` over the `2 ^ 10 = 1024` subsets of `S`.  Every
such sum is at most `10 * 99 = 990`, so it lands in `Finset.range 991`, and
`991 < 1024`.  Hence there are two **distinct** subsets `A ≠ B` of `S` with the
same sum.

Take `A \ B` and `B \ A`.  They are disjoint, and subtracting the common part
`A ∩ B` from both sides of `∑ A = ∑ B` shows their sums agree.  They are
nonempty: if `A \ B = ∅` then `A ⊆ B`, so `∑ (B \ A) = 0`; every element of `S`
is at least `10`, so `B \ A = ∅` too, giving `A = B`, a contradiction.

(The AoPS write-up counts `2 ^ 10 - 2 = 1022` nonempty proper subsets and bounds
the sums by `1000`; using all `1024` subsets and the sharper bound `990` avoids
having to exclude `∅` and `S` up front.)
-/

import Mathlib

namespace Imo1972P1

/-- Splitting a sum along an intersection. -/
private lemma sum_split (X Y : Finset ℕ) :
    ∑ x ∈ X \ Y, x + ∑ x ∈ X ∩ Y, x = ∑ x ∈ X, x := by
  have hsub : X ∩ Y ⊆ X := Finset.inter_subset_left
  have hs := Finset.sum_sdiff (f := fun x => x) hsub
  have hXY : X \ (X ∩ Y) = X \ Y := by
    ext a
    simp only [Finset.mem_sdiff, Finset.mem_inter]
    tauto
  rwa [hXY] at hs

/-- If `A ≠ B` are subsets of `S` with equal sums, then `A \ B` is nonempty. -/
private lemma nonempty_sdiff {S A B : Finset ℕ} (hS : ∀ n ∈ S, 10 ≤ n ∧ n ≤ 99)
    (hA : A ⊆ S) (hB : B ⊆ S) (hne : A ≠ B) (hsum : ∑ x ∈ A, x = ∑ x ∈ B, x) :
    (A \ B).Nonempty := by
  classical
  rw [Finset.nonempty_iff_ne_empty]
  intro hemp
  have hsub : A ⊆ B := Finset.sdiff_eq_empty_iff_subset.mp hemp
  have h1 : ∑ x ∈ B \ A, x + ∑ x ∈ B ∩ A, x = ∑ x ∈ B, x := sum_split B A
  have h2 : B ∩ A = A := Finset.inter_eq_right.mpr hsub
  rw [h2, ← hsum] at h1
  have h3 : ∑ x ∈ B \ A, x = 0 := by omega
  have h4 : B \ A = ∅ := by
    by_contra hcon
    obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hcon
    have hx0 : x = 0 := Finset.sum_eq_zero_iff.mp h3 x hx
    have hxS : x ∈ S := hB (Finset.mem_sdiff.mp hx).1
    have := (hS x hxS).1
    omega
  exact hne (Finset.Subset.antisymm hsub (Finset.sdiff_eq_empty_iff_subset.mp h4))

/-- **IMO 1972, Problem 1.** -/
theorem imo1972_p1 (S : Finset ℕ) (hcard : S.card = 10)
    (hS : ∀ n ∈ S, 10 ≤ n ∧ n ≤ 99) :
    ∃ A B : Finset ℕ, A ⊆ S ∧ B ⊆ S ∧ A.Nonempty ∧ B.Nonempty ∧
      Disjoint A B ∧ ∑ x ∈ A, x = ∑ x ∈ B, x := by
  classical
  -- every subset sum is at most `10 * 99 = 990`
  have hmaps : ∀ T ∈ S.powerset, (∑ x ∈ T, x) ∈ Finset.range 991 := by
    intro T hT
    rw [Finset.mem_powerset] at hT
    rw [Finset.mem_range]
    have h1 : ∑ x ∈ T, x ≤ T.card * 99 := by
      have h := Finset.sum_le_card_nsmul T (fun x => x) 99 fun x hx => (hS x (hT hx)).2
      simpa [smul_eq_mul] using h
    have h2 : T.card ≤ 10 := by
      rw [← hcard]; exact Finset.card_le_card hT
    omega
  -- there are more subsets than possible sums
  have hlt : (Finset.range 991).card < S.powerset.card := by
    rw [Finset.card_range, Finset.card_powerset, hcard]
    norm_num
  obtain ⟨A, hAmem, B, hBmem, hne, hsum⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt hmaps
  rw [Finset.mem_powerset] at hAmem hBmem
  refine ⟨A \ B, B \ A, Finset.sdiff_subset.trans hAmem, Finset.sdiff_subset.trans hBmem,
    nonempty_sdiff hS hAmem hBmem hne hsum,
    nonempty_sdiff hS hBmem hAmem (Ne.symm hne) hsum.symm, ?_, ?_⟩
  · -- disjointness
    rw [Finset.disjoint_left]
    intro a ha hb
    exact (Finset.mem_sdiff.mp ha).2 (Finset.mem_sdiff.mp hb).1
  · -- equal sums
    have h1 : ∑ x ∈ A \ B, x + ∑ x ∈ A ∩ B, x = ∑ x ∈ A, x := sum_split A B
    have h2 : ∑ x ∈ B \ A, x + ∑ x ∈ B ∩ A, x = ∑ x ∈ B, x := sum_split B A
    have h3 : B ∩ A = A ∩ B := Finset.inter_comm B A
    rw [h3] at h2
    omega

end Imo1972P1
