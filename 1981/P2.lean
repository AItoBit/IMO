import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Imo1981P2

open Finset

/-- The smallest member of a finite set of naturals (`0` for the empty set). -/
noncomputable def smallest (S : Finset ℕ) : ℕ := S.min.getD 0

/-- For a nonempty subset `S` of `{1, …, n}`, the number of indices `j ∈ {1, …, n}`
with `S ⊆ {j, …, n}` is exactly the smallest member of `S`. -/
lemma card_filter_subset_Icc (n : ℕ) (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 n)
    (hne : S.Nonempty) :
    ((Finset.Icc 1 n).filter (fun j => S ⊆ Finset.Icc j n)).card = smallest S := by
  have hmem : S.min' hne ∈ S := S.min'_mem hne
  have hle : S.min' hne ≤ n := (Finset.mem_Icc.mp (hS hmem)).2
  have hmin : smallest S = S.min' hne := by
    rw [smallest, ← Finset.coe_min' hne]
    rfl
  have hset : (Finset.Icc 1 n).filter (fun j => S ⊆ Finset.Icc j n)
      = Finset.Icc 1 (S.min' hne) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hj1, _⟩, hsub⟩
      exact ⟨hj1, (Finset.mem_Icc.mp (hsub hmem)).1⟩
    · rintro ⟨hj1, hjm⟩
      refine ⟨⟨hj1, le_trans hjm hle⟩, fun x hx => ?_⟩
      refine Finset.mem_Icc.mpr ⟨le_trans hjm (S.min'_le x hx), ?_⟩
      exact (Finset.mem_Icc.mp (hS hx)).2
  rw [hset, hmin, Nat.card_Icc]
  omega

/-- Slicing by the lower bound: the sum of the smallest members equals
`∑_{j=1}^{n} \binom{n+1-j}{r}`. -/
lemma sum_smallest_eq_sum_choose (n r : ℕ) (hr : 1 ≤ r) :
    ∑ S ∈ (Finset.Icc 1 n).powersetCard r, smallest S
      = ∑ j ∈ Finset.Icc 1 n, (n + 1 - j).choose r := by
  have h1 : ∀ S ∈ (Finset.Icc 1 n).powersetCard r,
      smallest S = ∑ j ∈ Finset.Icc 1 n, (if S ⊆ Finset.Icc j n then 1 else 0) := by
    intro S hS
    rw [Finset.mem_powersetCard] at hS
    have hne : S.Nonempty := by
      rw [← Finset.card_pos, hS.2]; omega
    rw [← card_filter_subset_Icc n S hS.1 hne, Finset.card_filter]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro j hj
  have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  have hfil : ((Finset.Icc 1 n).powersetCard r).filter (fun S => S ⊆ Finset.Icc j n)
      = (Finset.Icc j n).powersetCard r := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨_, hcard⟩, hsub⟩
      exact ⟨hsub, hcard⟩
    · rintro ⟨hsub, hcard⟩
      refine ⟨⟨hsub.trans ?_, hcard⟩, hsub⟩
      exact Finset.Icc_subset_Icc_left hj1
  rw [← Finset.card_filter, hfil, Finset.card_powersetCard, Nat.card_Icc]

/-- Hockey-stick: `∑_{j=1}^{n} \binom{n+1-j}{r} = \binom{n+1}{r+1}` for `1 ≤ r`. -/
lemma sum_choose_eq_choose (n r : ℕ) (hr : 1 ≤ r) :
    ∑ j ∈ Finset.Icc 1 n, (n + 1 - j).choose r = (n + 1).choose (r + 1) := by
  have hre : ∑ j ∈ Finset.Icc 1 n, (n + 1 - j).choose r
      = ∑ i ∈ Finset.Icc 1 n, i.choose r := by
    refine Finset.sum_nbij' (fun j => n + 1 - j) (fun i => n + 1 - i) ?_ ?_ ?_ ?_ ?_ <;>
      intro a ha <;> simp only [Finset.mem_Icc] at * <;> omega
  rw [hre]
  have hsub : Finset.Icc r n ⊆ Finset.Icc 1 n := Finset.Icc_subset_Icc_left hr
  have : ∑ i ∈ Finset.Icc 1 n, i.choose r = ∑ i ∈ Finset.Icc r n, i.choose r := by
    refine (Finset.sum_subset hsub ?_).symm
    intro x hx hxn
    simp only [Finset.mem_Icc] at hx hxn
    exact Nat.choose_eq_zero_of_lt (by omega)
  rw [this, Nat.sum_Icc_choose]

/-- The sum of the smallest members of all `r`-element subsets of `{1, …, n}`
is `\binom{n+1}{r+1}`. -/
theorem sum_smallest (n r : ℕ) (hr : 1 ≤ r) :
    ∑ S ∈ (Finset.Icc 1 n).powersetCard r, smallest S = (n + 1).choose (r + 1) := by
  rw [sum_smallest_eq_sum_choose n r hr, sum_choose_eq_choose n r hr]

/-- **IMO 1981, Problem 2.** For `1 ≤ r ≤ n`, the arithmetic mean `F (n, r)` of the smallest
members of all `r`-element subsets of `{1, 2, …, n}` equals `(n + 1) / (r + 1)`. -/
theorem imo1981_p2 (n r : ℕ) (hr : 1 ≤ r) (hrn : r ≤ n) :
    (∑ S ∈ (Finset.Icc 1 n).powersetCard r, (smallest S : ℚ))
        / (((Finset.Icc 1 n).powersetCard r).card : ℚ)
      = ((n : ℚ) + 1) / ((r : ℚ) + 1) := by
  have hcard : ((Finset.Icc 1 n).powersetCard r).card = n.choose r := by
    rw [Finset.card_powersetCard, Nat.card_Icc, Nat.add_sub_cancel]
  have hsum : (∑ S ∈ (Finset.Icc 1 n).powersetCard r, (smallest S : ℚ))
      = ((n + 1).choose (r + 1) : ℚ) := by
    rw [← Nat.cast_sum, sum_smallest n r hr]
  have hkey : (n + 1) * n.choose r = (n + 1).choose (r + 1) * (r + 1) :=
    Nat.add_one_mul_choose_eq n r
  have hne : (n.choose r : ℚ) ≠ 0 := by
    have : 0 < n.choose r := Nat.choose_pos hrn
    positivity
  have hr1 : ((r : ℚ) + 1) ≠ 0 := by positivity
  rw [hsum, hcard]
  rw [div_eq_div_iff hne hr1]
  have := congrArg (fun m : ℕ => (m : ℚ)) hkey
  push_cast at this ⊢
  linarith [this]

end Imo1981P2
