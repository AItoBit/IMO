import Mathlib

/-!
# IMO 1992, Problem 5 (Loomis–Whitney in dimension 3)

`S` is a finite set of points in space; `Sx`, `Sy`, `Sz` are its orthogonal projections onto the
`yz`-, `zx`- and `xy`-planes. Prove `|S|² ≤ |Sx|·|Sy|·|Sz|`.

Points are modelled as triples `(x, y, z)`. Nothing about `ℝ` is used, so the statement is proved
for an arbitrary triple product; `imo1992_p5_real` specialises it to `ℝ × ℝ × ℝ`.

## Proof

Slice `S` by its `z`-coordinate. For a value `c`, let `F c` be the slice, and let `A c`, `B c` be
the parts of `Sx`, `Sy` lying over `c`.

* `|F c| ≤ |A c|·|B c|`, since `p ↦ ((p.y, c), (p.x, c))` is injective on the slice.
* `|F c| ≤ |Sz|`, since `p ↦ (p.x, p.y)` is injective on the slice.
* Hence `|F c| ≤ √|Sz| · √|A c| · √|B c|`, and summing,
  `|S| ≤ √|Sz| · Σ √|A c|·√|B c|`.
* Cauchy–Schwarz gives `(Σ √|A c|·√|B c|)² ≤ (Σ |A c|)(Σ |B c|) = |Sx|·|Sy|`.

Squaring the two displayed inequalities gives `|S|² ≤ |Sz|·|Sx|·|Sy|`.
-/

open Finset

namespace Imo1992P5

theorem imo1992_p5 {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (S : Finset (α × β × γ)) (Sx : Finset (β × γ)) (Sy : Finset (α × γ)) (Sz : Finset (α × β))
    (hSx : Sx = S.image fun p => (p.2.1, p.2.2))
    (hSy : Sy = S.image fun p => (p.1, p.2.2))
    (hSz : Sz = S.image fun p => (p.1, p.2.1)) :
    S.card ^ 2 ≤ Sx.card * Sy.card * Sz.card := by
  classical
  -- the set of `z`-coordinates
  set Z : Finset γ := S.image (fun p : α × β × γ => p.2.2) with hZ
  -- `S` is the disjoint union of its slices
  have hfib : S.card = ∑ c ∈ Z, (S.filter (fun p => p.2.2 = c)).card := by
    refine Finset.card_eq_sum_card_fiberwise ?_
    intro p hp
    rw [Finset.mem_coe] at hp ⊢
    exact hZ ▸ Finset.mem_image_of_mem _ hp
  -- so are `Sx` and `Sy`
  have hSxsum : Sx.card = ∑ c ∈ Z, (Sx.filter (fun q => q.2 = c)).card := by
    refine Finset.card_eq_sum_card_fiberwise ?_
    intro q hq
    rw [Finset.mem_coe, hSx, Finset.mem_image] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    rw [Finset.mem_coe, hZ]
    exact Finset.mem_image_of_mem _ hp
  have hSysum : Sy.card = ∑ c ∈ Z, (Sy.filter (fun q => q.2 = c)).card := by
    refine Finset.card_eq_sum_card_fiberwise ?_
    intro q hq
    rw [Finset.mem_coe, hSy, Finset.mem_image] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    rw [Finset.mem_coe, hZ]
    exact Finset.mem_image_of_mem _ hp
  -- the slice bound
  have hbound : ∀ c : γ, (S.filter (fun p => p.2.2 = c)).card ^ 2
      ≤ ((Sx.filter (fun q => q.2 = c)).card * (Sy.filter (fun q => q.2 = c)).card) * Sz.card := by
    intro c
    have h1 : (S.filter (fun p => p.2.2 = c)).card
        ≤ (Sx.filter (fun q => q.2 = c)).card * (Sy.filter (fun q => q.2 = c)).card := by
      have := Finset.card_le_card_of_injOn
        (s := S.filter (fun p => p.2.2 = c))
        (t := (Sx.filter (fun q => q.2 = c)) ×ˢ (Sy.filter (fun q => q.2 = c)))
        (fun p => ((p.2.1, c), (p.1, c))) ?_ ?_
      · rwa [Finset.card_product] at this
      · intro p hp
        rw [Finset.mem_coe, Finset.mem_filter] at hp
        obtain ⟨hpS, hpc⟩ := hp
        rw [Finset.mem_coe, Finset.mem_product]
        constructor
        · refine Finset.mem_filter.2 ⟨?_, rfl⟩
          have h := Finset.mem_image_of_mem (fun p : α × β × γ => (p.2.1, p.2.2)) hpS
          rw [hpc] at h
          rwa [hSx]
        · refine Finset.mem_filter.2 ⟨?_, rfl⟩
          have h := Finset.mem_image_of_mem (fun p : α × β × γ => (p.1, p.2.2)) hpS
          rw [hpc] at h
          rwa [hSy]
      · intro p hp q hq hpq
        rw [Finset.mem_coe, Finset.mem_filter] at hp hq
        simp only [Prod.mk.injEq] at hpq
        refine Prod.ext_iff.2 ⟨hpq.2.1, Prod.ext_iff.2 ⟨hpq.1.1, ?_⟩⟩
        rw [hp.2, hq.2]
    have h2 : (S.filter (fun p => p.2.2 = c)).card ≤ Sz.card := by
      refine Finset.card_le_card_of_injOn (fun p => (p.1, p.2.1)) ?_ ?_
      · intro p hp
        rw [Finset.mem_coe, Finset.mem_filter] at hp
        rw [Finset.mem_coe, hSz]
        exact Finset.mem_image_of_mem _ hp.1
      · intro p hp q hq hpq
        rw [Finset.mem_coe, Finset.mem_filter] at hp hq
        simp only [Prod.mk.injEq] at hpq
        refine Prod.ext_iff.2 ⟨hpq.1, Prod.ext_iff.2 ⟨hpq.2, ?_⟩⟩
        rw [hp.2, hq.2]
    calc (S.filter (fun p => p.2.2 = c)).card ^ 2
        = (S.filter (fun p => p.2.2 = c)).card * (S.filter (fun p => p.2.2 = c)).card := sq _
      _ ≤ ((Sx.filter (fun q => q.2 = c)).card * (Sy.filter (fun q => q.2 = c)).card) * Sz.card :=
          Nat.mul_le_mul h1 h2
  -- pass to the reals and take square roots slice by slice
  have key : ∀ c ∈ Z, ((S.filter (fun p => p.2.2 = c)).card : ℝ)
      ≤ Real.sqrt (Sz.card) *
        (Real.sqrt ((Sx.filter (fun q => q.2 = c)).card)
          * Real.sqrt ((Sy.filter (fun q => q.2 = c)).card)) := by
    intro c _
    have hb : ((S.filter (fun p => p.2.2 = c)).card : ℝ) ^ 2
        ≤ (Sz.card : ℝ) * ((Sx.filter (fun q => q.2 = c)).card : ℝ)
            * ((Sy.filter (fun q => q.2 = c)).card : ℝ) := by
      have h := (Nat.cast_le (α := ℝ)).2 (hbound c)
      push_cast at h
      linarith
    calc ((S.filter (fun p => p.2.2 = c)).card : ℝ)
        = Real.sqrt (((S.filter (fun p => p.2.2 = c)).card : ℝ) ^ 2) :=
          (Real.sqrt_sq (Nat.cast_nonneg _)).symm
      _ ≤ Real.sqrt ((Sz.card : ℝ) * ((Sx.filter (fun q => q.2 = c)).card : ℝ)
            * ((Sy.filter (fun q => q.2 = c)).card : ℝ)) := Real.sqrt_le_sqrt hb
      _ = Real.sqrt (Sz.card) *
            (Real.sqrt ((Sx.filter (fun q => q.2 = c)).card)
              * Real.sqrt ((Sy.filter (fun q => q.2 = c)).card)) := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]
          ring
  -- sum over the slices
  have hsum : (S.card : ℝ) ≤ Real.sqrt (Sz.card) *
      ∑ c ∈ Z, (Real.sqrt ((Sx.filter (fun q => q.2 = c)).card)
        * Real.sqrt ((Sy.filter (fun q => q.2 = c)).card)) := by
    rw [hfib]
    push_cast
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum key
  -- Cauchy-Schwarz
  have hcs : (∑ c ∈ Z, (Real.sqrt ((Sx.filter (fun q => q.2 = c)).card)
        * Real.sqrt ((Sy.filter (fun q => q.2 = c)).card))) ^ 2
      ≤ (∑ c ∈ Z, ((Sx.filter (fun q => q.2 = c)).card : ℝ))
        * ∑ c ∈ Z, ((Sy.filter (fun q => q.2 = c)).card : ℝ) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Z
      (fun c => Real.sqrt ((Sx.filter (fun q => q.2 = c)).card))
      (fun c => Real.sqrt ((Sy.filter (fun q => q.2 = c)).card))
    simpa [Real.sq_sqrt (Nat.cast_nonneg _)] using h
  -- assemble
  have hT0 : (0 : ℝ) ≤ ∑ c ∈ Z, (Real.sqrt ((Sx.filter (fun q => q.2 = c)).card)
      * Real.sqrt ((Sy.filter (fun q => q.2 = c)).card)) :=
    Finset.sum_nonneg fun c _ => by positivity
  have hsx' : (Sx.card : ℝ) = ∑ c ∈ Z, ((Sx.filter (fun q => q.2 = c)).card : ℝ) := by
    rw [hSxsum]; push_cast; ring
  have hsy' : (Sy.card : ℝ) = ∑ c ∈ Z, ((Sy.filter (fun q => q.2 = c)).card : ℝ) := by
    rw [hSysum]; push_cast; ring
  have hfinal : ((S.card : ℝ)) ^ 2 ≤ (Sx.card : ℝ) * (Sy.card : ℝ) * (Sz.card : ℝ) := by
    have h0 : (0 : ℝ) ≤ (S.card : ℝ) := Nat.cast_nonneg _
    have hsq : ((S.card : ℝ)) ^ 2
        ≤ (Real.sqrt (Sz.card) *
            ∑ c ∈ Z, (Real.sqrt ((Sx.filter (fun q => q.2 = c)).card)
              * Real.sqrt ((Sy.filter (fun q => q.2 = c)).card))) ^ 2 := by
      nlinarith [hsum, h0, Real.sqrt_nonneg ((Sz.card : ℝ)), hT0]
    have hexp : (Real.sqrt (Sz.card) *
        ∑ c ∈ Z, (Real.sqrt ((Sx.filter (fun q => q.2 = c)).card)
          * Real.sqrt ((Sy.filter (fun q => q.2 = c)).card))) ^ 2
        = (Sz.card : ℝ) * (∑ c ∈ Z, (Real.sqrt ((Sx.filter (fun q => q.2 = c)).card)
          * Real.sqrt ((Sy.filter (fun q => q.2 = c)).card))) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    rw [hexp] at hsq
    have hz0 : (0 : ℝ) ≤ (Sz.card : ℝ) := Nat.cast_nonneg _
    rw [← hsx', ← hsy'] at hcs
    calc ((S.card : ℝ)) ^ 2
        ≤ (Sz.card : ℝ) * (∑ c ∈ Z, (Real.sqrt ((Sx.filter (fun q => q.2 = c)).card)
            * Real.sqrt ((Sy.filter (fun q => q.2 = c)).card))) ^ 2 := hsq
      _ ≤ (Sz.card : ℝ) * ((Sx.card : ℝ) * (Sy.card : ℝ)) :=
          mul_le_mul_of_nonneg_left hcs hz0
      _ = (Sx.card : ℝ) * (Sy.card : ℝ) * (Sz.card : ℝ) := by ring
  exact_mod_cast hfinal

/-- The statement for points of `ℝ³`, with the projections onto the `yz`-, `zx`- and `xy`-planes
identified with their images in `ℝ²`. -/
theorem imo1992_p5_real (S : Finset (ℝ × ℝ × ℝ)) :
    S.card ^ 2
      ≤ (S.image fun p => (p.2.1, p.2.2)).card
        * (S.image fun p => (p.1, p.2.2)).card
        * (S.image fun p => (p.1, p.2.1)).card :=
  imo1992_p5 S _ _ _ rfl rfl rfl

end Imo1992P5
