/-
# IMO 1971, Problem 2

Let `P₁` be a convex polyhedron with nine vertices `A₁, …, A₉`, and let `Pᵢ` be
the image of `P₁` under the translation that moves `A₁` to `Aᵢ`.  Prove that at
least two of `P₁, …, P₉` have an interior point in common.

## Modelling choices

* Ambient space: `EuclideanSpace ℝ (Fin 3)` with its Haar/Lebesgue `volume`.
* "Convex polyhedron with vertices `A₁, …, A₉`" is modelled as
  `K = convexHull ℝ (Set.range A)` for `A : Fin 9 → E3`.  That the `Aᵢ` are
  exactly the *extreme* points is never used by the argument, so it is not
  assumed; the proof only needs `A i ∈ K`.  This makes the theorem stronger.
* "Polyhedron" (as opposed to a degenerate flat figure) is encoded by
  `(interior K).Nonempty`, i.e. `K` is a solid body.
* `P i = (· + (A i - A 0)) '' K` is the translate carrying `A 0` to `A i`.
* Indices run `0 … 8`, so `A 0` plays the role of `A₁` and `P 0 = K`.
* Note that distinctness of the `Aᵢ` is not needed either: if two of them
  coincide the corresponding translates are equal, and the conclusion is
  immediate.

## Proof

For each `i` we have `P i ⊆ 2 • K - A 0`: if `p ∈ K` then `(A i + p) / 2 ∈ K`
by convexity, hence `A i + p ∈ 2 • K`.  The nine open sets `interior (P i)`
therefore all live inside a set of volume `8 * volume K`, while each of them has
volume `volume K` (a convex set has null frontier, so its interior has the same
measure as the set itself).  Since `9 * volume K > 8 * volume K` and
`0 < volume K < ∞`, the nine interiors cannot be pairwise disjoint.
-/

import Mathlib

open MeasureTheory Set Module Pointwise

/-- Ambient 3-dimensional Euclidean space. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- **IMO 1971, Problem 2.**  Given a solid convex polyhedron `K` with vertices
`A 0, …, A 8` and the nine translates `P i` of `K` carrying `A 0` to `A i`, two
of the `P i` share an interior point. -/
theorem imo1971_p2
    (A : Fin 9 → E3)
    (K : Set E3)
    (hKdef : K = convexHull ℝ (Set.range A))
    (hsolid : (interior K).Nonempty)
    (P : Fin 9 → Set E3)
    (hPdef : ∀ i, P i = (fun x => x + (A i - A 0)) '' K) :
    ∃ i j, i ≠ j ∧ (interior (P i) ∩ interior (P j)).Nonempty := by
  ---------------------------------------------------------------------------
  -- 1.  Basic properties of the body `K`.
  ---------------------------------------------------------------------------
  have hconv : Convex ℝ K := by rw [hKdef]; exact convex_convexHull ℝ _
  have hcomp : IsCompact K := by
    rw [hKdef]
    -- `apply` first, so that `𝕜 := ℝ` is fixed by unifying with the goal;
    -- with `exact` the instance search for `Field 𝕜` fires too early.
    apply Set.Finite.isCompact_convexHull
    exact Set.finite_range A
  have hmem : ∀ i, A i ∈ K := by
    intro i; rw [hKdef]; exact subset_convexHull ℝ _ ⟨i, rfl⟩

  ---------------------------------------------------------------------------
  -- 2.  Translations preserve interiors and volume.
  ---------------------------------------------------------------------------
  -- `⇑(Homeomorph.addRight v)` is definitionally `fun x => x + v`.
  have himg_int : ∀ (v : E3) (s : Set E3),
      interior ((fun x => x + v) '' s) = (fun x => x + v) '' interior s :=
    fun v s => ((Homeomorph.addRight v).image_interior s).symm
  have himg_vol : ∀ (v : E3) (s : Set E3),
      volume ((fun x => x + v) '' s) = volume s := by
    intro v s
    rw [Set.image_add_right, measure_preimage_add_right]

  ---------------------------------------------------------------------------
  -- 3.  `volume (interior K) = volume K`, and `0 < volume K < ∞`.
  ---------------------------------------------------------------------------
  have hVtop : volume K ≠ ⊤ := hcomp.measure_lt_top.ne
  have hIK : volume (interior K) = volume K := by
    have hfr : volume (frontier K) = 0 := hconv.addHaar_frontier volume
    refine le_antisymm (measure_mono interior_subset) ?_
    have hsubK : K ⊆ interior K ∪ frontier K := by
      intro x hx
      by_cases h : x ∈ interior K
      · exact Or.inl h
      · exact Or.inr ⟨subset_closure hx, h⟩
    calc volume K ≤ volume (interior K ∪ frontier K) := measure_mono hsubK
      _ ≤ volume (interior K) + volume (frontier K) := measure_union_le _ _
      _ = volume (interior K) := by rw [hfr, add_zero]
  have hVpos : 0 < volume K := by
    rw [← hIK]
    exact isOpen_interior.measure_pos volume hsolid

  ---------------------------------------------------------------------------
  -- 4.  All nine translates sit inside `T = 2 • K - A 0`, of volume `8 * V`.
  ---------------------------------------------------------------------------
  set T : Set E3 := (fun y => A 0 + y) ⁻¹' ((2 : ℝ) • K) with hTdef

  have hsub : ∀ i, P i ⊆ T := by
    intro i x hx
    rw [hPdef i] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    -- the midpoint of `A i` and `p` lies in `K`
    have hhalf : (2 : ℝ)⁻¹ • (A i + p) ∈ K := by
      have h := hconv (hmem i) hp (by norm_num : (0:ℝ) ≤ (2:ℝ)⁻¹)
        (by norm_num : (0:ℝ) ≤ (2:ℝ)⁻¹) (by norm_num)
      rw [smul_add]
      exact h
    rw [hTdef, Set.mem_preimage, Set.mem_smul_set]
    refine ⟨(2 : ℝ)⁻¹ • (A i + p), hhalf, ?_⟩
    have h2 : ((2 : ℝ) * (2 : ℝ)⁻¹) = 1 := by norm_num
    rw [smul_smul, h2, one_smul]
    -- goal: `A i + p = A 0 + (p + (A i - A 0))`; `abel` chokes on the `ℝ`-smul
    -- normal form, `module` is the right tactic for a module identity.
    module

  have hTvol : volume T = volume K * 8 := by
    rw [hTdef, measure_preimage_add, Measure.addHaar_smul,
      finrank_euclideanSpace_fin]
    norm_num [mul_comm]

  ---------------------------------------------------------------------------
  -- 5.  Each interior has volume `V`.
  ---------------------------------------------------------------------------
  have hIP : ∀ i, volume (interior (P i)) = volume K := by
    intro i
    rw [hPdef i, himg_int, himg_vol]
    exact hIK

  ---------------------------------------------------------------------------
  -- 6.  Pigeonhole:  9 * V ≤ 8 * V  is absurd.
  ---------------------------------------------------------------------------
  by_contra hcon
  have hcon' : ∀ i j : Fin 9, i ≠ j → interior (P i) ∩ interior (P j) = ∅ := by
    intro i j hij
    by_contra h
    exact hcon ⟨i, j, hij, Set.nonempty_iff_ne_empty.mpr h⟩

  have hdisj : Pairwise (Function.onFun Disjoint fun i => interior (P i)) := by
    intro i j hij
    show Disjoint (interior (P i)) (interior (P j))
    exact Set.disjoint_iff_inter_eq_empty.mpr (hcon' i j hij)

  have hmeas : ∀ i : Fin 9, MeasurableSet (interior (P i)) :=
    fun _ => isOpen_interior.measurableSet

  have hUnion : volume (⋃ i, interior (P i))
      = ∑' i : Fin 9, volume (interior (P i)) := measure_iUnion hdisj hmeas
  rw [tsum_fintype] at hUnion

  have hUsub : (⋃ i, interior (P i)) ⊆ T :=
    Set.iUnion_subset fun i => interior_subset.trans (hsub i)

  have hle : ∑ i : Fin 9, volume (interior (P i)) ≤ volume T := by
    rw [← hUnion]; exact measure_mono hUsub

  have hsum : ∑ i : Fin 9, volume (interior (P i)) = volume K * 9 := by
    rw [Finset.sum_congr rfl fun i _ => hIP i, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    simp [mul_comm]

  rw [hsum, hTvol] at hle
  -- `ENNReal.mul_lt_mul_left h0 htop : a < b → a * volume K < b * volume K`
  -- (an implication, and the multiplication is on the right).
  have hstrict : volume K * 8 < volume K * 9 := by
    rw [mul_comm (volume K) (8 : ENNReal), mul_comm (volume K) (9 : ENNReal)]
    exact ENNReal.mul_lt_mul_left hVpos.ne' hVtop (by norm_num)
  exact absurd hle (not_le.mpr hstrict)
