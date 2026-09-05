/-
IMO 1965, Problem 3.

  Tetrahedron `ABCD` has opposite edges `AB` and `CD`.  A plane `ε` parallel to
  both `AB` and `CD` cuts the tetrahedron into two solids, the ratio of the
  distances of `ε` from `AB` and from `CD` being `k`.  Then the two solids have
  volume ratio `k² (k + 3) / (3k + 1)`.

  ## Coordinates

  We use barycentric coordinates `(γ, δ, β)` relative to `A`, i.e. a point of
  the tetrahedron is

      P = A + γ • (C - A) + δ • (D - A) + β • (B - A),   γ, δ, β ≥ 0, γ+δ+β ≤ 1.

  In these coordinates the tetrahedron is the standard simplex `tetra`, with

      A ↦ (0,0,0),  C ↦ (1,0,0),  D ↦ (0,1,0),  B ↦ (0,0,1).

  The planes parallel to *both* `AB` and `CD` are exactly the level sets of the
  affine form `tParam (γ,δ,β) = γ + δ`: the edge `AB` lies in `{t = 0}` and the
  edge `CD` in `{t = 1}`.  Because `t` is affine, distances inside this pencil of
  parallel planes are proportional to `t`, so the plane `{t = c}` satisfies

      dist(ε, AB) / dist(ε, CD) = c / (1 - c),

  and the hypothesis of the problem reads `c = k / (k + 1)`.

  `lower c` is the piece containing the edge `AB` (the solid `ABWXYZ` of the
  reference solution), `upper c` is the complementary piece.

  Everything below is proved from Mathlib; there is no `sorry` and no new axiom.
-/

import Mathlib

open MeasureTheory Set

noncomputable section

namespace IMO1965Q3

/-- Barycentric coordinates `(γ, δ, β)`. -/
abbrev Pt := ℝ × ℝ × ℝ

/-- The tetrahedron, in barycentric coordinates: the standard `3`-simplex. -/
def tetra : Set Pt :=
  {p | 0 ≤ p.1 ∧ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧ p.1 + p.2.1 + p.2.2 ≤ 1}

/-- The affine form whose level sets are the planes parallel to `AB` and to `CD`. -/
def tParam (p : Pt) : ℝ := p.1 + p.2.1

/-- The piece of the tetrahedron on the `AB` side of the plane `{tParam = c}`,
written as an iterated box (this is the shape Fubini wants). -/
def lower (c : ℝ) : Set Pt :=
  {p | p.1 ∈ Icc (0 : ℝ) c ∧ p.2.1 ∈ Icc (0 : ℝ) (c - p.1) ∧
       p.2.2 ∈ Icc (0 : ℝ) (1 - p.1 - p.2.1)}

/-- The piece of the tetrahedron on the `CD` side of the plane. -/
def upper (c : ℝ) : Set Pt := tetra \ lower c

/-! ### The cut is really the cut -/

/-- `lower c` is exactly the part of the tetrahedron with `tParam ≤ c`. -/
theorem lower_eq (c : ℝ) : lower c = tetra ∩ {p | tParam p ≤ c} := by
  ext p
  simp only [lower, tetra, tParam, mem_setOf_eq, mem_inter_iff, mem_Icc]
  constructor
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩, ⟨h5, h6⟩⟩
    exact ⟨⟨h1, h3, h5, by linarith⟩, by linarith⟩
  · rintro ⟨⟨h1, h2, h3, h4⟩, h5⟩
    exact ⟨⟨h1, by linarith⟩, ⟨h2, by linarith⟩, ⟨h3, by linarith⟩⟩

theorem lower_subset_tetra (c : ℝ) : lower c ⊆ tetra := by
  rw [lower_eq]; exact inter_subset_left

/-- Taking `c = 1` recovers the whole tetrahedron. -/
theorem tetra_eq_lower_one : tetra = lower 1 := by
  rw [lower_eq]
  ext p
  simp only [tetra, tParam, mem_setOf_eq, mem_inter_iff]
  exact ⟨fun h => ⟨h, by linarith [h.1, h.2.1, h.2.2.1, h.2.2.2]⟩, fun h => h.1⟩

/-! ### Measurability -/

theorem isClosed_lower (c : ℝ) : IsClosed (lower c) := by
  have h : lower c =
      ({p : Pt | 0 ≤ p.1} ∩ {p : Pt | p.1 ≤ c}) ∩
      (({p : Pt | 0 ≤ p.2.1} ∩ {p : Pt | p.2.1 ≤ c - p.1}) ∩
       ({p : Pt | 0 ≤ p.2.2} ∩ {p : Pt | p.2.2 ≤ 1 - p.1 - p.2.1})) := by
    ext p; simp only [lower, mem_setOf_eq, mem_inter_iff, mem_Icc]; tauto
  rw [h]
  have c1 : Continuous fun p : Pt => p.1 := continuous_fst
  have c2 : Continuous fun p : Pt => p.2.1 := continuous_fst.comp continuous_snd
  have c3 : Continuous fun p : Pt => p.2.2 := continuous_snd.comp continuous_snd
  exact ((isClosed_le continuous_const c1).inter (isClosed_le c1 continuous_const)).inter
    (((isClosed_le continuous_const c2).inter
        (isClosed_le c2 (continuous_const.sub c1))).inter
     ((isClosed_le continuous_const c3).inter
        (isClosed_le c3 ((continuous_const.sub c1).sub c2))))

theorem measurableSet_lower (c : ℝ) : MeasurableSet (lower c) :=
  (isClosed_lower c).measurableSet

theorem measurableSet_tetra : MeasurableSet tetra := by
  rw [tetra_eq_lower_one]; exact measurableSet_lower 1

/-! ### The two-dimensional slice -/

/-- Area of the plane region `{(z, x) | 0 ≤ z ≤ a, 0 ≤ x ≤ b - z}`. -/
theorem volume_slice {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    volume {q : ℝ × ℝ | q.1 ∈ Icc (0 : ℝ) a ∧ q.2 ∈ Icc (0 : ℝ) (b - q.1)}
      = ENNReal.ofReal (a * b - a ^ 2 / 2) := by
  set S : Set (ℝ × ℝ) :=
    {q : ℝ × ℝ | q.1 ∈ Icc (0 : ℝ) a ∧ q.2 ∈ Icc (0 : ℝ) (b - q.1)} with hSdef
  -- `S` is closed, hence measurable.
  have hS : MeasurableSet S := by
    have hcl : IsClosed S := by
      have h : S = ({q : ℝ × ℝ | 0 ≤ q.1} ∩ {q : ℝ × ℝ | q.1 ≤ a}) ∩
                   ({q : ℝ × ℝ | 0 ≤ q.2} ∩ {q : ℝ × ℝ | q.2 ≤ b - q.1}) := by
        ext q; simp only [hSdef, mem_setOf_eq, mem_inter_iff, mem_Icc]; tauto
      rw [h]
      exact ((isClosed_le continuous_const continuous_fst).inter
          (isClosed_le continuous_fst continuous_const)).inter
        ((isClosed_le continuous_const continuous_snd).inter
          (isClosed_le continuous_snd (continuous_const.sub continuous_fst)))
    exact hcl.measurableSet
  rw [Measure.volume_eq_prod, Measure.prod_apply hS]
  -- The `z`-slice of `S` is `Icc 0 (b - z)` for `z ∈ [0, a]`, and empty otherwise.
  have key : (fun z => volume (Prod.mk z ⁻¹' S))
      = (Icc (0 : ℝ) a).indicator (fun z => ENNReal.ofReal (b - z)) := by
    funext z
    by_cases hz : z ∈ Icc (0 : ℝ) a
    · rw [indicator_of_mem hz]
      have hset : Prod.mk z ⁻¹' S = Icc (0 : ℝ) (b - z) := by
        ext w
        simp only [mem_preimage, hSdef, mem_setOf_eq]
        exact ⟨fun h => h.2, fun h => ⟨hz, h⟩⟩
      rw [hset, Real.volume_Icc, sub_zero]
    · rw [indicator_of_not_mem hz]
      have hset : Prod.mk z ⁻¹' S = (∅ : Set ℝ) := by
        ext w
        simp only [mem_preimage, hSdef, mem_setOf_eq, mem_empty_iff_false, iff_false]
        exact fun h => hz h.1
      rw [hset, measure_empty]
  rw [key, lintegral_indicator measurableSet_Icc]
  -- Turn the lower Lebesgue integral into a Bochner integral.
  have hcont : Continuous fun z : ℝ => b - z := by fun_prop
  have hint : IntegrableOn (fun z : ℝ => b - z) (Icc (0 : ℝ) a) :=
    hcont.integrableOn_Icc
  have hnn : 0 ≤ᵐ[volume.restrict (Icc (0 : ℝ) a)] fun z : ℝ => b - z := by
    refine ae_restrict_of_forall_mem measurableSet_Icc ?_
    intro z hz
    have h1 : z ≤ a := hz.2
    linarith
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
  congr 1
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ha]
  have : ∫ z in (0 : ℝ)..a, (b - z) = b * a - a ^ 2 / 2 := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const
      intervalIntegral.intervalIntegrable_id]
    rw [intervalIntegral.integral_const, integral_id]
    simp
    ring
  rw [this]; ring

/-! ### Volume of the two pieces -/

/-- The piece containing `AB` has volume `c²/2 - c³/3` (the tetrahedron itself
having volume `1/6` in these coordinates). -/
theorem volume_lower {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    volume (lower c) = ENNReal.ofReal (c ^ 2 / 2 - c ^ 3 / 3) := by
  rw [Measure.volume_eq_prod, Measure.prod_apply (measurableSet_lower c)]
  have key : (fun y => volume (Prod.mk y ⁻¹' lower c))
      = (Icc (0 : ℝ) c).indicator
          (fun y => ENNReal.ofReal ((c - y) * (1 - y) - (c - y) ^ 2 / 2)) := by
    funext y
    by_cases hy : y ∈ Icc (0 : ℝ) c
    · rw [indicator_of_mem hy]
      have hset : Prod.mk y ⁻¹' lower c
          = {q : ℝ × ℝ | q.1 ∈ Icc (0 : ℝ) (c - y) ∧ q.2 ∈ Icc (0 : ℝ) (1 - y - q.1)} := by
        ext q
        simp only [mem_preimage, lower, mem_setOf_eq]
        exact ⟨fun h => ⟨h.2.1, h.2.2⟩, fun h => ⟨hy, h.1, h.2⟩⟩
      have h1 : (0 : ℝ) ≤ c - y := by have := hy.2; linarith
      have h2 : c - y ≤ 1 - y := by linarith
      rw [hset, volume_slice h1 h2]
    · rw [indicator_of_not_mem hy]
      have hset : Prod.mk y ⁻¹' lower c = (∅ : Set (ℝ × ℝ)) := by
        ext q
        simp only [mem_preimage, lower, mem_setOf_eq, mem_empty_iff_false, iff_false]
        exact fun h => hy h.1
      rw [hset, measure_empty]
  rw [key, lintegral_indicator measurableSet_Icc]
  have hcont : Continuous fun y : ℝ => (c - y) * (1 - y) - (c - y) ^ 2 / 2 := by fun_prop
  have hint : IntegrableOn (fun y : ℝ => (c - y) * (1 - y) - (c - y) ^ 2 / 2)
      (Icc (0 : ℝ) c) := hcont.integrableOn_Icc
  have hnn : 0 ≤ᵐ[volume.restrict (Icc (0 : ℝ) c)]
      fun y : ℝ => (c - y) * (1 - y) - (c - y) ^ 2 / 2 := by
    refine ae_restrict_of_forall_mem measurableSet_Icc ?_
    intro y hy
    -- the integrand equals `(c - y) * (2 - c - y) / 2`
    have h1 : (0 : ℝ) ≤ y := hy.1
    have h2 : y ≤ c := hy.2
    nlinarith [sq_nonneg (c - y)]
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
  congr 1
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hc0]
  -- Fundamental theorem of calculus with the explicit antiderivative.
  have hderiv : ∀ y ∈ uIcc (0 : ℝ) c,
      HasDerivAt (fun y : ℝ => c * y - y ^ 2 / 2 + y ^ 3 / 6 - c ^ 2 * y / 2)
        ((c - y) * (1 - y) - (c - y) ^ 2 / 2) y := by
    intro y _
    have d1 : HasDerivAt (fun y : ℝ => c * y) c y := by
      simpa using (hasDerivAt_id y).const_mul c
    have d2 : HasDerivAt (fun y : ℝ => y ^ 2 / 2) y y := by
      have h := (hasDerivAt_pow 2 y).div_const 2
      convert h using 1; norm_num
    have d3 : HasDerivAt (fun y : ℝ => y ^ 3 / 6) (y ^ 2 / 2) y := by
      have h := (hasDerivAt_pow 3 y).div_const 6
      convert h using 1; norm_num; ring
    have d4 : HasDerivAt (fun y : ℝ => c ^ 2 * y / 2) (c ^ 2 / 2) y := by
      have h := ((hasDerivAt_id y).const_mul (c ^ 2)).div_const 2
      convert h using 1; norm_num
    have h := ((d1.sub d2).add d3).sub d4
    convert h using 1
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      (hcont.intervalIntegrable _ _)]
  ring

theorem volume_tetra : volume tetra = ENNReal.ofReal (1 / 6) := by
  rw [tetra_eq_lower_one, volume_lower zero_le_one le_rfl]
  norm_num

theorem lower_nonneg {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    0 ≤ c ^ 2 / 2 - c ^ 3 / 3 := by nlinarith [sq_nonneg c]

theorem volume_upper {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    volume (upper c) = ENNReal.ofReal (1 / 6 - (c ^ 2 / 2 - c ^ 3 / 3)) := by
  have hfin : volume (lower c) ≠ ⊤ := by
    rw [volume_lower hc0 hc1]; exact ENNReal.ofReal_ne_top
  rw [upper, measure_diff (lower_subset_tetra c)
      (measurableSet_lower c).nullMeasurableSet hfin,
    volume_tetra, volume_lower hc0 hc1,
    ← ENNReal.ofReal_sub _ (lower_nonneg hc0 hc1)]

/-! ### The answer -/

/-- **IMO 1965, Problem 3.**  If the cutting plane is `k` times as far from `AB`
as it is from `CD` — i.e. it is the plane `tParam = k / (k+1)` — then the piece
containing `AB` and the piece containing `CD` have volume ratio
`k² (k + 3) / (3k + 1)`. -/
theorem imo1965_q3 {k : ℝ} (hk : 0 < k) :
    (volume (lower (k / (k + 1)))).toReal / (volume (upper (k / (k + 1)))).toReal
      = k ^ 2 * (k + 3) / (3 * k + 1) := by
  have hk1 : (0 : ℝ) < k + 1 := by linarith
  have hk1' : (k : ℝ) + 1 ≠ 0 := ne_of_gt hk1
  set c : ℝ := k / (k + 1) with hcdef
  have hc0 : 0 ≤ c := by rw [hcdef]; positivity
  have hc1 : c ≤ 1 := by
    rw [hcdef, div_le_one hk1]; linarith
  -- Explicit values of the two volumes.
  have hnum : c ^ 2 / 2 - c ^ 3 / 3 = (k ^ 3 + 3 * k ^ 2) / (6 * (k + 1) ^ 3) := by
    rw [hcdef]; field_simp; ring
  have hden : 1 / 6 - (c ^ 2 / 2 - c ^ 3 / 3) = (3 * k + 1) / (6 * (k + 1) ^ 3) := by
    rw [hnum]; field_simp; ring
  have hL : 0 ≤ c ^ 2 / 2 - c ^ 3 / 3 := lower_nonneg hc0 hc1
  have hU : 0 ≤ 1 / 6 - (c ^ 2 / 2 - c ^ 3 / 3) := by
    rw [hden]; positivity
  rw [volume_lower hc0 hc1, volume_upper hc0 hc1,
    ENNReal.toReal_ofReal hL, ENNReal.toReal_ofReal hU, hnum, hden]
  have h6 : (6 : ℝ) * (k + 1) ^ 3 ≠ 0 := by positivity
  have hb : (3 : ℝ) * k + 1 ≠ 0 := by positivity
  field_simp
  ring

end IMO1965Q3
