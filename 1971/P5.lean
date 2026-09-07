/-
# IMO 1971, Problem 5

Prove that for every natural number `m` there is a finite set `S` of points in
the plane such that every point of `S` has exactly `m` points of `S` at unit
distance from it.

## Strategy

The AoPS solution builds the "unit cube" graph `Qₘ = Qₘ₋₁ × K₂` and then has to
argue that a generic choice of `m` unit vectors realises it in the plane.  That
genericity argument is a single global choice of `m` angles avoiding finitely
many bad values.

Here we do the same thing **one step at a time**, which is much easier to
formalize.  Working in `ℂ`, we induct on `m`:

* `m = 0`: take `S = {0}`.
* `m + 1`: given `S` good for `m`, pick a unit `u` such that for all `x ≠ y` in
  `S` we have `dist (x - y) u ≠ 1` and `u ≠ x - y`, and set
  `T = S ∪ (S + u)`.

The two conditions say exactly that the only unit-distance edges between `S` and
`S + u` are the `2^m` "vertical" ones `x ↔ x + u`, and that the union is
disjoint.  So every point of `T` gains exactly one new neighbour: `m + 1`.

Such a `u` exists because the bad set is finite: for a fixed `d ≠ 0`, a point
`v` with `dist v 0 = 1` and `dist v d = 1` satisfies

  `conj d * v ^ 2 - (d * conj d) * v + d = 0`,

a quadratic with nonzero leading coefficient, so there are at most two of them;
and the unit circle is infinite.

Everything below is stated with `dist` and reduced to real coordinates through
`Complex.dist_eq_re_im`, so no `Complex.abs` / `norm` API is needed.
-/

import Mathlib

namespace Imo1971P5

/-! ### Distance in coordinates -/

private lemma dist_eq_one_iff (z w : ℂ) :
    dist z w = 1 ↔ (z.re - w.re) ^ 2 + (z.im - w.im) ^ 2 = 1 := by
  rw [Complex.dist_eq_re_im]
  constructor
  · intro h
    have h2 : Real.sqrt ((z.re - w.re) ^ 2 + (z.im - w.im) ^ 2) ^ 2 = 1 ^ 2 := by rw [h]
    rwa [Real.sq_sqrt (by positivity), one_pow] at h2
  · intro h
    rw [h, Real.sqrt_one]

private lemma conj_eq_one_of_dist {z : ℂ} (h : dist z 0 = 1) :
    z * (starRingEnd ℂ) z = 1 := by
  rw [dist_eq_one_iff] at h
  simp only [Complex.zero_re, Complex.zero_im, sub_zero] at h
  rw [Complex.mul_conj, show Complex.normSq z = z.re ^ 2 + z.im ^ 2 by
    rw [Complex.normSq_apply]; ring, h]
  norm_num

private lemma dist_shift (a b c : ℂ) : dist (a - b) c = dist a (b + c) := by
  rw [dist_eq_norm, dist_eq_norm, sub_sub]

/-! ### Two unit circles meet in finitely many points -/

/-- A quadratic with nonzero leading coefficient has finitely many roots:
if `u₀` is one root, every root is `u₀` or `a⁻¹ * (-b - a * u₀)`. -/
private lemma quad_finite {a b c : ℂ} (ha : a ≠ 0) :
    {u : ℂ | a * u ^ 2 + b * u + c = 0}.Finite := by
  rcases Set.eq_empty_or_nonempty {u : ℂ | a * u ^ 2 + b * u + c = 0} with h | h
  · rw [h]; exact Set.finite_empty
  · obtain ⟨u₀, hu₀⟩ := h
    refine Set.Finite.subset
      (Set.Finite.insert u₀ (Set.finite_singleton (a⁻¹ * (-b - a * u₀)))) ?_
    intro v hv
    have hv' : a * v ^ 2 + b * v + c = 0 := hv
    have hu₀' : a * u₀ ^ 2 + b * u₀ + c = 0 := hu₀
    rcases eq_or_ne v u₀ with h' | h'
    · exact Set.mem_insert_iff.mpr (Or.inl h')
    · refine Set.mem_insert_iff.mpr (Or.inr ?_)
      have hne : v - u₀ ≠ 0 := sub_ne_zero.mpr h'
      have hd : (v - u₀) * (a * (v + u₀) + b) = 0 := by linear_combination hv' - hu₀'
      have h2 : a * (v + u₀) + b = 0 := by
        rcases mul_eq_zero.mp hd with h'' | h''
        · exact absurd h'' hne
        · exact h''
      have h3 : a * v = -b - a * u₀ := by linear_combination h2
      show v = a⁻¹ * (-b - a * u₀)
      calc v = a⁻¹ * (a * v) := (inv_mul_cancel_left₀ ha v).symm
        _ = a⁻¹ * (-b - a * u₀) := by rw [h3]

/-- A point on both unit circles (centred at `0` and at `d`) is a root of an
explicit quadratic. -/
private lemma quad_root {d u : ℂ} (hu : dist u 0 = 1) (hud : dist u d = 1) :
    (starRingEnd ℂ) d * u ^ 2 - (d * (starRingEnd ℂ) d) * u + d = 0 := by
  have h1 : u * (starRingEnd ℂ) u = 1 := conj_eq_one_of_dist hu
  have hd1 : dist (u - d) 0 = 1 := by
    rw [dist_eq_one_iff] at hud ⊢
    simpa using hud
  have h2 : (u - d) * ((starRingEnd ℂ) u - (starRingEnd ℂ) d) = 1 := by
    have h := conj_eq_one_of_dist hd1
    rwa [map_sub] at h
  linear_combination (u - d) * h1 - u * h2

private lemma two_circles_finite {d : ℂ} (hd : d ≠ 0) :
    {v : ℂ | dist v d = 1 ∧ dist v 0 = 1}.Finite := by
  have hcd : (starRingEnd ℂ) d ≠ 0 := by
    intro h
    apply hd
    have h' := congrArg (starRingEnd ℂ) h
    simpa using h'
  refine Set.Finite.subset
    (quad_finite (a := (starRingEnd ℂ) d) (b := -(d * (starRingEnd ℂ) d)) (c := d) hcd) ?_
  intro v hv
  have h := quad_root hv.2 hv.1
  show (starRingEnd ℂ) d * v ^ 2 + -(d * (starRingEnd ℂ) d) * v + d = 0
  linear_combination h

/-! ### The unit circle is infinite -/

private lemma circle_infinite : {z : ℂ | dist z 0 = 1}.Infinite := by
  have hre : ∀ t : ℝ, ((Real.cos t : ℂ) + (Real.sin t : ℂ) * Complex.I).re = Real.cos t := by
    intro t
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  have him : ∀ t : ℝ, ((Real.cos t : ℂ) + (Real.sin t : ℂ) * Complex.I).im = Real.sin t := by
    intro t
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  have hpi : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hinj : Set.InjOn (fun t : ℝ => (Real.cos t : ℂ) + (Real.sin t : ℂ) * Complex.I)
      (Set.Icc 0 1) := by
    intro a ha b hb hab
    have hc : Real.cos a = Real.cos b := by
      rw [← hre a, ← hre b]
      exact congrArg Complex.re hab
    exact Real.injOn_cos ⟨ha.1, ha.2.trans hpi⟩ ⟨hb.1, hb.2.trans hpi⟩ hc
  refine Set.Infinite.mono ?_ ((Set.Icc_infinite (by norm_num : (0 : ℝ) < 1)).image hinj)
  rintro z ⟨t, -, rfl⟩
  show dist ((Real.cos t : ℂ) + (Real.sin t : ℂ) * Complex.I) 0 = 1
  rw [dist_eq_one_iff, hre, him]
  simp [Real.cos_sq_add_sin_sq]

/-! ### Choosing the new direction -/

private lemma exists_good (S : Finset ℂ) :
    ∃ u : ℂ, dist u 0 = 1 ∧
      ∀ x ∈ S, ∀ y ∈ S, x ≠ y → dist (x - y) u ≠ 1 ∧ u ≠ x - y := by
  classical
  obtain ⟨D, hDmem⟩ :
      ∃ D : Finset ℂ, ∀ d : ℂ, d ∈ D ↔ (d ≠ 0 ∧ ∃ x ∈ S, ∃ y ∈ S, d = x - y) := by
    refine ⟨((S ×ˢ S).image (fun p => p.1 - p.2)).erase 0, ?_⟩
    intro d
    constructor
    · intro h
      rw [Finset.mem_erase] at h
      obtain ⟨h0, hi⟩ := h
      obtain ⟨p, hp, hpd⟩ := Finset.mem_image.mp hi
      rw [Finset.mem_product] at hp
      exact ⟨h0, p.1, hp.1, p.2, hp.2, hpd.symm⟩
    · rintro ⟨h0, x, hx, y, hy, rfl⟩
      rw [Finset.mem_erase]
      exact ⟨h0, Finset.mem_image.mpr ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩, rfl⟩⟩
  have hBadFin :
      (⋃ d ∈ (D : Set ℂ), ({v : ℂ | dist v d = 1 ∧ dist v 0 = 1} ∪ {d})).Finite := by
    refine Set.Finite.biUnion D.finite_toSet ?_
    intro d hd
    have hd0 : d ≠ 0 := ((hDmem d).mp (Finset.mem_coe.mp hd)).1
    exact (two_circles_finite hd0).union (Set.finite_singleton d)
  obtain ⟨u, hu⟩ :=
    (Set.Infinite.sdiff circle_infinite hBadFin).nonempty
  refine ⟨u, hu.1, ?_⟩
  intro x hx y hy hxy
  have hdmem : x - y ∈ (D : Set ℂ) :=
    Finset.mem_coe.mpr ((hDmem _).mpr ⟨sub_ne_zero.mpr hxy, x, hx, y, hy, rfl⟩)
  constructor
  · intro hcon
    refine hu.2 (Set.mem_biUnion hdmem (Or.inl ⟨?_, hu.1⟩))
    rwa [dist_comm] at hcon
  · intro hcon
    exact hu.2 (Set.mem_biUnion hdmem (Or.inr hcon))

/-! ### The theorem -/

open scoped Classical in
/-- **IMO 1971, Problem 5.**  For every `m` there is a finite set of points of
the plane in which every point has exactly `m` points at unit distance. -/
theorem imo1971_p5 (m : ℕ) :
    ∃ S : Finset ℂ, ∀ A ∈ S, (S.filter (fun B => dist A B = 1)).card = m := by
  induction m with
  | zero =>
    refine ⟨{0}, ?_⟩
    intro A hA
    rw [Finset.mem_singleton] at hA
    subst hA
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro b hb
    rw [Finset.mem_singleton] at hb
    subst hb
    simp
  | succ n ih =>
    obtain ⟨S, hS⟩ := ih
    obtain ⟨u, hu, hgood⟩ := exists_good S
    have hu0 : u ≠ 0 := by
      intro h
      rw [h] at hu
      simp at hu
    -- the translate `x ↦ x + u` is injective and moves `S` off itself
    have hinj : Function.Injective (fun z : ℂ => z + u) := fun a b hab => by
      simpa using hab
    have hdisj : Disjoint S (S.image (fun z => z + u)) := by
      rw [Finset.disjoint_right]
      rintro x hx hxS
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      have hxy : y + u ≠ y := fun h => hu0 (by linear_combination h)
      exact (hgood (y + u) hxS y hy hxy).2 (by ring)
    -- distance to a translated point
    have hdu : ∀ a : ℂ, dist a (a + u) = 1 := by
      intro a
      rw [← dist_shift a a u, sub_self, dist_comm]
      exact hu
    refine ⟨S ∪ S.image (fun z => z + u), ?_⟩
    intro A hA
    rw [Finset.filter_union,
      Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hdisj)]
    rcases Finset.mem_union.mp hA with hA' | hA'
    · -- `A ∈ S` : `n` old neighbours plus the single new one `A + u`
      have h1 : (S.filter (fun B => dist A B = 1)).card = n := hS A hA'
      have h2 : (S.image (fun z => z + u)).filter (fun B => dist A B = 1) = {A + u} := by
        ext b
        simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_singleton]
        constructor
        · rintro ⟨⟨y, hy, rfl⟩, hb⟩
          rcases eq_or_ne A y with h' | h'
          · rw [h']
          · exact absurd (by rw [dist_shift]; exact hb) (hgood A hA' y hy h').1
        · rintro rfl
          exact ⟨⟨A, hA', rfl⟩, hdu A⟩
      rw [h1, h2, Finset.card_singleton]
    · -- `A = x + u` : the single old neighbour `x` plus `n` translated ones
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hA'
      have h1 : S.filter (fun B => dist (x + u) B = 1) = {x} := by
        ext b
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hb, hd⟩
          rcases eq_or_ne b x with h' | h'
          · exact h'
          · exact absurd (by rw [dist_shift]; rw [dist_comm] at hd; exact hd)
              (hgood b hb x hx h').1
        · rintro rfl
          exact ⟨hx, by rw [dist_comm]; exact hdu b⟩
      have h2 : (S.image (fun z => z + u)).filter (fun B => dist (x + u) B = 1)
          = (S.filter (fun B => dist x B = 1)).image (fun z => z + u) := by
        ext b
        simp only [Finset.mem_filter, Finset.mem_image]
        constructor
        · rintro ⟨⟨y, hy, rfl⟩, hb⟩
          exact ⟨y, ⟨hy, by rwa [dist_add_right] at hb⟩, rfl⟩
        · rintro ⟨y, ⟨hy, hby⟩, rfl⟩
          exact ⟨⟨y, hy, rfl⟩, by rwa [dist_add_right]⟩
      rw [h1, h2, Finset.card_singleton, Finset.card_image_of_injective _ hinj,
        hS x hx]
      omega

end Imo1971P5
