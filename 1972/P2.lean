/-
# IMO 1972, Problem 2 — the cyclic-trapezoid engine

Prove that for `n ≥ 4`, every quadrilateral inscribable in a circle can be
dissected into `n` quadrilaterals each inscribable in a circle.

## Honest scope note

Like 1971 P4, this is not a one-pass formalization.  The statement itself needs
a notion of *dissection*, which Mathlib does not have.  A workable definition is

```
structure CyclicQuad (Q : Set ℂ) : Prop where
  vertices : ∃ p q r s : ℂ,
    Q = convexHull ℝ {p, q, r, s} ∧
    (∃ o : ℂ, ∃ ρ : ℝ, dist p o = ρ ∧ dist q o = ρ ∧ dist r o = ρ ∧ dist s o = ρ)

def IsDissection (K : Set ℂ) (n : ℕ) : Prop :=
  ∃ Q : Fin n → Set ℂ,
    (⋃ i, Q i) = K ∧
    (∀ i j, i ≠ j → interior (Q i) ∩ interior (Q j) = ∅) ∧
    ∀ i, CyclicQuad (Q i)

theorem imo1972_p2 (K : Set ℂ) (hK : CyclicQuad K) (n : ℕ) (hn : 4 ≤ n) :
    IsDissection K n
```

and proving it requires, for a *general* cyclic `ABCD`: the auxiliary points
`E ∈ AB`, `F ∈ CD` with `EF ∥ AD`, the isosceles trapezoid `AEVU`, the circle
through `U` and `D` cutting `UV` and `DF`, and then a verification that the four
pieces cover `K` with disjoint interiors.  The covering/disjointness bookkeeping
over convex hulls is the expensive part, and the AoPS write-up is itself only a
sketch there (it asserts the auxiliary circle exists without constructing it).

What follows compiles with no `sorry` and proves the part that actually drives
the induction — the `n ≥ 5` step of the official solution, "since we have an
isosceles trapezoid, we can add as many trapezoids as we want by dissecting it
with lines parallel to its bases":

* `trapezoid_cyclic` — the four vertices `(±a, h₀)`, `(±b, h₁)` of any trapezoid
  symmetric about the `y`-axis are concyclic, as soon as `h₀ ≠ h₁`.  The centre
  is `(0, k)` with `k = (b² + h₁² - a² - h₀²) / (2(h₁ - h₀))`.
* `cut_mem_segment` — the horizontal line at height `t` meets the leg from
  `(a, 0)` to `(b, h)` exactly at `(a + (b - a)t/h, t)`.
* `cut_pieces_cyclic` — hence both pieces of such a cut are again cyclic.

Iterating `cut_pieces_cyclic` turns one cyclic piece into `m` cyclic pieces for
any `m ≥ 1`, which is exactly how `n = 4` bootstraps to every `n ≥ 4`.
-/

import Mathlib

namespace Imo1972P2

/-- The point of the plane with coordinates `(x, y)`, as a complex number. -/
noncomputable def pt (x y : ℝ) : ℂ := (x : ℂ) + (y : ℂ) * Complex.I

@[simp] lemma pt_re (x y : ℝ) : (pt x y).re = x := by
  simp only [pt, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

@[simp] lemma pt_im (x y : ℝ) : (pt x y).im = y := by
  simp only [pt, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

lemma dist_pt (x₁ y₁ x₂ y₂ : ℝ) :
    dist (pt x₁ y₁) (pt x₂ y₂) = Real.sqrt ((x₁ - x₂) ^ 2 + (y₁ - y₂) ^ 2) := by
  rw [Complex.dist_eq_re_im, pt_re, pt_re, pt_im, pt_im]

/-- **Every trapezoid symmetric about the `y`-axis is cyclic.**  The vertices
`(±a, h₀)` and `(±b, h₁)` lie on the circle centred at `(0, k)` with
`k = (b² + h₁² - a² - h₀²) / (2 (h₁ - h₀))`. -/
theorem trapezoid_cyclic (a b h₀ h₁ : ℝ) (hne : h₀ ≠ h₁) :
    ∃ (o : ℂ) (r : ℝ),
      dist (pt a h₀) o = r ∧ dist (pt (-a) h₀) o = r ∧
      dist (pt b h₁) o = r ∧ dist (pt (-b) h₁) o = r := by
  have hd : h₁ - h₀ ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  set k : ℝ := (b ^ 2 + h₁ ^ 2 - a ^ 2 - h₀ ^ 2) / (2 * (h₁ - h₀)) with hk
  refine ⟨pt 0 k, Real.sqrt (a ^ 2 + (h₀ - k) ^ 2), ?_, ?_, ?_, ?_⟩
  · rw [dist_pt]; congr 1; ring
  · rw [dist_pt]; congr 1; ring
  · rw [dist_pt]
    congr 1
    rw [hk]
    field_simp
    ring
  · rw [dist_pt]
    congr 1
    rw [hk]
    field_simp
    ring

/-- The horizontal line at height `t` meets the leg from `(a, 0)` to `(b, h)`
exactly at `(a + (b - a) * t / h, t)`. -/
theorem cut_mem_segment (a b h t : ℝ) (hh : 0 < h) (ht0 : 0 ≤ t) (hth : t ≤ h) :
    pt (a + (b - a) * t / h) t ∈ segment ℝ (pt a 0) (pt b h) := by
  have hC : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh.ne'
  refine ⟨1 - t / h, t / h, ?_, div_nonneg ht0 hh.le, by ring, ?_⟩
  · have : t / h ≤ 1 := (div_le_one hh).mpr hth
    linarith
  · simp only [pt, Complex.real_smul]
    push_cast
    field_simp
    ring

/-- Both pieces obtained by cutting the symmetric trapezoid with vertices
`(±a, 0)`, `(±b, h)` along the horizontal line at height `t` are again cyclic
quadrilaterals. -/
theorem cut_pieces_cyclic (a b h t : ℝ) (ht0 : 0 < t) (hth : t < h) :
    (∃ (o : ℂ) (r : ℝ),
      dist (pt a 0) o = r ∧ dist (pt (-a) 0) o = r ∧
      dist (pt (a + (b - a) * t / h) t) o = r ∧
      dist (pt (-(a + (b - a) * t / h)) t) o = r) ∧
    (∃ (o : ℂ) (r : ℝ),
      dist (pt (a + (b - a) * t / h) t) o = r ∧
      dist (pt (-(a + (b - a) * t / h)) t) o = r ∧
      dist (pt b h) o = r ∧ dist (pt (-b) h) o = r) :=
  ⟨trapezoid_cyclic a (a + (b - a) * t / h) 0 t (ne_of_lt ht0),
   trapezoid_cyclic (a + (b - a) * t / h) b t h (ne_of_lt hth)⟩

end Imo1972P2
