/-
# IMO 1971, Problem 4 — planar-development core

## Honest scope note

Unlike 1971 P2 and P3, this problem does **not** admit a one-pass
formalization.  A faithful statement needs:

* a tetrahedron `A B C D` in `EuclideanSpace ℝ (Fin 3)` with all four faces
  acute;
* the family of closed paths `X Y Z T X` with `X ∈ open segment A B`,
  `Y ∈ open segment B C`, `Z ∈ open segment C D`, `T ∈ open segment D A`;
* the *planar development*: the composite of three rotations unfolding
  `B C D`, `C D A`, `D A B` into the plane of `A B C`, together with the proof
  that it is an isometry on each face, so that path length is preserved;
* for (a), that the infimum of the length is not attained (the development of
  `A B` and of `A' B'` meet, and the straight segment realising the infimum has
  an endpoint outside the *open* edges);
* for (b), that the parallelism `A B ∥ A' B'` is equivalent to
  `∠DAB + ∠BCD = ∠CDA + ∠ABC`, that every `X` then gives a shortest path, and
  that the common length is `dist A A' = 2 * dist A C * sin (α / 2)`.

The development step is the expensive one — there is no unfolding machinery in
Mathlib, so it has to be built (compose `EuclideanGeometry` rotations / use
`AffineIsometryEquiv` glued face by face).  That is a project, not a file.

What follows compiles with no `sorry` and proves the two facts that carry the
actual mathematical content of part (b) once the development is available:

* `dist_eq_two_mul_sin_half_angle` — the chord formula, i.e. the answer
  `2 * AC * sin (α / 2)` (`AC` the equal legs, `α` the apex angle at `C`);
* `length_ge` / `length_ge_two_mul_sin_half` — in the developed plane, any
  four-link path from `X` to its copy `X'` is at least as long as `dist X X'`,
  hence at least `2 * r * sin (α / 2)`.

The full statement, for reference (not compiled, to keep the file `sorry`-free):

```
theorem imo1971_p4a (A B C D : EuclideanSpace ℝ (Fin 3))
    (hacute : AllFacesAcute A B C D)
    (hne : ∠ D A B + ∠ B C D ≠ ∠ C D A + ∠ A B C) :
    ¬ ∃ p ∈ paths A B C D, ∀ q ∈ paths A B C D, length p ≤ length q

theorem imo1971_p4b (A B C D : EuclideanSpace ℝ (Fin 3))
    (hacute : AllFacesAcute A B C D)
    (heq : ∠ D A B + ∠ B C D = ∠ C D A + ∠ A B C) :
    {p ∈ paths A B C D | ∀ q ∈ paths A B C D, length p ≤ length q}.Infinite ∧
    ∀ p ∈ paths A B C D, (∀ q ∈ paths A B C D, length p ≤ length q) →
      length p = 2 * dist A C *
        Real.sin ((∠ B A C + ∠ C A D + ∠ D A B) / 2)
```
-/

import Mathlib

open EuclideanGeometry

namespace Imo1971P4

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MetricSpace P] [NormedAddTorsor V P]

/-- `cos (2 x) = 1 - 2 sin x ^ 2`. -/
private lemma cos_two_mul' (x : ℝ) : Real.cos (2 * x) = 1 - 2 * Real.sin x ^ 2 := by
  rw [Real.cos_two_mul]
  linarith [Real.sin_sq_add_cos_sq x]

/-- **Chord formula.**  In the isosceles triangle with apex `c`, equal legs `r`
and apex angle `∠ a c b`, the base has length `2 * r * sin (∠ a c b / 2)`.

This is the last step of part (b): with `c = C`, `a = A`, `b = A'` (the two
copies of `A` in the development) and `α = ∠ B A C + ∠ C A D + ∠ D A B` the
total angle at `C`, it gives the announced value `2 * AC * sin (α / 2)`. -/
theorem dist_eq_two_mul_sin_half_angle {a b c : P} {r : ℝ}
    (ha : dist a c = r) (hb : dist b c = r) :
    dist a b = 2 * r * Real.sin (∠ a c b / 2) := by
  have hr0 : 0 ≤ r := ha ▸ dist_nonneg
  have hs0 : 0 ≤ Real.sin (∠ a c b / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi
      (by linarith [angle_nonneg a c b])
      (by linarith [angle_le_pi a c b, Real.pi_pos])
  have hcos : Real.cos (∠ a c b) = 1 - 2 * Real.sin (∠ a c b / 2) ^ 2 := by
    have h := cos_two_mul' (∠ a c b / 2)
    rwa [show 2 * (∠ a c b / 2) = ∠ a c b by ring] at h
  have hlaw := EuclideanGeometry.law_cos a c b
  rw [ha, hb] at hlaw
  have hsq : dist a b ^ 2 = (2 * r * Real.sin (∠ a c b / 2)) ^ 2 := by
    rw [pow_two, pow_two, hlaw, hcos]; ring
  have hnn : 0 ≤ 2 * r * Real.sin (∠ a c b / 2) :=
    mul_nonneg (mul_nonneg (by norm_num) hr0) hs0
  calc dist a b = Real.sqrt (dist a b ^ 2) := (Real.sqrt_sq dist_nonneg).symm
    _ = Real.sqrt ((2 * r * Real.sin (∠ a c b / 2)) ^ 2) := by rw [hsq]
    _ = 2 * r * Real.sin (∠ a c b / 2) := Real.sqrt_sq hnn

/-- **Unfolding lower bound.**  In the developed plane, a four-link path
`x → y → z → t → x'` is at least as long as the segment `x x'`. -/
theorem length_ge (x y z t x' : P) :
    dist x x' ≤ dist x y + dist y z + dist z t + dist t x' := by
  have h1 := dist_triangle x y z
  have h2 := dist_triangle x z t
  have h3 := dist_triangle x t x'
  linarith

/-- The two facts combined: every developed path from `x` to `x'`, where `x` and
`x'` are at distance `r` from `c`, has length at least `2 * r * sin (α / 2)`
with `α = ∠ x c x'`.  This is the lower bound of part (b). -/
theorem length_ge_two_mul_sin_half {x y z t x' c : P} {r : ℝ}
    (hx : dist x c = r) (hx' : dist x' c = r) :
    2 * r * Real.sin (∠ x c x' / 2) ≤ dist x y + dist y z + dist z t + dist t x' := by
  rw [← dist_eq_two_mul_sin_half_angle hx hx']
  exact length_ge x y z t x'

end Imo1971P4
