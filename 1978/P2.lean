/-
# IMO 1978, Problem 2

`P` is a point inside a fixed sphere of centre `O` and radius `R`.  Three
mutually perpendicular segments `PA`, `PB`, `PC` have `A, B, C` on the sphere,
and `Q` is the vertex opposite `P` in the right parallelepiped with edges
`PA, PB, PC`.  Find the locus of `Q`.

Answer: the sphere centred at `O` of radius `√(3R² − 2·OP²)`.

## Honest scope note

"Locus" has two halves, and they are of completely different difficulty.

* **Forward** (every such `Q` lies on that sphere).  Proved below, with no
  `sorry`, and in *any* real inner product space — the dimension plays no role.
* **Converse** (every point of that sphere arises as such a `Q`).  This is the
  hard half; the AoPS page says so explicitly in Remark 1b, and its Solution 1
  is simply wrong (Remark 1a: it silently assumes `O, P, A, B` coplanar).
  Solution 2 does prove it, but through a long coordinate construction: solve
  the planar case with a `tan(α/2)` substitution and a discriminant check, then
  build an auxiliary point `D` with `QD² = 1 − a²`, `QD ⊥ OD`, `QD ⊥ OP` by
  solving a quadratic whose discriminant is `4a⁴ + q₂²(1 − a²) ≥ 0`, and finally
  reduce to the planar case in the plane `DOP`.

  In vector terms the converse is: given `s = Q − P` with
  `‖s‖² + 2⟪p, s⟫ = 3(R² − ‖p‖²)` (`p = P − O`), find an orthonormal frame in
  which the symmetric form `x ↦ ⟪s, x⟫² + 2⟪s, x⟫⟪p, x⟫` has constant diagonal.
  That is the classical "orthogonally equalise the diagonal of a symmetric
  matrix" statement, which Mathlib does not have; formalizing it is a project,
  not a file.  The full statement would read

  ```
  theorem imo1978_p2_locus (O P Q : EuclideanSpace ℝ (Fin 3)) (R : ℝ)
      (hP : dist P O < R) :
      (∃ A B C, dist A O = R ∧ dist B O = R ∧ dist C O = R ∧
          ⟪A - P, B - P⟫_ℝ = 0 ∧ ⟪B - P, C - P⟫_ℝ = 0 ∧ ⟪C - P, A - P⟫_ℝ = 0 ∧
          Q = P + (A - P) + (B - P) + (C - P))
        ↔ dist Q O = Real.sqrt (3 * R ^ 2 - 2 * dist P O ^ 2)
  ```

## Proof of the forward half

Put the origin at `O` and write `p = P − O`, `u = A − P`, `v = B − P`,
`w = C − P`.  Then `A − O = p + u` and `Q − O = p + u + v + w`, and

  `‖p+u‖² = ‖p‖² + 2⟪p,u⟫ + ‖u‖² = R²`,

so `‖u‖² + 2⟪p,u⟫ = R² − ‖p‖²`, and likewise for `v, w`.  Expanding

  `‖p+u+v+w‖² = ‖p‖² + Σ (‖x‖² + 2⟪p,x⟫) + 2(⟪u,v⟫ + ⟪v,w⟫ + ⟪w,u⟫)`

the last bracket vanishes by perpendicularity, giving
`‖p‖² + 3(R² − ‖p‖²) = 3R² − 2‖p‖²`.

No angles, no coordinates, no case analysis — which is exactly what goes wrong
in the AoPS Solution 1.
-/

import Mathlib

open scoped RealInnerProductSpace

namespace Imo1978P2

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The computation, in inner-product form. -/
private lemma key (p u v w : V) (R : ℝ)
    (hu : ⟪p + u, p + u⟫ = R ^ 2) (hv : ⟪p + v, p + v⟫ = R ^ 2)
    (hw : ⟪p + w, p + w⟫ = R ^ 2)
    (huv : ⟪u, v⟫ = 0) (hvw : ⟪v, w⟫ = 0) (hwu : ⟪w, u⟫ = 0) :
    ⟪p + u + v + w, p + u + v + w⟫ = 3 * R ^ 2 - 2 * ⟪p, p⟫ := by
  simp only [inner_add_left, inner_add_right] at hu hv hw ⊢
  linarith [real_inner_comm p u, real_inner_comm p v, real_inner_comm p w,
    real_inner_comm u v, real_inner_comm v w, real_inner_comm w u]

/-- **IMO 1978, Problem 2** (forward half).  With `A, B, C` on the sphere of
centre `O` and radius `R`, the segments `PA, PB, PC` pairwise perpendicular and
`Q` the opposite vertex of the parallelepiped, `OQ² = 3R² − 2·OP²`. -/
theorem imo1978_p2 (O P A B C Q : V) (R : ℝ)
    (hA : dist A O = R) (hB : dist B O = R) (hC : dist C O = R)
    (hab : ⟪A - P, B - P⟫ = 0) (hbc : ⟪B - P, C - P⟫ = 0) (hca : ⟪C - P, A - P⟫ = 0)
    (hQ : Q = P + (A - P) + (B - P) + (C - P)) :
    dist Q O ^ 2 = 3 * R ^ 2 - 2 * dist P O ^ 2 := by
  have e1 : A - O = (P - O) + (A - P) := by abel
  have e2 : B - O = (P - O) + (B - P) := by abel
  have e3 : C - O = (P - O) + (C - P) := by abel
  have e4 : Q - O = (P - O) + (A - P) + (B - P) + (C - P) := by rw [hQ]; abel
  have hu : ⟪(P - O) + (A - P), (P - O) + (A - P)⟫ = R ^ 2 := by
    rw [← e1, real_inner_self_eq_norm_sq, ← dist_eq_norm, hA]
  have hv : ⟪(P - O) + (B - P), (P - O) + (B - P)⟫ = R ^ 2 := by
    rw [← e2, real_inner_self_eq_norm_sq, ← dist_eq_norm, hB]
  have hw : ⟪(P - O) + (C - P), (P - O) + (C - P)⟫ = R ^ 2 := by
    rw [← e3, real_inner_self_eq_norm_sq, ← dist_eq_norm, hC]
  have hmain := key (P - O) (A - P) (B - P) (C - P) R hu hv hw hab hbc hca
  rw [dist_eq_norm, dist_eq_norm, ← real_inner_self_eq_norm_sq,
    ← real_inner_self_eq_norm_sq, e4]
  exact hmain

/-- The same statement as a distance: `Q` lies on the sphere of centre `O` and
radius `√(3R² − 2·OP²)`. -/
theorem imo1978_p2_dist (O P A B C Q : V) (R : ℝ)
    (hA : dist A O = R) (hB : dist B O = R) (hC : dist C O = R)
    (hab : ⟪A - P, B - P⟫ = 0) (hbc : ⟪B - P, C - P⟫ = 0) (hca : ⟪C - P, A - P⟫ = 0)
    (hQ : Q = P + (A - P) + (B - P) + (C - P)) :
    dist Q O = Real.sqrt (3 * R ^ 2 - 2 * dist P O ^ 2) := by
  rw [← imo1978_p2 O P A B C Q R hA hB hC hab hbc hca hQ, Real.sqrt_sq dist_nonneg]

end Imo1978P2
