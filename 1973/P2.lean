/-
# IMO 1973, Problem 2

Determine whether or not there exists a finite set `M` of points in space, not
all in one plane, such that for any two points `A, B ∈ M` one can select two
other points `C, D ∈ M` with `AB` and `CD` parallel and not coincident.

The answer is **yes**, and the AoPS construction is the `3 × 3 × 3` grid
`{-1, 0, 1}³` (equivalently: the vertices, edge midpoints, face centres and
centre of a cube).

## Modelling

Points are taken in `ℤ³ ⊆ ℝ³`; all the notions involved are linear-algebraic
and unchanged by that inclusion:

* `AB ∥ CD` (as directions) is `(B - A) × (D - C) = 0` — for nonzero `B - A`
  and `D - C` this is exactly parallelism;
* the two lines are **not coincident** iff `C` is off the line `AB`, i.e.
  `(C - A) × (B - A) ≠ 0`;
* "not all in one plane" is the existence of `A, B, C, D ∈ M` with
  `det (B - A, C - A, D - A) ≠ 0`, i.e. the affine span is all of space.

## Proof

Rather than searching for `C, D` (which would make the kernel check `27⁴`
candidate quadruples), the witness is produced by an explicit function `wit`.
Write `v = B - A`.

* If some coordinate `i` has `vᵢ = 0`, translate the whole segment by `±eᵢ`
  (the sign chosen to stay inside `{-1,0,1}`).  Then `D - C = v`, and
  `±eᵢ` is not parallel to `v` because `v ≠ 0` has a nonzero coordinate `≠ i`.
* Otherwise, if some coordinate has `|vᵢ| = 1`, translate by `±eᵢ` again; here
  every other coordinate of `v` is nonzero, so again `eᵢ ∦ v`.
* Otherwise `|vᵢ| = 2` for all `i`, so `A ∈ {-1,1}³` and `B = -A` (a long
  diagonal).  Take `C = (-a₁, 0, 0)`, `D = (0, a₂, a₃)`: then `D - C = A`, which
  is parallel to `v = -2A`, and `C` is not on the line `{tA}`.

With `wit` in hand the whole statement is a check over the `27 × 27` pairs,
which `decide` performs.
-/

import Mathlib

set_option maxRecDepth 100000

namespace Imo1973P2

open Finset

/-- Points of space, with integer coordinates. -/
abbrev Pt := ℤ × ℤ × ℤ

/-- Difference of two points. -/
def sub (A B : Pt) : Pt := (A.1 - B.1, A.2.1 - B.2.1, A.2.2 - B.2.2)

/-- Cross product; it vanishes exactly on parallel pairs. -/
def cross (u v : Pt) : Pt :=
  (u.2.1 * v.2.2 - u.2.2 * v.2.1,
   u.2.2 * v.1 - u.1 * v.2.2,
   u.1 * v.2.1 - u.2.1 * v.1)

/-- Determinant of three vectors; it vanishes exactly when they are coplanar. -/
def det (u v w : Pt) : ℤ :=
  u.1 * (v.2.1 * w.2.2 - v.2.2 * w.2.1)
    - u.2.1 * (v.1 * w.2.2 - v.2.2 * w.1)
    + u.2.2 * (v.1 * w.2.1 - v.2.1 * w.1)

/-- The `3 × 3 × 3` grid `{-1, 0, 1}³`. -/
def M : Finset Pt :=
  ({-1, 0, 1} : Finset ℤ) ×ˢ (({-1, 0, 1} : Finset ℤ) ×ˢ ({-1, 0, 1} : Finset ℤ))

/-- The shift `±1` that keeps both `a` and `b` inside `{-1, 0, 1}`, when
`|a - b| ≤ 1`. -/
def sh (a b : ℤ) : ℤ := if a ≤ 0 ∧ b ≤ 0 then 1 else -1

/-- The explicit choice of the second pair `(C, D)` for a given pair `(A, B)`. -/
def wit (A B : Pt) : Pt × Pt :=
  if A.1 = B.1 then
    ((A.1 + sh A.1 B.1, A.2.1, A.2.2), (B.1 + sh A.1 B.1, B.2.1, B.2.2))
  else if A.2.1 = B.2.1 then
    ((A.1, A.2.1 + sh A.2.1 B.2.1, A.2.2), (B.1, B.2.1 + sh A.2.1 B.2.1, B.2.2))
  else if A.2.2 = B.2.2 then
    ((A.1, A.2.1, A.2.2 + sh A.2.2 B.2.2), (B.1, B.2.1, B.2.2 + sh A.2.2 B.2.2))
  else if A.1 - B.1 = 1 ∨ B.1 - A.1 = 1 then
    ((A.1 + sh A.1 B.1, A.2.1, A.2.2), (B.1 + sh A.1 B.1, B.2.1, B.2.2))
  else if A.2.1 - B.2.1 = 1 ∨ B.2.1 - A.2.1 = 1 then
    ((A.1, A.2.1 + sh A.2.1 B.2.1, A.2.2), (B.1, B.2.1 + sh A.2.1 B.2.1, B.2.2))
  else if A.2.2 - B.2.2 = 1 ∨ B.2.2 - A.2.2 = 1 then
    ((A.1, A.2.1, A.2.2 + sh A.2.2 B.2.2), (B.1, B.2.1, B.2.2 + sh A.2.2 B.2.2))
  else
    ((-A.1, 0, 0), (0, A.2.1, A.2.2))

/-- The whole verification, as a finite check over the `27 × 27` pairs. -/
private lemma wit_spec : ∀ A ∈ M, ∀ B ∈ M, A ≠ B →
    (wit A B).1 ∈ M ∧ (wit A B).2 ∈ M ∧ (wit A B).1 ≠ (wit A B).2 ∧
      cross (sub B A) (sub (wit A B).2 (wit A B).1) = (0, 0, 0) ∧
      cross (sub (wit A B).1 A) (sub B A) ≠ (0, 0, 0) := by
  decide

/-- **IMO 1973, Problem 2.**  Such a set exists. -/
theorem imo1973_p2 :
    ∃ M : Finset Pt,
      (∃ A ∈ M, ∃ B ∈ M, ∃ C ∈ M, ∃ D ∈ M,
          det (sub B A) (sub C A) (sub D A) ≠ 0) ∧
      (∀ A ∈ M, ∀ B ∈ M, A ≠ B → ∃ C ∈ M, ∃ D ∈ M, C ≠ D ∧
          cross (sub B A) (sub D C) = (0, 0, 0) ∧
          cross (sub C A) (sub B A) ≠ (0, 0, 0)) := by
  refine ⟨M, ?_, ?_⟩
  · exact ⟨(0, 0, 0), by decide, (1, 0, 0), by decide, (0, 1, 0), by decide,
      (0, 0, 1), by decide, by decide⟩
  · intro A hA B hB hAB
    obtain ⟨h1, h2, h3, h4, h5⟩ := wit_spec A hA B hB hAB
    exact ⟨(wit A B).1, h1, (wit A B).2, h2, h3, h4, h5⟩

end Imo1973P2
