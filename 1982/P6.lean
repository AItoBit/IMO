/-
# IMO 1982, Problem 6 — the quantitative core

`S` is a square of side `100`.  `L` is a non-self-intersecting closed polygonal
path `A₀A₁ … Aₙ` inside `S` (`A₀ = Aₙ`) such that every point of the boundary of
`S` is within `1/2` of some point of `L`.  Prove that there are two points `X`,
`Y` of `L` with `dist X Y ≤ 1` and with the part of `L` between `X` and `Y` of
length at least `198`.

## Honest scope note

This is not a one-pass formalization,  is a sketch rather
than a proof.  A faithful statement needs an arc-length parametrisation of a
polygonal path and the notion of "the part of `L` between `X` and `Y`", roughly:

```
theorem imo1982_p6 (n : ℕ) (A : ℕ → EuclideanSpace ℝ (Fin 2))
    (S : Set (EuclideanSpace ℝ (Fin 2))) (hS : IsSquareOfSide S 100)
    (hclosed : A n = A 0) (hin : ∀ i ≤ n, A i ∈ S)
    (hsimple : Set.InjOn (param A) (Set.Ico 0 1))          -- `L` does not meet itself
    (hcover : ∀ p ∈ frontier S, ∃ t ∈ Set.Icc (0:ℝ) 1, dist p (param A t) ≤ 1/2) :
    ∃ s t : ℝ, s ∈ Set.Icc (0:ℝ) 1 ∧ t ∈ Set.Icc (0:ℝ) 1 ∧ s ≤ t ∧
      dist (param A s) (param A t) ≤ 1 ∧
      198 ≤ eVariationOn (param A) (Set.Icc s t)
```

and the two genuinely hard steps of the argument are the ones the write-up
hand-waves:

* "`L` must subsequently approach both `B'` and `D'`" — this uses the covering
  hypothesis at *all four* vertices and the simplicity of `L`;
* "by compactness `X'` itself must be approached by `L₂`" — the set of boundary
  points approached by a sub-path is closed, which needs an argument.

What follows compiles with no `sorry` and is the final paragraph of the
solution, made precise: once the three points are in place, the two conclusions
are pure metric-space estimates.  (`X` and `Y` are taken to be vertices `A j`,
`A k` here; in the problem they may lie inside segments, which only adds
bookkeeping — one splits the two containing segments.)
-/

import Mathlib

namespace Imo1982P6

variable {P : Type*} [PseudoMetricSpace P]

/-- The length of the portion of the polygonal path `A` between indices `j` and
`k`. -/
noncomputable def plen (A : ℕ → P) (j k : ℕ) : ℝ :=
  ∑ i ∈ Finset.Ico j k, dist (A i) (A (i + 1))

theorem plen_add (A : ℕ → P) {j m k : ℕ} (h1 : j ≤ m) (h2 : m ≤ k) :
    plen A j m + plen A m k = plen A j k :=
  Finset.sum_Ico_consecutive _ h1 h2

/-- A polygonal path is at least as long as the distance between its endpoints. -/
theorem dist_le_plen (A : ℕ → P) {j k : ℕ} (h : j ≤ k) :
    dist (A j) (A k) ≤ plen A j k := by
  induction k, h using Nat.le_induction with
  | base => simp [plen]
  | succ m hm ih =>
    have h1 : plen A j (m + 1) = plen A j m + dist (A m) (A (m + 1)) := by
      rw [plen, plen, Finset.sum_Ico_succ_top hm]
    calc dist (A j) (A (m + 1)) ≤ dist (A j) (A m) + dist (A m) (A (m + 1)) :=
          dist_triangle _ _ _
      _ ≤ plen A j m + dist (A m) (A (m + 1)) := by linarith
      _ = plen A j (m + 1) := h1.symm

/-- If `p` is within `1/2` of `Z`, `q` is within `1/2` of `B`, and `Z`, `B` are
at least `100` apart, then `p` and `q` are at least `99` apart. -/
private theorem far {p q Z B : P} (hp : dist p Z ≤ 1 / 2) (hq : dist q B ≤ 1 / 2)
    (h : 100 ≤ dist Z B) : 99 ≤ dist p q := by
  have t1 : dist Z B ≤ dist Z p + dist p B := dist_triangle _ _ _
  have t2 : dist p B ≤ dist p q + dist q B := dist_triangle _ _ _
  have e : dist Z p = dist p Z := dist_comm _ _
  linarith

/-- **IMO 1982, Problem 6 — the estimate.**  Suppose the vertices `A j` and
`A k` of the path both lie within `1/2` of one boundary point `Z`, that an
intermediate vertex `A m` lies within `1/2` of a point `B` at distance at least
`100` from `Z` (a far vertex of the square).  Then `A j` and `A k` are at
distance at most `1`, while the part of the path between them has length at
least `198`. -/
theorem imo1982_p6_estimate (A : ℕ → P) {j m k : ℕ} (hjm : j ≤ m) (hmk : m ≤ k)
    (Z B : P) (hXZ : dist (A j) Z ≤ 1 / 2) (hYZ : dist (A k) Z ≤ 1 / 2)
    (hB : dist (A m) B ≤ 1 / 2) (hZB : 100 ≤ dist Z B) :
    dist (A j) (A k) ≤ 1 ∧ 198 ≤ plen A j k := by
  constructor
  · have t : dist (A j) (A k) ≤ dist (A j) Z + dist Z (A k) := dist_triangle _ _ _
    have e : dist Z (A k) = dist (A k) Z := dist_comm _ _
    linarith
  · have h1 : 99 ≤ dist (A j) (A m) := far hXZ hB hZB
    have h2 : 99 ≤ dist (A k) (A m) := far hYZ hB hZB
    have h2' : 99 ≤ dist (A m) (A k) := by rwa [dist_comm] at h2
    have h3 := dist_le_plen A hjm
    have h4 := dist_le_plen A hmk
    have h5 := plen_add A hjm hmk
    linarith

end Imo1982P6
