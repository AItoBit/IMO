/-
# IMO 1965 Problem 6 — the diameter graph

Given a finite set `S` of points in the plane whose pairwise distances are all at
most `d`, the number of pairs at distance exactly `d` ("diagonals") is at most `S.card`.

Roadmap, following the handwritten proof:

* handshake:  sum of degrees = twice the number of diagonals
* pigeonhole: more than `n` diagonals forces a point `P` of degree `≥ 3`
* geometry:   among the three neighbours of `P` there is a "middle" one `Q`
              whose only diagonal is `PQ`
* descent:    erase `Q`; one point and one diagonal disappear, contradicting minimality

Only the *combinatorial* steps are proved here. The geometric step is taken as an
explicit hypothesis `MiddlePoint`, stated exactly as the handwritten argument needs it.
There is no `sorry` and no `axiom` in this file: the main theorem is conditional.

Counting convention: `pairCount S d` counts **ordered** pairs, so each diagonal is
counted twice and the bound reads `pairCount S d ≤ 2 * S.card`.
-/

import Mathlib

open Finset

open scoped Classical

noncomputable section

/-- The Euclidean plane. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The number of points of `S` joined to `P` by a segment of length `d`
(the "diagonal degree" of `P`). -/
def deg (S : Finset Plane) (d : ℝ) (P : Plane) : ℕ :=
  (S.filter fun y => dist P y = d).card

/-- Ordered pairs of points of `S` at distance exactly `d`.
Each diagonal contributes `2`. -/
def pairCount (S : Finset Plane) (d : ℝ) : ℕ :=
  ((S ×ˢ S).filter fun p => dist p.1 p.2 = d).card

/-! ## Handshake -/

/-- Sum of the diagonal degrees counts each diagonal twice. -/
theorem pairCount_eq_sum_deg (S : Finset Plane) (d : ℝ) :
    pairCount S d = ∑ x ∈ S, deg S d x := by
  unfold pairCount deg
  rw [Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun x _ => ?_
  exact (Finset.card_filter _ _).symm

/-! ## Removing one point -/

/-- Deleting `Q` from the ambient set lowers the degree of `x` by one exactly when
`x` and `Q` are joined by a diagonal. -/
theorem deg_erase (S : Finset Plane) (d : ℝ) {Q : Plane} (hQ : Q ∈ S) (x : Plane) :
    deg S d x = deg (S.erase Q) d x + (if dist x Q = d then 1 else 0) := by
  unfold deg
  have hfe : (S.erase Q).filter (fun y => dist x y = d)
      = (S.filter (fun y => dist x y = d)).erase Q := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_erase]
    tauto
  rw [hfe]
  split_ifs with h
  · have hmem : Q ∈ S.filter (fun y => dist x y = d) := Finset.mem_filter.mpr ⟨hQ, h⟩
    exact (Finset.card_erase_add_one hmem).symm
  · have hmem : Q ∉ S.filter (fun y => dist x y = d) := by
      simp only [Finset.mem_filter, not_and]
      exact fun _ => h
    rw [Finset.erase_eq_self.mpr hmem, Nat.add_zero]

/-- Erasing a point destroys exactly its own diagonals. -/
theorem pairCount_erase (S : Finset Plane) {d : ℝ} (hd : 0 < d) {Q : Plane} (hQ : Q ∈ S) :
    pairCount S d = pairCount (S.erase Q) d + 2 * deg S d Q := by
  have hQQ : dist Q Q ≠ d := by
    rw [dist_self]; exact ne_of_lt hd
  have h1 : ∑ x ∈ S, deg S d x = deg S d Q + ∑ x ∈ S.erase Q, deg S d x :=
    (Finset.add_sum_erase S (deg S d) hQ).symm
  have h2 : ∑ x ∈ S.erase Q, deg S d x
      = ∑ x ∈ S.erase Q, deg (S.erase Q) d x
        + ∑ x ∈ S.erase Q, (if dist x Q = d then 1 else 0) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => deg_erase S d hQ x
  have h3 : ∑ x ∈ S.erase Q, (if dist x Q = d then 1 else 0) = deg S d Q := by
    rw [← Finset.card_filter]
    have hset : (S.erase Q).filter (fun x => dist x Q = d)
        = S.filter (fun y => dist Q y = d) := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨⟨-, hy⟩, hyd⟩
        exact ⟨hy, by rwa [dist_comm]⟩
      · rintro ⟨hy, hyd⟩
        refine ⟨⟨?_, hy⟩, by rwa [dist_comm]⟩
        rintro rfl
        exact hQQ hyd
    rw [hset]
    rfl
  rw [pairCount_eq_sum_deg, pairCount_eq_sum_deg, h1, h2, h3]
  ring

/-! ## Pigeonhole -/

/-- More than `n` diagonals on `n` points forces a point of diagonal degree at least `3`. -/
theorem exists_deg_three {S : Finset Plane} {d : ℝ} (h : 2 * S.card < pairCount S d) :
    ∃ P ∈ S, 3 ≤ deg S d P := by
  by_contra hcon
  have hcon' : ∀ P ∈ S, deg S d P ≤ 2 := fun P hP => by
    by_contra hP3
    exact hcon ⟨P, hP, by omega⟩
  have hle : pairCount S d ≤ 2 * S.card := by
    rw [pairCount_eq_sum_deg]
    calc ∑ x ∈ S, deg S d x
        ≤ ∑ _x ∈ S, 2 := Finset.sum_le_sum fun x hx => hcon' x hx
      _ = 2 * S.card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  omega

/-! ## The geometric input -/

/-- The "middle point" property extracted from the plane geometry. -/
def MiddlePoint (d : ℝ) : Prop :=
  ∀ S : Finset Plane, (∀ x ∈ S, ∀ y ∈ S, dist x y ≤ d) →
    ∀ P ∈ S, 3 ≤ deg S d P → ∃ Q ∈ S, dist P Q = d ∧ deg S d Q = 1

/-! ## Main theorem -/

/-- **IMO 1965, Problem 6.** If every pairwise distance in the finite set `S` is at
most `d`, then the number of pairs at distance exactly `d` is at most `S.card`
(stated with the ordered-pair count, hence the factor `2` on both sides). -/
theorem imo1965_p6 {d : ℝ} (hd : 0 < d) (geom : MiddlePoint d) :
    ∀ S : Finset Plane, (∀ x ∈ S, ∀ y ∈ S, dist x y ≤ d) →
      pairCount S d ≤ 2 * S.card := by
  intro S
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    intro hS
    rcases le_or_gt (pairCount S d) (2 * S.card) with hle | hcon
    · exact hle
    · exfalso
      obtain ⟨P, hPS, hP3⟩ := exists_deg_three hcon
      obtain ⟨Q, hQS, hPQ, hQ1⟩ := geom S hS P hPS hP3
      have hcard : 1 ≤ S.card := Finset.card_pos.mpr ⟨Q, hQS⟩
      have hsub : S.erase Q ⊂ S := Finset.erase_ssubset hQS
      have hrec : pairCount (S.erase Q) d ≤ 2 * (S.erase Q).card :=
        ih _ hsub fun x hx y hy =>
          hS x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy)
      have hsplit := pairCount_erase S hd hQS
      rw [hQ1] at hsplit
      rw [Finset.card_erase_of_mem hQS] at hrec
      omega

end
