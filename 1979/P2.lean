import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Imo1979P2

/-!
# IMO 1979, Problem 2

We consider a prism whose upper and lower bases are the pentagons `A₁A₂A₃A₄A₅` and
`B₁B₂B₃B₄B₅`.  Each of the ten sides of the two pentagons and each of the twenty-five
segments `AᵢBⱼ` is coloured red or blue.  Assume that in every triangle all of whose
sides are coloured, there is a red side and a blue side.  Then all ten sides of the two
pentagons have the same colour.

Formalisation.  Colours are modelled by `Bool`.

* `a i` is the colour of the pentagon side `Aᵢ Aᵢ₊₁`,
* `b j` is the colour of the pentagon side `Bⱼ Bⱼ₊₁`,
* `c i j` is the colour of the segment `Aᵢ Bⱼ`,

with indices in `Fin 5`, so that `i + 1` is the cyclic successor.  The triangles all of
whose sides are coloured are exactly the triangles `Aᵢ Aᵢ₊₁ Bⱼ` (with sides `a i`,
`c i j`, `c (i+1) j`) and `Aᵢ Bⱼ Bⱼ₊₁` (with sides `b j`, `c i j`, `c i (j+1)`); the
hypothesis says that these are not monochromatic.
-/

/-- On a 5-cycle, any two-colouring of the vertices has two adjacent vertices of the
same colour (the 5-cycle is not bipartite). -/
lemma exists_adj_eq (q : Fin 5 → Bool) : ∃ j : Fin 5, q j = q (j + 1) := by
  revert q; decide

/-- A set of vertices of a 5-cycle containing no two adjacent vertices has at most two
elements. -/
lemma indep_le_two (p : Fin 5 → Bool) (h : ∀ i : Fin 5, ¬ (p i = true ∧ p (i + 1) = true)) :
    (∑ i : Fin 5, if p i then 1 else 0) ≤ 2 := by
  revert p; decide

variable {a b : Fin 5 → Bool} {c : Fin 5 → Fin 5 → Bool}

/-- Neighbouring sides of the pentagon `A₁A₂A₃A₄A₅` have the same colour. -/
lemma a_succ_eq
    (hA : ∀ i j : Fin 5, ¬ (a i = c i j ∧ a i = c (i + 1) j))
    (hB : ∀ i j : Fin 5, ¬ (b j = c i j ∧ b j = c i (j + 1)))
    (i : Fin 5) : a (i + 1) = a i := by
  by_contra hne
  -- two cyclically adjacent `j`s with the segments `Aᵢ₊₁ Bⱼ`, `Aᵢ₊₁ Bⱼ₊₁` of equal colour `X`
  obtain ⟨j, hj⟩ := exists_adj_eq (fun j => c (i + 1) j)
  -- the triangle `Aᵢ₊₁ Bⱼ Bⱼ₊₁` forces `b j ≠ X`
  have e1 := hB (i + 1) j
  -- the triangles `Aᵢ Aᵢ₊₁ Bⱼ` and `Aᵢ Aᵢ₊₁ Bⱼ₊₁`
  have e2 := hA i j
  have e3 := hA i (j + 1)
  -- the triangle `Aᵢ Bⱼ Bⱼ₊₁`
  have e4 := hB i j
  -- the triangles `Aᵢ₊₁ Aᵢ₊₂ Bⱼ` and `Aᵢ₊₁ Aᵢ₊₂ Bⱼ₊₁`
  have e5 := hA (i + 1) j
  have e6 := hA (i + 1) (j + 1)
  -- the triangle `Aᵢ₊₂ Bⱼ Bⱼ₊₁`
  have e7 := hB (i + 1 + 1) j
  clear hA hB
  cases h1 : a i <;> cases h2 : a (i + 1) <;> cases h3 : b j <;>
    cases h4 : c i j <;> cases h5 : c i (j + 1) <;> cases h6 : c (i + 1) j <;>
    cases h7 : c (i + 1) (j + 1) <;> cases h8 : c (i + 1 + 1) j <;>
    cases h9 : c (i + 1 + 1) (j + 1) <;> simp_all

/-- All five sides of the pentagon `A₁A₂A₃A₄A₅` have the same colour. -/
lemma a_const
    (hA : ∀ i j : Fin 5, ¬ (a i = c i j ∧ a i = c (i + 1) j))
    (hB : ∀ i j : Fin 5, ¬ (b j = c i j ∧ b j = c i (j + 1)))
    (i : Fin 5) : a i = a 0 := by
  have h := a_succ_eq hA hB
  have h0 : a 1 = a 0 := by simpa using h 0
  have h1 : a 2 = a 1 := by simpa using h 1
  have h2 : a 3 = a 2 := by simpa using h 2
  have h3 : a 4 = a 3 := by simpa using h 3
  fin_cases i <;> simp_all

/-- All five sides of the pentagon `B₁B₂B₃B₄B₅` have the same colour. -/
lemma b_const
    (hA : ∀ i j : Fin 5, ¬ (a i = c i j ∧ a i = c (i + 1) j))
    (hB : ∀ i j : Fin 5, ¬ (b j = c i j ∧ b j = c i (j + 1)))
    (j : Fin 5) : b j = b 0 :=
  a_const (a := b) (b := a) (c := fun j i => c i j) (fun i j => hB j i) (fun i j => hA j i) j

/-- **IMO 1979, Problem 2.** All ten sides of the two pentagons are coloured with the
same colour. -/
theorem imo1979_p2
    (hA : ∀ i j : Fin 5, ¬ (a i = c i j ∧ a i = c (i + 1) j))
    (hB : ∀ i j : Fin 5, ¬ (b j = c i j ∧ b j = c i (j + 1))) :
    ∃ col : Bool, (∀ i, a i = col) ∧ (∀ j, b j = col) := by
  refine ⟨a 0, a_const hA hB, fun j => ?_⟩
  rw [b_const hA hB j]
  -- it remains to show that the two pentagons have the same colour
  by_contra hne
  set A : Bool := a 0 with hAdef
  have hb0 : b 0 = !A := by cases h1 : b 0 <;> cases h2 : A <;> simp_all
  -- in each "column" `j`, no two adjacent `Aᵢ B_j`, `Aᵢ₊₁ B_j` are of colour `A`
  have hred : ∀ j : Fin 5, (∑ i : Fin 5, if c i j = A then 1 else 0) ≤ 2 := by
    intro j
    have := indep_le_two (fun i => decide (c i j = A)) (by
      intro i ⟨h1, h2⟩
      simp only [decide_eq_true_eq] at h1 h2
      exact hA i j ⟨by rw [h1, a_const hA hB i], by rw [h2, a_const hA hB i]⟩)
    simpa using this
  -- in each "row" `i`, no two adjacent `Aᵢ B_j`, `Aᵢ B_{j+1}` are of colour `!A`
  have hblue : ∀ i : Fin 5, (∑ j : Fin 5, if c i j = A then 0 else 1) ≤ 2 := by
    intro i
    have := indep_le_two (fun j => !decide (c i j = A)) (by
      intro j ⟨h1, h2⟩
      simp only [Bool.not_eq_true', decide_eq_false_iff_not] at h1 h2
      refine hB i j ⟨?_, ?_⟩
      · rw [b_const hA hB j, hb0]
        cases h : c i j <;> cases h' : A <;> simp_all
      · rw [b_const hA hB j, hb0]
        cases h : c i (j + 1) <;> cases h' : A <;> simp_all)
    simpa using this
  -- counting: there are 25 segments, at most 10 of each colour
  have hsum1 : (∑ i : Fin 5, ∑ j : Fin 5, if c i j = A then 1 else 0) ≤ 10 := by
    rw [Finset.sum_comm]
    calc (∑ j : Fin 5, ∑ i : Fin 5, if c i j = A then 1 else 0)
        ≤ ∑ _j : Fin 5, 2 := Finset.sum_le_sum (fun j _ => hred j)
      _ = 10 := by simp
  have hsum2 : (∑ i : Fin 5, ∑ j : Fin 5, if c i j = A then 0 else 1) ≤ 10 := by
    calc (∑ i : Fin 5, ∑ j : Fin 5, if c i j = A then 0 else 1)
        ≤ ∑ _i : Fin 5, 2 := Finset.sum_le_sum (fun i _ => hblue i)
      _ = 10 := by simp
  have htot : (∑ i : Fin 5, ∑ j : Fin 5, if c i j = A then 1 else 0)
      + (∑ i : Fin 5, ∑ j : Fin 5, if c i j = A then 0 else 1) = 25 := by
    rw [← Finset.sum_add_distrib]
    have : ∀ i : Fin 5, ((∑ j : Fin 5, if c i j = A then 1 else 0)
        + ∑ j : Fin 5, if c i j = A then 0 else 1) = 5 := by
      intro i
      rw [← Finset.sum_add_distrib]
      have : ∀ j : Fin 5, ((if c i j = A then 1 else 0) + (if c i j = A then 0 else 1)) = 1 := by
        intro j; by_cases h : c i j = A <;> simp [h]
      rw [Finset.sum_congr rfl (fun j _ => this j)]
      simp
    rw [Finset.sum_congr rfl (fun i _ => this i)]
    simp
  omega

/-- The hypotheses are consistent: an admissible colouring exists (so the theorem above is
not vacuous). -/
lemma exists_admissible_colouring :
    ∃ (a b : Fin 5 → Bool) (c : Fin 5 → Fin 5 → Bool),
      (∀ i j : Fin 5, ¬ (a i = c i j ∧ a i = c (i + 1) j)) ∧
      (∀ i j : Fin 5, ¬ (b j = c i j ∧ b j = c i (j + 1))) :=
  ⟨fun _ => true, fun _ => true, fun _ _ => false, by simp, by simp⟩

end Imo1979P2
