import Mathlib

/-!
# IMO 1992, Problem 3

Nine points in space, no four coplanar. Every pair is joined by an edge, each edge coloured red
or blue or left uncoloured. Find the smallest `n` such that whenever `n` edges are coloured, the
coloured edges must contain a monochromatic triangle.

Answer: `n = 33`.

## Modelling

The "no four coplanar" condition only guarantees that the nine points are in general position; it
plays no role in the combinatorics, so the problem is exactly a statement about `K₉`.

A colouring is `c : Fin 9 → Fin 9 → Option Bool`, symmetric, with `none` meaning "uncoloured".
Edges are the pairs `(i, j)` with `i < j`, so `E.card = 36`; `colored c` is the set of coloured
ones.

The statement proved is `IsLeast S 33` for

  `S = {n | ∀ c symmetric, n ≤ (colored c).card → HasMono c}`.

Phrasing the membership with `≤` rather than `=` makes `S` upward closed, which is what "smallest
`n` such that colouring `n` edges forces a monochromatic triangle" means; the two readings have
the same least element.

## Proof

* **`33 ≤ (colored c).card` forces a triangle.** At most `3` edges are uncoloured. Picking one
  endpoint of each leaves at least `6` points all of whose mutual edges are coloured, and
  `R(3,3) ≤ 6` gives a monochromatic triangle there.
* **`32` does not suffice.** Two squares `R₀R₁R₂R₃` and `B₀B₁B₂B₃` plus a ninth point `X`.
  Colour the sides of the first square red and of the second blue, leaving all four diagonals
  uncoloured; colour `X`–`Rᵢ` blue and `X`–`Bⱼ` red; colour `RᵢBⱼ` red when `i, j` have the same
  parity and blue otherwise. That is `32` coloured edges with no monochromatic triangle, checked
  by `decide`.
-/

open Finset

namespace Imo1992P3

set_option maxRecDepth 100000

/-- The 36 edges of `K₉`, as ordered pairs `i < j`. -/
def E : Finset (Fin 9 × Fin 9) := Finset.univ.filter (fun p => p.1 < p.2)

/-- The coloured edges of a colouring. -/
def colored (c : Fin 9 → Fin 9 → Option Bool) : Finset (Fin 9 × Fin 9) :=
  E.filter (fun p => c p.1 p.2 ≠ none)

/-- There is a triangle all of whose edges carry the same colour. -/
def HasMono (c : Fin 9 → Fin 9 → Option Bool) : Prop :=
  ∃ x y z : Fin 9, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧ ∃ b : Bool,
    c x y = some b ∧ c y z = some b ∧ c x z = some b

instance (c : Fin 9 → Fin 9 → Option Bool) : Decidable (HasMono c) := by
  unfold HasMono
  infer_instance

/-! ### `R(3,3) ≤ 6` -/

theorem ramsey (col : Fin 9 → Fin 9 → Bool) (S : Finset (Fin 9)) (hS : 6 ≤ S.card)
    (_hsym : ∀ i j, col i j = col j i) :
    ∃ x ∈ S, ∃ y ∈ S, ∃ z ∈ S, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      col x y = col y z ∧ col y z = col x z := by
  classical
  obtain ⟨v, hv⟩ : S.Nonempty := Finset.card_pos.1 (by omega)
  have hT : 5 ≤ (S.erase v).card := by
    rw [Finset.card_erase_of_mem hv]; omega
  have hfe : (S.erase v).filter (fun w => col v w = false)
      = (S.erase v).filter (fun w => ¬ (col v w = true)) := by
    refine Finset.filter_congr ?_
    intro w _
    simp
  have hsum : ((S.erase v).filter (fun w => col v w = true)).card
      + ((S.erase v).filter (fun w => col v w = false)).card = (S.erase v).card := by
    rw [hfe]
    exact Finset.card_filter_add_card_filter_not _
  obtain ⟨r, hr⟩ : ∃ r : Bool, 3 ≤ ((S.erase v).filter (fun w => col v w = r)).card := by
    by_contra hcon
    simp only [not_exists, Nat.not_le] at hcon
    have h1 := hcon true
    have h2 := hcon false
    omega
  obtain ⟨U, hUsub, hU3⟩ := Finset.exists_subset_card_eq hr
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.1 hU3
  have hmem : ∀ w ∈ ({x, y, z} : Finset (Fin 9)), w ∈ S ∧ w ≠ v ∧ col v w = r := by
    intro w hw
    have h := hUsub hw
    rw [Finset.mem_filter, Finset.mem_erase] at h
    exact ⟨h.1.2, h.1.1, h.2⟩
  obtain ⟨hxS, hxv, hxr⟩ := hmem x (by simp)
  obtain ⟨hyS, hyv, hyr⟩ := hmem y (by simp)
  obtain ⟨hzS, hzv, hzr⟩ := hmem z (by simp)
  by_cases h1 : col x y = r
  · exact ⟨v, hv, x, hxS, y, hyS, hxv.symm, hxy, hyv.symm, by rw [hxr, h1], by rw [h1, hyr]⟩
  by_cases h2 : col y z = r
  · exact ⟨v, hv, y, hyS, z, hzS, hyv.symm, hyz, hzv.symm, by rw [hyr, h2], by rw [h2, hzr]⟩
  by_cases h3 : col x z = r
  · exact ⟨v, hv, x, hxS, z, hzS, hxv.symm, hxz, hzv.symm, by rw [hxr, h3], by rw [h3, hzr]⟩
  · have hb : ∀ b : Bool, b ≠ r → b = !r := by
      intro b hb
      cases b <;> cases r <;> simp_all
    have e1 : col x y = !r := hb _ h1
    have e2 : col y z = !r := hb _ h2
    have e3 : col x z = !r := hb _ h3
    exact ⟨x, hxS, y, hyS, z, hzS, hxy, hyz, hxz, by rw [e1, e2], by rw [e2, e3]⟩

/-! ### The upper bound -/

theorem upper (c : Fin 9 → Fin 9 → Option Bool) (hsym : ∀ i j, c i j = c j i)
    (hcard : 33 ≤ (colored c).card) : HasMono c := by
  classical
  have hsub : colored c ⊆ E := Finset.filter_subset _ _
  have hE : E.card = 36 := by decide
  have hU : (E \ colored c).card ≤ 3 := by
    rw [Finset.card_sdiff_of_subset hsub, hE]
    omega
  have hTcard : ((E \ colored c).image Prod.fst).card ≤ 3 :=
    le_trans Finset.card_image_le hU
  have hRcard : 6 ≤ (Finset.univ \ (E \ colored c).image Prod.fst).card := by
    have h1 : (Finset.univ \ (E \ colored c).image Prod.fst).card
        = 9 - ((E \ colored c).image Prod.fst).card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
      simp
    omega
  -- every edge inside the remaining points is coloured
  have hkey : ∀ a b : Fin 9, a < b →
      a ∈ Finset.univ \ (E \ colored c).image Prod.fst → c a b ≠ none := by
    intro a b hab ha hc0
    have hmem : (a, b) ∈ E \ colored c := by
      refine Finset.mem_sdiff.2 ⟨?_, ?_⟩
      · simpa [E] using hab
      · simp [colored, hc0]
    exact (Finset.mem_sdiff.1 ha).2 (Finset.mem_image.2 ⟨(a, b), hmem, rfl⟩)
  have hcol : ∀ i ∈ Finset.univ \ (E \ colored c).image Prod.fst,
      ∀ j ∈ Finset.univ \ (E \ colored c).image Prod.fst, i ≠ j → c i j ≠ none := by
    intro i hi j hj hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact hkey i j h hi
    · rw [hsym]
      exact hkey j i h hj
  obtain ⟨S, hSsub, hS6⟩ := Finset.exists_subset_card_eq hRcard
  have hcolS : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → c i j ≠ none :=
    fun i hi j hj hij => hcol i (hSsub hi) j (hSsub hj) hij
  have hval : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → c i j = some ((c i j).getD true) := by
    intro i hi j hj hij
    have h := hcolS i hi j hj hij
    cases hc : c i j with
    | none => exact absurd hc h
    | some b => simp
  have hcolsym : ∀ i j : Fin 9, (c i j).getD true = (c j i).getD true := by
    intro i j; rw [hsym]
  obtain ⟨x, hx, y, hy, z, hz, hxy, hyz, hxz, e1, e2⟩ :=
    ramsey (fun i j => (c i j).getD true) S (by omega) hcolsym
  refine ⟨x, y, z, hxy, hyz, hxz, (c x y).getD true, hval x hx y hy hxy, ?_, ?_⟩
  · rw [hval y hy z hz hyz, ← e1]
  · rw [hval x hx z hz hxz, ← e2, ← e1]

/-! ### The extremal colouring on 32 edges -/

/-- Two squares `0123` (red sides) and `4567` (blue sides) with all diagonals uncoloured,
plus `8` joined to the first square in blue and to the second in red, and `RᵢBⱼ` red exactly
when the indices have the same parity. -/
def ex : Fin 9 → Fin 9 → Option Bool := fun i j =>
  if (i : ℕ) = (j : ℕ) then none
  else if (i : ℕ) = 8 then (if (j : ℕ) < 4 then some false else some true)
  else if (j : ℕ) = 8 then (if (i : ℕ) < 4 then some false else some true)
  else if (i : ℕ) < 4 ∧ (j : ℕ) < 4 then
    (if ((i : ℕ) + (j : ℕ)) % 2 = 1 then some true else none)
  else if 4 ≤ (i : ℕ) ∧ 4 ≤ (j : ℕ) then
    (if ((i : ℕ) + (j : ℕ)) % 2 = 1 then some false else none)
  else some (decide (((i : ℕ) + (j : ℕ)) % 2 = 0))

theorem ex_symm : ∀ i j, ex i j = ex j i := by decide

theorem ex_card : (colored ex).card = 32 := by decide

theorem ex_nomono : ¬ HasMono ex := by decide

/-! ### The answer -/

/-- **IMO 1992 P3.** -/
theorem imo1992_p3 :
    IsLeast {n : ℕ | ∀ c : Fin 9 → Fin 9 → Option Bool,
      (∀ i j, c i j = c j i) → n ≤ (colored c).card → HasMono c} 33 := by
  constructor
  · intro c hsym hn
    exact upper c hsym hn
  · intro m hm
    by_contra hcon
    rw [not_le] at hcon
    exact ex_nomono (hm ex ex_symm (by rw [ex_card]; omega))

end Imo1992P3
