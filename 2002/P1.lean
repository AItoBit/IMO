import Mathlib

/-!
# IMO 2002, Problem 1

`S` is the set of `(h, k)` with `h, k ≥ 0` and `h + k < n`, each cell coloured red or blue so
that the red cells are downward closed: if `(h,k)` is red and `h' ≤ h`, `k' ≤ k`, then `(h',k')`
is red. A *type 1* subset has `n` blue elements with distinct first members; a *type 2* subset has
`n` blue elements with distinct second members. Show the two counts agree.

## Proof

Column `h` of the board has `n - h` cells, so a type 1 subset must contain exactly one blue cell
from each of the `n` columns; hence there are `∏_{h<n} a_h` of them, where `a_h` is the number of
blue cells in column `h`. Symmetrically there are `∏_{k<n} b_k` type 2 subsets.

So it suffices to prove `∏ a_h = ∏ b_k` for every downward-closed red set `R`, which we do by
induction on `|R|`. With `R = ∅` the two products are both `∏_{h<n} (n - h)`.

Otherwise pick `(p,q) ∈ R` maximising `p + q`. Then `R' = R \ {(p,q)}` is still downward closed,
and by maximality plus downward closure the red cells of column `p` are exactly `k ≤ q`, while
those of row `q` are exactly `h ≤ p`. Writing `v = n - p - q ≥ 1`:

* column `p` has `v - 1` blue cells in `R` and `v` in `R'`; every other column is unchanged;
* row `q` has `v - 1` blue cells in `R` and `v` in `R'`; every other row is unchanged.

So if `P` and `Q` are the products over the columns `≠ p` and the rows `≠ q`, the inductive
hypothesis reads `v * P = v * Q`, and cancelling `v ≥ 1` gives `P = Q`. Then the products for `R`
are `(v-1) * P` and `(v-1) * Q`, which agree.

This is the AoPS "Actual Proof" made precise: it asserts that colouring `(p,q)` red changes the
column count and the row count to the same value `n - (p+q) - 1`, which is exactly the step
above — but the maximality of `(p,q)`, needed to know the column and row are filled to `q` and
`p` respectively, is left implicit there.
-/

namespace Imo2002P1

open Finset

/-- The triangular board `{(h,k) : h + k < n}`. -/
def board (n : ℕ) : Finset (ℕ × ℕ) :=
  (range n ×ˢ range n).filter fun p => p.1 + p.2 < n

theorem mem_board {n : ℕ} {p : ℕ × ℕ} : p ∈ board n ↔ p.1 + p.2 < n := by
  simp only [board, mem_filter, mem_product, mem_range]
  exact ⟨fun h => h.2, fun h => ⟨⟨by omega, by omega⟩, h⟩⟩

/-- The blue cells of column `h`, recorded by their second coordinate. -/
def colB (n : ℕ) (R : Finset (ℕ × ℕ)) (h : ℕ) : Finset ℕ :=
  (range (n - h)).filter fun k => (h, k) ∉ R

/-- The blue cells of row `k`, recorded by their first coordinate. -/
def rowB (n : ℕ) (R : Finset (ℕ × ℕ)) (k : ℕ) : Finset ℕ :=
  (range (n - k)).filter fun h => (h, k) ∉ R

theorem mem_colB {n : ℕ} {R : Finset (ℕ × ℕ)} {h k : ℕ} :
    k ∈ colB n R h ↔ k < n - h ∧ (h, k) ∉ R := by
  simp [colB]

theorem mem_rowB {n : ℕ} {R : Finset (ℕ × ℕ)} {h k : ℕ} :
    h ∈ rowB n R k ↔ h < n - k ∧ (h, k) ∉ R := by
  simp [rowB]

/-- Type 1 subsets: `n` blue cells with distinct first coordinates. -/
def Type1 (n : ℕ) (R : Finset (ℕ × ℕ)) : Finset (Finset (ℕ × ℕ)) :=
  (board n \ R).powerset.filter fun T => T.card = n ∧ (T.image Prod.fst).card = n

/-- Type 2 subsets: `n` blue cells with distinct second coordinates. -/
def Type2 (n : ℕ) (R : Finset (ℕ × ℕ)) : Finset (Finset (ℕ × ℕ)) :=
  (board n \ R).powerset.filter fun T => T.card = n ∧ (T.image Prod.snd).card = n

/-! ### Counting the two kinds of subset -/

theorem card_Type1 (n : ℕ) (R : Finset (ℕ × ℕ)) :
    (Type1 n R).card = ∏ h ∈ range n, (colB n R h).card := by
  have hbij : (Fintype.piFinset fun i : Fin n => colB n R (i : ℕ)).card = (Type1 n R).card := by
    refine Finset.card_bij (fun f _ => image (fun i : Fin n => ((i : ℕ), f i)) univ) ?_ ?_ ?_
    · -- the image is a type 1 subset
      intro f hf
      simp only [Fintype.mem_piFinset] at hf
      have hinj : Function.Injective fun i : Fin n => ((i : ℕ), f i) := by
        intro i j hij
        exact Fin.val_injective (congrArg Prod.fst hij)
      simp only [Type1, mem_filter, mem_powerset]
      refine ⟨?_, ?_, ?_⟩
      · intro x hx
        simp only [mem_image, mem_univ, true_and] at hx
        obtain ⟨i, rfl⟩ := hx
        have h1 := mem_colB.1 (hf i)
        have h2 := i.isLt
        simp only [mem_sdiff, mem_board]
        exact ⟨by omega, h1.2⟩
      · rw [card_image_of_injective _ hinj, card_univ, Fintype.card_fin]
      · rw [image_image]
        have : ((fun i : Fin n => ((i : ℕ), f i)) |> (Prod.fst ∘ ·)) = fun i : Fin n => (i : ℕ) :=
          rfl
        rw [show (Prod.fst ∘ fun i : Fin n => ((i : ℕ), f i)) = fun i : Fin n => (i : ℕ) from rfl,
          card_image_of_injective _ Fin.val_injective, card_univ, Fintype.card_fin]
    · -- injective
      intro f _ g _ hfg
      funext i
      have hmem : ((i : ℕ), f i) ∈ image (fun j : Fin n => ((j : ℕ), g j)) univ := by
        rw [← hfg]
        exact mem_image_of_mem _ (mem_univ i)
      simp only [mem_image, mem_univ, true_and, Prod.mk.injEq] at hmem
      obtain ⟨j, hj1, hj2⟩ := hmem
      have : j = i := Fin.val_injective hj1
      subst this
      exact hj2.symm
    · -- surjective
      intro T hT
      simp only [Type1, mem_filter, mem_powerset] at hT
      obtain ⟨hsub, hcard, himg⟩ := hT
      have hfst : T.image Prod.fst = range n := by
        refine Finset.eq_of_subset_of_card_le ?_ ?_
        · intro x hx
          simp only [mem_image] at hx
          obtain ⟨y, hy, rfl⟩ := hx
          have := hsub hy
          simp only [mem_sdiff, mem_board] at this
          rw [mem_range]
          omega
        · rw [himg, card_range]
      have hex : ∀ i : Fin n, ∃ k, ((i : ℕ), k) ∈ T := by
        intro i
        have h1 : (i : ℕ) ∈ T.image Prod.fst := by
          rw [hfst]; exact mem_range.2 i.isLt
        simp only [mem_image] at h1
        obtain ⟨y, hy, hy2⟩ := h1
        exact ⟨y.2, by rw [← hy2]; exact hy⟩
      choose f hf using hex
      have hinj : Function.Injective fun i : Fin n => ((i : ℕ), f i) := by
        intro i j hij
        exact Fin.val_injective (congrArg Prod.fst hij)
      refine ⟨f, ?_, ?_⟩
      · simp only [Fintype.mem_piFinset]
        intro i
        have h1 := hsub (hf i)
        simp only [mem_sdiff, mem_board] at h1
        exact mem_colB.2 ⟨by omega, h1.2⟩
      · refine Finset.eq_of_subset_of_card_le ?_ ?_
        · intro x hx
          simp only [mem_image, mem_univ, true_and] at hx
          obtain ⟨i, rfl⟩ := hx
          exact hf i
        · rw [hcard, card_image_of_injective _ hinj, card_univ, Fintype.card_fin]
  rw [← hbij, Fintype.card_piFinset]
  exact Fin.prod_univ_eq_prod_range (fun h => (colB n R h).card) n

theorem card_Type2 (n : ℕ) (R : Finset (ℕ × ℕ)) :
    (Type2 n R).card = ∏ k ∈ range n, (rowB n R k).card := by
  have hbij : (Fintype.piFinset fun i : Fin n => rowB n R (i : ℕ)).card = (Type2 n R).card := by
    refine Finset.card_bij (fun f _ => image (fun i : Fin n => (f i, (i : ℕ))) univ) ?_ ?_ ?_
    · intro f hf
      simp only [Fintype.mem_piFinset] at hf
      have hinj : Function.Injective fun i : Fin n => (f i, (i : ℕ)) := by
        intro i j hij
        exact Fin.val_injective (congrArg Prod.snd hij)
      simp only [Type2, mem_filter, mem_powerset]
      refine ⟨?_, ?_, ?_⟩
      · intro x hx
        simp only [mem_image, mem_univ, true_and] at hx
        obtain ⟨i, rfl⟩ := hx
        have h1 := mem_rowB.1 (hf i)
        have h2 := i.isLt
        simp only [mem_sdiff, mem_board]
        exact ⟨by omega, h1.2⟩
      · rw [card_image_of_injective _ hinj, card_univ, Fintype.card_fin]
      · rw [image_image,
          show (Prod.snd ∘ fun i : Fin n => (f i, (i : ℕ))) = fun i : Fin n => (i : ℕ) from rfl,
          card_image_of_injective _ Fin.val_injective, card_univ, Fintype.card_fin]
    · intro f _ g _ hfg
      funext i
      have hmem : (f i, (i : ℕ)) ∈ image (fun j : Fin n => (g j, (j : ℕ))) univ := by
        rw [← hfg]
        exact mem_image_of_mem _ (mem_univ i)
      simp only [mem_image, mem_univ, true_and, Prod.mk.injEq] at hmem
      obtain ⟨j, hj1, hj2⟩ := hmem
      have : j = i := Fin.val_injective hj2
      subst this
      exact hj1.symm
    · intro T hT
      simp only [Type2, mem_filter, mem_powerset] at hT
      obtain ⟨hsub, hcard, himg⟩ := hT
      have hsnd : T.image Prod.snd = range n := by
        refine Finset.eq_of_subset_of_card_le ?_ ?_
        · intro x hx
          simp only [mem_image] at hx
          obtain ⟨y, hy, rfl⟩ := hx
          have := hsub hy
          simp only [mem_sdiff, mem_board] at this
          rw [mem_range]
          omega
        · rw [himg, card_range]
      have hex : ∀ i : Fin n, ∃ h, (h, (i : ℕ)) ∈ T := by
        intro i
        have h1 : (i : ℕ) ∈ T.image Prod.snd := by
          rw [hsnd]; exact mem_range.2 i.isLt
        simp only [mem_image] at h1
        obtain ⟨y, hy, hy2⟩ := h1
        exact ⟨y.1, by rw [← hy2]; exact hy⟩
      choose f hf using hex
      have hinj : Function.Injective fun i : Fin n => (f i, (i : ℕ)) := by
        intro i j hij
        exact Fin.val_injective (congrArg Prod.snd hij)
      refine ⟨f, ?_, ?_⟩
      · simp only [Fintype.mem_piFinset]
        intro i
        have h1 := hsub (hf i)
        simp only [mem_sdiff, mem_board] at h1
        exact mem_rowB.2 ⟨by omega, h1.2⟩
      · refine Finset.eq_of_subset_of_card_le ?_ ?_
        · intro x hx
          simp only [mem_image, mem_univ, true_and] at hx
          obtain ⟨i, rfl⟩ := hx
          exact hf i
        · rw [hcard, card_image_of_injective _ hinj, card_univ, Fintype.card_fin]
  rw [← hbij, Fintype.card_piFinset]
  exact Fin.prod_univ_eq_prod_range (fun k => (rowB n R k).card) n

/-! ### The product identity -/

theorem colB_empty_card (n h : ℕ) : (colB n ∅ h).card = n - h := by
  rw [colB, Finset.filter_true_of_mem (by simp), card_range]

theorem rowB_empty_card (n k : ℕ) : (rowB n ∅ k).card = n - k := by
  rw [rowB, Finset.filter_true_of_mem (by simp), card_range]

theorem core_empty (n : ℕ) :
    ∏ h ∈ range n, (colB n ∅ h).card = ∏ k ∈ range n, (rowB n ∅ k).card := by
  simp only [colB_empty_card, rowB_empty_card]

/-- For a downward-closed red set, the product of the column blue-counts equals the product of
the row blue-counts. -/
theorem core (n : ℕ) : ∀ N : ℕ, ∀ R : Finset (ℕ × ℕ), R.card ≤ N →
    (∀ p ∈ R, p.1 + p.2 < n) →
    (∀ p ∈ R, ∀ a b : ℕ, a ≤ p.1 → b ≤ p.2 → (a, b) ∈ R) →
    ∏ h ∈ range n, (colB n R h).card = ∏ k ∈ range n, (rowB n R k).card := by
  intro N
  induction N with
  | zero =>
      intro R hcard _ _
      have : R = ∅ := Finset.card_eq_zero.1 (by omega)
      subst this
      exact core_empty n
  | succ N ih =>
      intro R hcard hsub hdown
      rcases Finset.eq_empty_or_nonempty R with rfl | hne
      · exact core_empty n
      obtain ⟨c, hcR, hcmax⟩ := Finset.exists_max_image R (fun p => p.1 + p.2) hne
      obtain ⟨p, q⟩ := c
      have hpq : p + q < n := hsub (p, q) hcR
      have hpn : p < n := by omega
      have hqn : q < n := by omega
      -- the red cells of column `p` are exactly `k ≤ q`
      have hmemR : ∀ k, ((p, k) ∈ R ↔ k ≤ q) := by
        intro k
        refine ⟨fun h => ?_, fun h => hdown (p, q) hcR p k (le_refl p) h⟩
        have h2 : p + k ≤ p + q := hcmax (p, k) h
        omega
      -- the red cells of row `q` are exactly `h ≤ p`
      have hmemRr : ∀ h, ((h, q) ∈ R ↔ h ≤ p) := by
        intro h
        refine ⟨fun hh => ?_, fun hh => hdown (p, q) hcR h q hh (le_refl q)⟩
        have h2 : h + q ≤ p + q := hcmax (h, q) hh
        omega
      set R' := R.erase (p, q) with hR'def
      have hmemR' : ∀ k, ((p, k) ∈ R' ↔ k < q) := by
        intro k
        rw [hR'def, mem_erase, hmemR k]
        constructor
        · rintro ⟨h1, h2⟩
          rcases Nat.lt_or_ge k q with hlt | hge
          · exact hlt
          · exact absurd (congrArg (fun t => ((p, t) : ℕ × ℕ)) (le_antisymm h2 hge)) h1
        · intro hlt
          refine ⟨fun hc => ?_, by omega⟩
          have hkq : k = q := congrArg Prod.snd hc
          omega
      have hmemR'r : ∀ h, ((h, q) ∈ R' ↔ h < p) := by
        intro h
        rw [hR'def, mem_erase, hmemRr h]
        constructor
        · rintro ⟨h1, h2⟩
          rcases Nat.lt_or_ge h p with hlt | hge
          · exact hlt
          · exact absurd (congrArg (fun t => ((t, q) : ℕ × ℕ)) (le_antisymm h2 hge)) h1
        · intro hlt
          refine ⟨fun hc => ?_, by omega⟩
          have hhp : h = p := congrArg Prod.fst hc
          omega
      -- the inductive hypothesis applies to `R'`
      have hR'card : R'.card ≤ N := by
        rw [hR'def, card_erase_of_mem hcR]
        omega
      have hR'sub : ∀ x ∈ R', x.1 + x.2 < n := fun x hx => hsub x (mem_of_mem_erase hx)
      have hR'down : ∀ x ∈ R', ∀ a b : ℕ, a ≤ x.1 → b ≤ x.2 → (a, b) ∈ R' := by
        intro x hx a b ha hb
        have hxR : x ∈ R := mem_of_mem_erase hx
        have hne2 : x ≠ (p, q) := (mem_erase.1 hx).1
        refine mem_erase.2 ⟨?_, hdown x hxR a b ha hb⟩
        intro hab
        simp only [Prod.mk.injEq] at hab
        apply hne2
        have h2 : x.1 + x.2 ≤ p + q := hcmax x hxR
        exact Prod.ext (by omega) (by omega)
      have IH := ih R' hR'card hR'sub hR'down
      -- column and row counts
      have hcolRp : (colB n R p).card = n - p - q - 1 := by
        have e : colB n R p = Ico (q + 1) (n - p) := by
          ext k
          rw [mem_colB, mem_Ico, hmemR k]
          omega
        rw [e, Nat.card_Ico]
        omega
      have hcolR'p : (colB n R' p).card = n - p - q := by
        have e : colB n R' p = Ico q (n - p) := by
          ext k
          rw [mem_colB, mem_Ico, hmemR' k]
          omega
        rw [e, Nat.card_Ico]
      have hrowRq : (rowB n R q).card = n - p - q - 1 := by
        have e : rowB n R q = Ico (p + 1) (n - q) := by
          ext h
          rw [mem_rowB, mem_Ico, hmemRr h]
          omega
        rw [e, Nat.card_Ico]
        omega
      have hrowR'q : (rowB n R' q).card = n - p - q := by
        have e : rowB n R' q = Ico p (n - q) := by
          ext h
          rw [mem_rowB, mem_Ico, hmemR'r h]
          omega
        rw [e, Nat.card_Ico]
        omega
      -- nothing else changes
      have hcolEq : ∀ h ∈ (range n).erase p, (colB n R' h).card = (colB n R h).card := by
        intro h hh
        have hhp : h ≠ p := (mem_erase.1 hh).1
        have key : ∀ k, ((h, k) ∈ R' ↔ (h, k) ∈ R) := by
          intro k
          rw [hR'def, mem_erase]
          exact ⟨fun x => x.2, fun x => ⟨fun hc => hhp (congrArg Prod.fst hc), x⟩⟩
        congr 1
        ext k
        rw [mem_colB, mem_colB, key k]
      have hrowEq : ∀ k ∈ (range n).erase q, (rowB n R' k).card = (rowB n R k).card := by
        intro k hk
        have hkq : k ≠ q := (mem_erase.1 hk).1
        have key : ∀ h, ((h, k) ∈ R' ↔ (h, k) ∈ R) := by
          intro h
          rw [hR'def, mem_erase]
          exact ⟨fun x => x.2, fun x => ⟨fun hc => hkq (congrArg Prod.snd hc), x⟩⟩
        congr 1
        ext h
        rw [mem_rowB, mem_rowB, key h]
      -- cancel the common factor
      have hP : ∏ h ∈ (range n).erase p, (colB n R' h).card
          = ∏ h ∈ (range n).erase p, (colB n R h).card := Finset.prod_congr rfl hcolEq
      have hQ : ∏ k ∈ (range n).erase q, (rowB n R' k).card
          = ∏ k ∈ (range n).erase q, (rowB n R k).card := Finset.prod_congr rfl hrowEq
      have e1 : (n - p - q) * ∏ h ∈ (range n).erase p, (colB n R h).card
          = ∏ h ∈ range n, (colB n R' h).card := by
        rw [← Finset.mul_prod_erase _ _ (mem_range.2 hpn), hcolR'p, hP]
      have e2 : (n - p - q) * ∏ k ∈ (range n).erase q, (rowB n R k).card
          = ∏ k ∈ range n, (rowB n R' k).card := by
        rw [← Finset.mul_prod_erase _ _ (mem_range.2 hqn), hrowR'q, hQ]
      have key : ∏ h ∈ (range n).erase p, (colB n R h).card
          = ∏ k ∈ (range n).erase q, (rowB n R k).card := by
        refine Nat.eq_of_mul_eq_mul_left (by omega : 0 < n - p - q) ?_
        rw [e1, e2, IH]
      rw [← Finset.mul_prod_erase _ _ (mem_range.2 hpn),
        ← Finset.mul_prod_erase _ _ (mem_range.2 hqn), hcolRp, hrowRq, key]

/-- **IMO 2002 P1.** There are as many type 1 subsets as type 2 subsets. -/
theorem imo2002_p1 (n : ℕ) (R : Finset (ℕ × ℕ))
    (hsub : ∀ p ∈ R, p.1 + p.2 < n)
    (hdown : ∀ p ∈ R, ∀ a b : ℕ, a ≤ p.1 → b ≤ p.2 → (a, b) ∈ R) :
    (Type1 n R).card = (Type2 n R).card := by
  rw [card_Type1, card_Type2]
  exact core n R.card R (le_refl _) hsub hdown

end Imo2002P1
