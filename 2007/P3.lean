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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-!
# IMO 2007, Problem 3

In a mathematical competition some competitors are friends. Friendship is always mutual.
Call a group of competitors a *clique* if each two of them are friends.  (In particular,
any group of fewer than two competitors is a clique.)  The number of members of a clique
is called its *size*.

Given that, in this competition, the largest size of a clique is *even*, prove that the
competitors can be arranged into two rooms such that the largest size of a clique
contained in one room is the same as the largest size of a clique contained in the other
room.

Competitors are modelled by a finite type `V`, friendship by a `SimpleGraph V`, and a room
by a `Finset V` (the other room being its complement).  The quantity
`cliqueSize G T` is the largest size of a clique all of whose members belong to the
room `T`.

## Outline of the proof

Let `M` be a clique of maximum size `2 * m`.  Among all subsets `S ⊆ M`, pick one of least
size with `cliqueSize G Sᶜ ≤ S.card` (the room `S` is a clique, so its largest clique size
is `S.card`).  If equality holds we are done.  Otherwise, deleting one competitor from `S`
gives a room `M₁` with `cliqueSize G M₁ = M₁.card = m₁` and `cliqueSize G M₁ᶜ = m₁ + 1`;
this is handled by the lemma `repair`.  Write `M₂ = M \ M₁`; since `M₂` is a clique in the
second room, `M₂.card ≤ m₁ + 1`, and because the maximum clique size `2 * m` is *even* this
forces `m ≤ m₁`, i.e. the number `r = 2 * m₁ + 1 - 2 * m` is at least `1`.  (For an odd
maximum clique size the corresponding number can vanish, and indeed a triangle is a
counterexample to the statement without the evenness hypothesis.)  Two cases:

* some member `u` of `M₂` is missing from some largest clique `C` of the second room: then
  moving `u` into the first room gives two rooms with largest clique size `m₁ + 1`;
* otherwise every largest clique of the second room contains `M₂`.  Consider the set
  `Bstar` of competitors outside `M` who are friends of everybody in `M₂`; its cliques
  have size at most `r`, and size `r` is attained.  Choose an inclusion-minimal set
  `U ⊆ Bstar` meeting every clique of size `r` in `Bstar`, and move `U` into the first
  room.  Both rooms then have largest clique size exactly `m₁`.
-/

namespace IMO2007P3

open Finset

variable {V : Type*} [DecidableEq V]

/-- `cliqueSize G T` is the largest size of a clique of `G` all of whose members lie in
the room `T`. -/
noncomputable def cliqueSize (G : SimpleGraph V) (T : Finset V) : ℕ :=
  (T.powerset.filter (fun s : Finset V => G.IsClique (s : Set V))).sup Finset.card

/-- Any clique contained in the room `T` has size at most `cliqueSize G T`. -/
lemma le_cliqueSize {G : SimpleGraph V} {s T : Finset V} (h : s ⊆ T)
    (hc : G.IsClique (s : Set V)) : s.card ≤ cliqueSize G T := by
  apply Finset.le_sup (f := Finset.card)
  simp [Finset.mem_filter, Finset.mem_powerset, h, hc]

/-- The bound defining `cliqueSize G T` is attained. -/
lemma exists_clique_cliqueSize (G : SimpleGraph V) (T : Finset V) :
    ∃ s ⊆ T, G.IsClique (s : Set V) ∧ s.card = cliqueSize G T := by
  have hne : (T.powerset.filter (fun s : Finset V => G.IsClique (s : Set V))).Nonempty := by
    refine ⟨∅, ?_⟩
    simp [Finset.mem_filter, Finset.mem_powerset]
  obtain ⟨s, hs, hcard⟩ := Finset.exists_mem_eq_sup _ hne Finset.card
  simp only [Finset.mem_filter, Finset.mem_powerset] at hs
  exact ⟨s, hs.1, hs.2, hcard.symm⟩

lemma cliqueSize_mono {G : SimpleGraph V} {T T' : Finset V} (h : T ⊆ T') :
    cliqueSize G T ≤ cliqueSize G T' := by
  obtain ⟨s, hs, hc, hcard⟩ := exists_clique_cliqueSize G T
  rw [← hcard]
  exact le_cliqueSize (hs.trans h) hc

/-- A room which is itself a clique has `cliqueSize` equal to its cardinality. -/
lemma cliqueSize_of_isClique {G : SimpleGraph V} {T : Finset V}
    (hT : G.IsClique (T : Set V)) : cliqueSize G T = T.card := by
  refine le_antisymm ?_ (le_cliqueSize (subset_refl T) hT)
  obtain ⟨s, hs, _, hcard⟩ := exists_clique_cliqueSize G T
  rw [← hcard]
  exact Finset.card_le_card hs

/-- Adding one competitor to a room increases the largest clique size by at most one. -/
lemma cliqueSize_insert_le {G : SimpleGraph V} (x : V) (T : Finset V) :
    cliqueSize G (insert x T) ≤ cliqueSize G T + 1 := by
  obtain ⟨s, hs, hc, hcard⟩ := exists_clique_cliqueSize G (insert x T)
  rw [← hcard]
  have h1 : s.erase x ⊆ T := by
    intro y hy
    have hy' := hs (Finset.mem_of_mem_erase hy)
    rcases Finset.mem_insert.1 hy' with h | h
    · exact absurd h (Finset.ne_of_mem_erase hy)
    · exact h
  have h2 : G.IsClique ((s.erase x : Finset V) : Set V) :=
    hc.subset (by exact_mod_cast Finset.erase_subset x s)
  have h3 := le_cliqueSize h1 h2
  have hcard2 : s.card ≤ (s.erase x).card + 1 := by
    by_cases h : x ∈ s
    · have h1s : 1 ≤ s.card := Finset.card_pos.2 ⟨x, h⟩
      rw [Finset.card_erase_of_mem h]
      omega
    · simp [Finset.erase_eq_of_notMem h]
  omega

/-- If every member of `s` is a friend of every (different) member of `t`, and both are
cliques, then their union is a clique. -/
lemma isClique_union {G : SimpleGraph V} {s t : Finset V} (hs : G.IsClique (s : Set V))
    (ht : G.IsClique (t : Set V)) (h : ∀ a ∈ s, ∀ b ∈ t, a ≠ b → G.Adj a b) :
    G.IsClique ((s ∪ t : Finset V) : Set V) := by
  intro a ha b hb hab
  simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at ha hb
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact hs ha hb hab
  · exact h a ha b hb hab
  · exact (h b hb a ha (Ne.symm hab)).symm
  · exact ht ha hb hab

section Main

variable [Fintype V]

/-- The key step: from a "bad" configuration in which the room `M₁` (a part of a maximum
clique `M`, of size `m₁`) has largest clique size `m₁` while the other room has largest
clique size `m₁ + 1`, one can still build an arrangement of the competitors into two rooms
with equal largest clique sizes. -/
lemma repair {G : SimpleGraph V} {m m₁ : ℕ} {M M₁ : Finset V}
    (hMclique : G.IsClique (M : Set V)) (hMcard : M.card = 2 * m)
    (hglobal : ∀ s : Finset V, G.IsClique (s : Set V) → s.card ≤ 2 * m)
    (hM₁sub : M₁ ⊆ M) (hm₁ : M₁.card = m₁)
    (hBsize : cliqueSize G M₁ᶜ = m₁ + 1) :
    ∃ A : Finset V, cliqueSize G A = cliqueSize G Aᶜ := by
  classical
  set M₂ : Finset V := M \ M₁ with hM₂def
  have hM₂card : M₂.card + m₁ = 2 * m := by
    rw [hM₂def, Finset.card_sdiff_of_subset hM₁sub, hMcard, hm₁]
    have : M₁.card ≤ M.card := Finset.card_le_card hM₁sub
    omega
  have hM₂sub : M₂ ⊆ M := Finset.sdiff_subset
  have hM₂clique : G.IsClique (M₂ : Set V) := hMclique.subset (by exact_mod_cast hM₂sub)
  have hM₂compl : M₂ ⊆ M₁ᶜ := by
    intro w hw
    simp only [hM₂def, Finset.mem_sdiff] at hw
    simpa using hw.2
  -- The complement room has largest clique size `m₁ + 1`; it contains the clique `M₂`.
  have hm₂le : M₂.card ≤ m₁ + 1 := by
    have := le_cliqueSize hM₂compl hM₂clique
    omega
  -- hence `m ≤ m₁`, and there is "room to spare": this is where evenness is used.
  have hmm₁ : m ≤ m₁ := by omega
  -- the complement room cannot have a clique larger than the global maximum
  have hm₁lt : m₁ + 1 ≤ 2 * m := by
    obtain ⟨s, _, hc, hcard⟩ := exists_clique_cliqueSize G M₁ᶜ
    have := hglobal s hc
    omega
  by_cases hcase : ∃ u ∈ M₂, ∃ C ⊆ M₁ᶜ, G.IsClique (C : Set V) ∧ C.card = m₁ + 1 ∧ u ∉ C
  · -- Easy case: some member of `M₂` misses a largest clique `C` of the other room.
    obtain ⟨u, huM₂, C, hCsub, hCclique, hCcard, huC⟩ := hcase
    refine ⟨insert u M₁, ?_⟩
    have huM₁ : u ∉ M₁ := by
      simp only [hM₂def, Finset.mem_sdiff] at huM₂
      exact huM₂.2
    have hAsub : insert u M₁ ⊆ M := by
      intro w hw
      rcases Finset.mem_insert.1 hw with h | h
      · exact h ▸ hM₂sub huM₂
      · exact hM₁sub h
    have hAclique : G.IsClique ((insert u M₁ : Finset V) : Set V) :=
      hMclique.subset (by exact_mod_cast hAsub)
    have hA : cliqueSize G (insert u M₁) = m₁ + 1 := by
      rw [cliqueSize_of_isClique hAclique, Finset.card_insert_of_notMem huM₁, hm₁]
    have hCsub' : C ⊆ (insert u M₁)ᶜ := by
      intro w hw
      simp only [Finset.mem_compl, Finset.mem_insert, not_or]
      refine ⟨?_, ?_⟩
      · rintro rfl; exact huC hw
      · have := hCsub hw
        simpa using this
    have h1 : m₁ + 1 ≤ cliqueSize G (insert u M₁)ᶜ := by
      have := le_cliqueSize hCsub' hCclique
      omega
    have h2 : cliqueSize G (insert u M₁)ᶜ ≤ m₁ + 1 := by
      have hsub : (insert u M₁)ᶜ ⊆ M₁ᶜ := by
        intro w hw
        simp only [Finset.mem_compl, Finset.mem_insert, not_or] at hw ⊢
        exact hw.2
      have := cliqueSize_mono (G := G) hsub
      omega
    omega
  · -- Main case: every largest clique of the other room contains all of `M₂`.
    push_neg at hcase
    have hall : ∀ C ⊆ M₁ᶜ, G.IsClique (C : Set V) → C.card = m₁ + 1 → M₂ ⊆ C := by
      intro C hCsub hCclique hCcard u huM₂
      by_contra huC
      exact huC (hcase u huM₂ C hCsub hCclique hCcard)
    -- `Bstar` : the competitors outside `M` who are friends with everybody in `M₂`.
    set Bstar : Finset V := Finset.univ.filter
      (fun w : V => w ∉ M ∧ ∀ v ∈ M₂, G.Adj w v) with hBstardef
    have hBstar_mem : ∀ w, w ∈ Bstar ↔ (w ∉ M ∧ ∀ v ∈ M₂, G.Adj w v) := by
      intro w; simp [hBstardef]
    have hBstar_compl : Bstar ⊆ M₁ᶜ := by
      intro w hw
      have hw' := (hBstar_mem w).1 hw
      simp only [Finset.mem_compl]
      exact fun h => hw'.1 (hM₁sub h)
    -- the surplus `r`
    obtain ⟨r, hr⟩ : ∃ r : ℕ, 2 * m + r = 2 * m₁ + 1 := ⟨2 * m₁ + 1 - 2 * m, by omega⟩
    have hrpos : 1 ≤ r := by omega
    -- every clique inside `Bstar` has size at most `r`
    have hBstar_bound : ∀ K ⊆ Bstar, G.IsClique (K : Set V) → K.card ≤ r := by
      intro K hK hKclique
      have hdisj : Disjoint K M₂ := by
        rw [Finset.disjoint_left]
        intro a haK haM₂
        exact ((hBstar_mem a).1 (hK haK)).1 (hM₂sub haM₂)
      have hunion : G.IsClique ((K ∪ M₂ : Finset V) : Set V) := by
        refine isClique_union hKclique hM₂clique ?_
        intro a ha b hb _
        exact ((hBstar_mem a).1 (hK ha)).2 b hb
      have hsub : K ∪ M₂ ⊆ M₁ᶜ := Finset.union_subset (hK.trans hBstar_compl) hM₂compl
      have := le_cliqueSize hsub hunion
      rw [Finset.card_union_of_disjoint hdisj, hBsize] at this
      omega
    -- and this bound is attained
    obtain ⟨R₀, hR₀sub, hR₀clique, hR₀card⟩ :
        ∃ R₀ ⊆ Bstar, G.IsClique (R₀ : Set V) ∧ R₀.card = r := by
      obtain ⟨C, hCsub, hCclique, hCcard⟩ := exists_clique_cliqueSize G M₁ᶜ
      rw [hBsize] at hCcard
      have hM₂C : M₂ ⊆ C := hall C hCsub hCclique hCcard
      refine ⟨C \ M₂, ?_, hCclique.subset (by exact_mod_cast (Finset.sdiff_subset : C \ M₂ ⊆ C)),
        ?_⟩
      · intro w hw
        simp only [Finset.mem_sdiff] at hw
        rw [hBstar_mem]
        constructor
        · intro hwM
          have hwM₁ : w ∉ M₁ := by have := hCsub hw.1; simpa using this
          exact hw.2 (by simp [hM₂def, Finset.mem_sdiff, hwM, hwM₁])
        · intro v hv
          exact hCclique (by exact_mod_cast hw.1) (by exact_mod_cast hM₂C hv)
            (by rintro rfl; exact hw.2 hv)
      · rw [Finset.card_sdiff_of_subset hM₂C, hCcard]
        omega
    -- choose an inclusion-minimal set `U ⊆ Bstar` meeting every `r`-clique of `Bstar`
    set family : Finset (Finset V) := Bstar.powerset.filter
      (fun U : Finset V => ∀ R ∈ Bstar.powerset, G.IsClique (R : Set V) → R.card = r →
        (R ∩ U).Nonempty) with hfamdef
    have hfam_mem : ∀ U : Finset V, U ∈ family ↔ (U ⊆ Bstar ∧
        ∀ R ⊆ Bstar, G.IsClique (R : Set V) → R.card = r → (R ∩ U).Nonempty) := by
      intro U
      simp [hfamdef, Finset.mem_filter, Finset.mem_powerset]
    have hfam_ne : family.Nonempty := by
      refine ⟨Bstar, (hfam_mem Bstar).2 ⟨subset_refl _, ?_⟩⟩
      intro R hR _ hRcard
      have : R.Nonempty := Finset.card_pos.1 (by omega)
      obtain ⟨a, ha⟩ := this
      exact ⟨a, Finset.mem_inter.2 ⟨ha, hR ha⟩⟩
    obtain ⟨U, hUfam, hUmin⟩ := family.exists_min_image Finset.card hfam_ne
    rw [hfam_mem] at hUfam
    obtain ⟨hUsub, hUhit⟩ := hUfam
    -- `U` is nonempty, and removing a point of `U` misses some `r`-clique
    obtain ⟨u, huU⟩ : U.Nonempty := by
      obtain ⟨a, ha⟩ := hUhit R₀ hR₀sub hR₀clique hR₀card
      exact ⟨a, (Finset.mem_inter.1 ha).2⟩
    obtain ⟨R, hRsub, hRclique, hRcard, hRU⟩ :
        ∃ R ⊆ Bstar, G.IsClique (R : Set V) ∧ R.card = r ∧ R ∩ U ⊆ {u} := by
      by_contra hcon
      push_neg at hcon
      have : U.erase u ∈ family := by
        rw [hfam_mem]
        refine ⟨(Finset.erase_subset u U).trans hUsub, ?_⟩
        intro R hR hRclique hRcard
        have hnot := hcon R hR hRclique hRcard
        rw [Finset.not_subset] at hnot
        obtain ⟨a, ha, ha'⟩ := hnot
        rw [Finset.mem_inter] at ha
        have hau : a ≠ u := by simpa using ha'
        exact ⟨a, Finset.mem_inter.2 ⟨ha.1, Finset.mem_erase.2 ⟨hau, ha.2⟩⟩⟩
      have hlt : (U.erase u).card < U.card := Finset.card_erase_lt_of_mem huU
      have := hUmin _ this
      omega
    -- the final arrangement
    refine ⟨M₁ ∪ U, ?_⟩
    have hUdisjM : ∀ a ∈ U, a ∉ M := fun a ha => ((hBstar_mem a).1 (hUsub ha)).1
    -- first room
    have hroom1 : cliqueSize G (M₁ ∪ U) = m₁ := by
      refine le_antisymm ?_ ?_
      · obtain ⟨K, hKsub, hKclique, hKcard⟩ := exists_clique_cliqueSize G (M₁ ∪ U)
        have hdisj : Disjoint K M₂ := by
          rw [Finset.disjoint_left]
          intro a haK haM₂
          rcases Finset.mem_union.1 (hKsub haK) with h | h
          · have : a ∈ M₁ := h
            simp only [hM₂def, Finset.mem_sdiff] at haM₂
            exact haM₂.2 this
          · exact hUdisjM a h (hM₂sub haM₂)
        have hunion : G.IsClique ((K ∪ M₂ : Finset V) : Set V) := by
          refine isClique_union hKclique hM₂clique ?_
          intro a ha b hb hab
          rcases Finset.mem_union.1 (hKsub ha) with h | h
          · exact hMclique (by exact_mod_cast hM₁sub h) (by exact_mod_cast hM₂sub hb) hab
          · exact ((hBstar_mem a).1 (hUsub h)).2 b hb
        have hb := hglobal _ hunion
        rw [Finset.card_union_of_disjoint hdisj] at hb
        omega
      · have : M₁ ⊆ M₁ ∪ U := Finset.subset_union_left
        have hcl : G.IsClique ((M₁ : Finset V) : Set V) :=
          hMclique.subset (by exact_mod_cast hM₁sub)
        have := le_cliqueSize this hcl
        omega
    -- second room
    have hroom2 : cliqueSize G (M₁ ∪ U)ᶜ = m₁ := by
      have hcomplsub : (M₁ ∪ U)ᶜ ⊆ M₁ᶜ := by
        intro w hw
        simp only [Finset.mem_compl, Finset.mem_union, not_or] at hw ⊢
        exact hw.1
      refine le_antisymm ?_ ?_
      · obtain ⟨K, hKsub, hKclique, hKcard⟩ := exists_clique_cliqueSize G (M₁ ∪ U)ᶜ
        by_contra hcon
        push_neg at hcon
        have hKle : K.card ≤ m₁ + 1 := by
          have := le_cliqueSize (hKsub.trans hcomplsub) hKclique
          omega
        have hKeq : K.card = m₁ + 1 := by omega
        have hM₂K : M₂ ⊆ K := hall K (hKsub.trans hcomplsub) hKclique hKeq
        have hKU : ∀ a ∈ K, a ∉ U := by
          intro a ha haU
          have := hKsub ha
          simp only [Finset.mem_compl, Finset.mem_union, not_or] at this
          exact this.2 haU
        have hsub : K \ M₂ ⊆ Bstar := by
          intro w hw
          simp only [Finset.mem_sdiff] at hw
          rw [hBstar_mem]
          constructor
          · intro hwM
            have hwM₁ : w ∉ M₁ := by
              have := hcomplsub (hKsub hw.1); simpa using this
            exact hw.2 (by simp [hM₂def, Finset.mem_sdiff, hwM, hwM₁])
          · intro v hv
            exact hKclique (by exact_mod_cast hw.1) (by exact_mod_cast hM₂K hv)
              (by rintro rfl; exact hw.2 hv)
        have hcard : (K \ M₂).card = r := by
          rw [Finset.card_sdiff_of_subset hM₂K, hKeq]; omega
        obtain ⟨a, ha⟩ := hUhit _ hsub
          (hKclique.subset (by exact_mod_cast (Finset.sdiff_subset : K \ M₂ ⊆ K))) hcard
        rw [Finset.mem_inter, Finset.mem_sdiff] at ha
        exact hKU a ha.1.1 ha.2
      · -- the clique `M₂ ∪ (R.erase u)` lives in the second room and has size `m₁`
        have hRe_sub : R.erase u ⊆ Bstar := (Finset.erase_subset u R).trans hRsub
        have hRe_clique : G.IsClique (((R.erase u) : Finset V) : Set V) :=
          hRclique.subset (by exact_mod_cast Finset.erase_subset u R)
        have hdisj : Disjoint M₂ (R.erase u) := by
          rw [Finset.disjoint_left]
          intro a haM₂ haR
          exact ((hBstar_mem a).1 (hRe_sub haR)).1 (hM₂sub haM₂)
        have hunion : G.IsClique ((M₂ ∪ R.erase u : Finset V) : Set V) := by
          refine isClique_union hM₂clique hRe_clique ?_
          intro a ha b hb hab
          exact (((hBstar_mem b).1 (hRe_sub hb)).2 a ha).symm
        have hsub : M₂ ∪ R.erase u ⊆ (M₁ ∪ U)ᶜ := by
          intro w hw
          simp only [Finset.mem_compl, Finset.mem_union, not_or]
          rcases Finset.mem_union.1 hw with h | h
          · refine ⟨?_, ?_⟩
            · simp only [hM₂def, Finset.mem_sdiff] at h; exact h.2
            · intro hwU
              exact ((hBstar_mem w).1 (hUsub hwU)).1 (hM₂sub h)
          · refine ⟨?_, ?_⟩
            · intro hwM₁
              exact ((hBstar_mem w).1 (hRe_sub h)).1 (hM₁sub hwM₁)
            · intro hwU
              have : w ∈ R ∩ U := Finset.mem_inter.2 ⟨Finset.mem_of_mem_erase h, hwU⟩
              have := hRU this
              simp only [Finset.mem_singleton] at this
              exact (Finset.ne_of_mem_erase h) this
        have hcard : (M₂ ∪ R.erase u).card = m₁ := by
          rw [Finset.card_union_of_disjoint hdisj, Finset.card_erase_of_mem, hRcard]
          · omega
          · -- `u ∈ R`
            obtain ⟨a, ha⟩ := hUhit R hRsub hRclique hRcard
            rw [Finset.mem_inter] at ha
            have hau : a = u := by simpa using hRU (Finset.mem_inter.2 ⟨ha.1, ha.2⟩)
            exact hau ▸ ha.1
        have := le_cliqueSize hsub hunion
        omega
    rw [hroom1, hroom2]

/-- **IMO 2007, Problem 3.**  If the largest size of a clique among all the competitors is
even, then the competitors can be arranged into two rooms (a room `A` and its complement)
so that the largest size of a clique contained in one room equals the largest size of a
clique contained in the other. -/
theorem imo2007_p3 (G : SimpleGraph V) (hEven : Even (cliqueSize G Finset.univ)) :
    ∃ A : Finset V, cliqueSize G A = cliqueSize G Aᶜ := by
  classical
  obtain ⟨m, hm⟩ := hEven
  have hm' : cliqueSize G Finset.univ = 2 * m := by omega
  have hglobal : ∀ s : Finset V, G.IsClique (s : Set V) → s.card ≤ 2 * m := by
    intro s hs
    have := le_cliqueSize (Finset.subset_univ s) hs
    omega
  obtain ⟨M, -, hMclique, hMcard⟩ := exists_clique_cliqueSize G Finset.univ
  rw [hm'] at hMcard
  -- Choose a subset `S ⊆ M` of least size with `cliqueSize G Sᶜ ≤ S.card`.
  set family : Finset (Finset V) :=
    M.powerset.filter (fun S : Finset V => cliqueSize G Sᶜ ≤ S.card) with hfamdef
  have hfam_mem : ∀ S : Finset V, S ∈ family ↔ (S ⊆ M ∧ cliqueSize G Sᶜ ≤ S.card) := by
    intro S; simp [hfamdef, Finset.mem_filter, Finset.mem_powerset]
  have hfam_ne : family.Nonempty := by
    refine ⟨M, (hfam_mem M).2 ⟨subset_refl _, ?_⟩⟩
    obtain ⟨s, _, hc, hcard⟩ := exists_clique_cliqueSize G Mᶜ
    have := hglobal s hc
    omega
  obtain ⟨S, hSfam, hSmin⟩ := family.exists_min_image Finset.card hfam_ne
  rw [hfam_mem] at hSfam
  obtain ⟨hSsub, hSle⟩ := hSfam
  by_cases heq : cliqueSize G Sᶜ = S.card
  · -- the two rooms `S` and `Sᶜ` already work
    refine ⟨S, ?_⟩
    have hScl : G.IsClique ((S : Finset V) : Set V) :=
      hMclique.subset (by exact_mod_cast hSsub)
    rw [cliqueSize_of_isClique hScl, heq]
  · -- otherwise, removing one competitor from `S` produces the "bad" configuration
    have hlt : cliqueSize G Sᶜ < S.card := lt_of_le_of_ne hSle heq
    have hSne : S.Nonempty := Finset.card_pos.1 (by omega)
    obtain ⟨x, hx⟩ := hSne
    set M₁ : Finset V := S.erase x with hM₁def
    have hM₁sub : M₁ ⊆ M := (Finset.erase_subset x S).trans hSsub
    have hM₁card : M₁.card + 1 = S.card := by
      rw [hM₁def, Finset.card_erase_of_mem hx]
      have : 1 ≤ S.card := Finset.card_pos.2 ⟨x, hx⟩
      omega
    have hnotfam : M₁ ∉ family := by
      intro h
      have := hSmin _ h
      omega
    have hgt : M₁.card < cliqueSize G M₁ᶜ := by
      by_contra hcon
      exact hnotfam ((hfam_mem M₁).2 ⟨hM₁sub, by omega⟩)
    have hcompl : M₁ᶜ = insert x Sᶜ := by
      rw [hM₁def]
      ext w
      simp only [Finset.mem_compl, Finset.mem_erase, Finset.mem_insert, not_and]
      by_cases hwx : w = x <;> simp [hwx]
    have hle : cliqueSize G M₁ᶜ ≤ M₁.card + 1 := by
      rw [hcompl]
      have := cliqueSize_insert_le (G := G) x Sᶜ
      omega
    exact repair hMclique hMcard hglobal hM₁sub rfl (by omega)

end Main

/-! ### A sanity check on the definition of `cliqueSize` -/

/-- In a competition of three mutual friends, the largest clique has size `3`. -/
example : cliqueSize (⊤ : SimpleGraph (Fin 3)) Finset.univ = 3 := by
  refine le_antisymm ?_ ?_
  · obtain ⟨s, _, _, hcard⟩ := exists_clique_cliqueSize (⊤ : SimpleGraph (Fin 3)) Finset.univ
    have : s.card ≤ (Finset.univ : Finset (Fin 3)).card := Finset.card_le_card (Finset.subset_univ s)
    simp only [Finset.card_univ, Fintype.card_fin] at this
    omega
  · have hcl : (⊤ : SimpleGraph (Fin 3)).IsClique ((Finset.univ : Finset (Fin 3)) : Set (Fin 3)) := by
      intro a _ b _ hab
      exact hab
    have := le_cliqueSize (subset_refl (Finset.univ : Finset (Fin 3))) hcl
    simpa using this

end IMO2007P3
