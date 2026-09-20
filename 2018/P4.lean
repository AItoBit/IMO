import Mathlib

namespace Imo2018P4

set_option maxRecDepth 100000

abbrev Site := Fin 20 × Fin 20

/-!
# IMO 2018 Problem 4

Amy and Ben play on the 20 × 20 lattice.

The goal is to prove that the greatest number of red stones
Amy can guarantee is exactly 100.

No `sorry`, `admit`, or additional axioms are used.
-/

/-!
============================================================
1. Geometry
============================================================
-/

/-- Two sites are at distance `√5`. -/
def sq5 (s t : Site) : Prop :=
  ((s.1.val : ℤ) - (t.1.val : ℤ)) ^ 2 +
      ((s.2.val : ℤ) - (t.2.val : ℤ)) ^ 2
    =
  5

instance (s t : Site) :
    Decidable (sq5 s t) := by
  unfold sq5
  infer_instance

lemma sq5_symm
    {s t : Site}
    (h : sq5 s t) :
    sq5 t s := by

  unfold sq5 at h ⊢
  linear_combination h

/--
If `a² + b² = 5`, then `a+b` cannot be even.
-/
lemma sq5_parity
    {a b : ℤ}
    (h :
      a ^ 2 + b ^ 2 = 5) :
    ¬ (2 ∣ a + b) := by

  rintro ⟨c, hc⟩

  have ha :
      a = 2 * c - b := by
    linarith

  subst a

  have h2 :
      2 *
          (2 * c ^ 2 -
            2 * c * b +
            b ^ 2)
        =
      5 := by
    linear_combination h

  obtain ⟨K, hK⟩ :
      ∃ K : ℤ,
        2 * K = 5 :=
    ⟨_,
     h2⟩

  omega

/-!
============================================================
2. Game definition
============================================================
-/

/-- Legal moves for Amy. -/
def amyMoves
    (r b : Finset Site) :
    Finset Site :=
  Finset.univ.filter
    (fun s =>
      s ∉ r ∧
      s ∉ b ∧
      ∀ t ∈ r,
        ¬ sq5 s t)

/-- Legal moves for Ben. -/
def benMoves
    (r b : Finset Site) :
    Finset Site :=
  Finset.univ.filter
    (fun s =>
      s ∉ r ∧
      s ∉ b)

abbrev Strat :=
  Finset Site →
    Finset Site →
      Site

/--
`play A B n turn r b` is the number of red stones Amy
places during at most `n` remaining turns.
-/
def play
    (A B : Strat) :
    ℕ →
    Bool →
    Finset Site →
    Finset Site →
    ℕ
  | 0, _, _, _ =>
      0

  | n + 1, true, r, b =>
      if (amyMoves r b).Nonempty then
        1 +
          play A B n false
            (insert (A r b) r)
            b
      else
        0

  | n + 1, false, r, b =>
      if (benMoves r b).Nonempty then
        play A B n true
          r
          (insert (B r b) b)
      else
        0

lemma play_zero
    (A B : Strat)
    (t : Bool)
    (r b : Finset Site) :
    play A B 0 t r b = 0 := by
  rfl

lemma play_amy
    (A B : Strat)
    (n : ℕ)
    (r b : Finset Site) :
    play A B (n + 1) true r b
      =
    if (amyMoves r b).Nonempty then
      1 +
        play A B n false
          (insert (A r b) r)
          b
    else
      0 := by
  rfl

lemma play_ben
    (A B : Strat)
    (n : ℕ)
    (r b : Finset Site) :
    play A B (n + 1) false r b
      =
    if (benMoves r b).Nonempty then
      play A B n true
        r
        (insert (B r b) b)
    else
      0 := by
  rfl

/--
A strategy is valid when it always chooses a legal move
whenever at least one legal move exists.
-/
def ValidA
    (A : Strat) : Prop :=
  ∀ r b,
    (amyMoves r b).Nonempty →
    A r b ∈ amyMoves r b

def ValidB
    (B : Strat) : Prop :=
  ∀ r b,
    (benMoves r b).Nonempty →
    B r b ∈ benMoves r b

/-!
============================================================
3. Choice from finite sets
============================================================
-/

noncomputable def pick
    (S : Finset Site) :
    Site :=
  if h : S.Nonempty then
    h.choose
  else
    (0, 0)

lemma pick_mem
    {S : Finset Site}
    (h : S.Nonempty) :
    pick S ∈ S := by

  unfold pick

  split
  next hS =>
    exact hS.choose_spec
  next hS =>
    exact False.elim (hS h)

lemma pick_singleton
    (x : Site) :
    pick {x} = x := by

  apply Finset.mem_singleton.mp

  exact
    pick_mem
      ⟨x,
       Finset.mem_singleton_self x⟩

/-!
============================================================
4. Ben has a free site before the board is full
============================================================
-/

lemma exists_free
    {r b : Finset Site}
    (h :
      r.card + b.card < 400) :
    (benMoves r b).Nonempty := by

  by_contra hcon

  rw [Finset.not_nonempty_iff_eq_empty] at hcon

  have hsub :
      (Finset.univ : Finset Site) ⊆
        r ∪ b := by

    intro x _

    by_contra hx

    rw [Finset.mem_union] at hx

    have hx2 :
        x ∈ benMoves r b := by

      simp only [
        benMoves,
        Finset.mem_filter,
        Finset.mem_univ,
        true_and
      ]

      exact
        ⟨fun hr =>
            hx (Or.inl hr),
         fun hb =>
            hx (Or.inr hb)⟩

    rw [hcon] at hx2

    simp at hx2

  have h1 :=
    Finset.card_le_card hsub

  have h2 :=
    Finset.card_union_le r b

  have h3 :
      (Finset.univ : Finset Site).card =
        400 := by
    simp

  omega

/-!
============================================================
5. Amy's lower-bound strategy
============================================================
-/

def evenSites :
    Finset Site :=
  Finset.univ.filter
    (fun s =>
      (s.1.val + s.2.val) % 2 = 0)

lemma evenSites_card :
    evenSites.card = 200 := by
  native_decide

/--
Two sites with even coordinate sums cannot be √5 apart.
-/
lemma even_no_conflict
    {s t : Site}
    (hs :
      s ∈ evenSites)
    (ht :
      t ∈ evenSites) :
    ¬ sq5 s t := by

  intro h

  refine
    sq5_parity h ?_

  simp only [
    evenSites,
    Finset.mem_filter,
    Finset.mem_univ,
    true_and
  ] at hs ht

  obtain ⟨u, hu⟩ :
      ∃ u : ℕ,
        s.1.val + s.2.val =
          2 * u := by

    refine
      ⟨(s.1.val + s.2.val) / 2,
       ?_⟩

    omega

  obtain ⟨v, hv⟩ :
      ∃ v : ℕ,
        t.1.val + t.2.val =
          2 * v := by

    refine
      ⟨(t.1.val + t.2.val) / 2,
       ?_⟩

    omega

  refine
    ⟨(u : ℤ) - v,
     ?_⟩

  have h1 :
      (s.1.val : ℤ) +
          (s.2.val : ℤ)
        =
      2 * u := by
    exact_mod_cast hu

  have h2 :
      (t.1.val : ℤ) +
          (t.2.val : ℤ)
        =
      2 * v := by
    exact_mod_cast hv

  linarith

lemma exists_free_even
    {r b : Finset Site}
    (h :
      r.card + b.card < 200) :
    (evenSites \ (r ∪ b)).Nonempty := by

  rw [Finset.nonempty_iff_ne_empty]

  intro hcon

  have hsub :
      evenSites ⊆ r ∪ b := by

    intro x hx

    by_contra hx2

    have hx3 :
        x ∈ evenSites \ (r ∪ b) :=
      Finset.mem_sdiff.mpr
        ⟨hx, hx2⟩

    rw [hcon] at hx3

    simp at hx3

  have h1 :=
    Finset.card_le_card hsub

  have h2 :=
    Finset.card_union_le r b

  rw [evenSites_card] at h1

  omega

noncomputable def amyStrat
    (r b : Finset Site) :
    Site :=
  if (amyMoves r b ∩ evenSites).Nonempty then
    pick (amyMoves r b ∩ evenSites)
  else
    pick (amyMoves r b)

lemma amyStrat_valid :
    ValidA amyStrat := by

  intro r b h

  unfold amyStrat

  split
  next hc =>
    exact
      (Finset.mem_inter.mp
        (pick_mem hc)).1

  next _ =>
    exact pick_mem h

/-!
============================================================
6. Amy can guarantee 100 red stones
============================================================
-/

lemma lower_aux
    (B : Strat)
    (hB : ValidB B) :
    ∀ (j n : ℕ)
      (r b : Finset Site),
      2 * j ≤ n →
      r ⊆ evenSites →
      Disjoint r b →
      b.card ≤ r.card →
      r.card + j ≤ 100 →
      j ≤ play amyStrat B n true r b := by

  intro j

  induction j with

  | zero =>
      intro n r b _ _ _ _ _
      exact Nat.zero_le _

  | succ j ih =>
      intro n r b hn hre hdis hbc hrc

      obtain ⟨n1, rfl⟩ :
          ∃ n1,
            n = n1 + 1 :=
        ⟨n - 1,
         by omega⟩

      obtain ⟨n2, rfl⟩ :
          ∃ n2,
            n1 = n2 + 1 :=
        ⟨n1 - 1,
         by omega⟩

      obtain ⟨s0, hs0⟩ :=
        exists_free_even
          (r := r)
          (b := b)
          (by omega)

      rw [
        Finset.mem_sdiff,
        Finset.mem_union
      ] at hs0

      have hs0amy :
          s0 ∈ amyMoves r b := by

        simp only [
          amyMoves,
          Finset.mem_filter,
          Finset.mem_univ,
          true_and
        ]

        exact
          ⟨fun hc =>
              hs0.2 (Or.inl hc),
           fun hc =>
              hs0.2 (Or.inr hc),
           fun t ht =>
              even_no_conflict
                hs0.1
                (hre ht)⟩

      have hne1 :
          (amyMoves r b ∩ evenSites).Nonempty :=
        ⟨s0,
         Finset.mem_inter.mpr
           ⟨hs0amy,
            hs0.1⟩⟩

      have hne0 :
          (amyMoves r b).Nonempty :=
        ⟨s0, hs0amy⟩

      have hsdef :
          amyStrat r b ∈
            amyMoves r b ∩ evenSites := by

        unfold amyStrat

        split
        next _ =>
          exact pick_mem hne1

        next hbad =>
          exact False.elim (hbad hne1)

      obtain ⟨hsamy, hseven⟩ :=
        Finset.mem_inter.mp hsdef

      have hsamy' := hsamy

      simp only [
        amyMoves,
        Finset.mem_filter,
        Finset.mem_univ,
        true_and
      ] at hsamy'

      rw [play_amy]

      split

      next _ =>
        have hcard' :
            (insert (amyStrat r b) r).card =
              r.card + 1 :=
          Finset.card_insert_of_notMem
            hsamy'.1

        have hben :
            (benMoves
              (insert (amyStrat r b) r)
              b).Nonempty :=
          exists_free
            (by omega)

        rw [play_ben]

        split

        next hben' =>
          have ht :=
            hB
              (insert (amyStrat r b) r)
              b
              hben'

          have ht' := ht

          simp only [
            benMoves,
            Finset.mem_filter,
            Finset.mem_univ,
            true_and
          ] at ht'

          have hkey :
              j ≤
                play amyStrat B n2 true
                  (insert (amyStrat r b) r)
                  (insert
                    (B
                      (insert (amyStrat r b) r)
                      b)
                    b) := by

            refine
              ih
                n2
                _
                _
                (by omega)
                ?_
                ?_
                ?_
                ?_

            · intro x hx

              rcases
                Finset.mem_insert.mp hx
              with hx | hx

              · exact
                  hx ▸ hseven

              · exact
                  hre hx

            · rw [Finset.disjoint_left]

              intro x hx hx2

              rcases
                Finset.mem_insert.mp hx2
              with hxB | hxB

              · exact
                  ht'.1
                    (hxB ▸ hx)

              · rcases
                  Finset.mem_insert.mp hx
                with hxA | hxA

                · exact
                    hsamy'.2.1
                      (hxA ▸ hxB)

                · exact
                    (Finset.disjoint_left.mp
                      hdis
                      hxA)
                      hxB

            · rw [
                Finset.card_insert_of_notMem
                  ht'.2,
                hcard'
              ]

              omega

            · omega

          omega

        next hben' =>
          exact
            False.elim
              (hben' hben)

      next hmove =>
        exact
          False.elim
            (hmove hne0)

/-!
============================================================
7. Ben's 4×4 partner strategy
============================================================
-/

/--
Reflect one coordinate inside its block of length four.
-/
def rev4
    (v : ℕ) :
    ℕ :=
  4 * (v / 4) +
    3 -
    v % 4

lemma rev4_lt
    {v : ℕ}
    (h : v < 20) :
    rev4 v < 20 := by

  unfold rev4
  omega

lemma rev4_rev4
    {v : ℕ}
    (h : v < 20) :
    rev4 (rev4 v) = v := by

  unfold rev4
  omega

lemma rev4_ne
    {v : ℕ}
    (_h : v < 20) :
    rev4 v ≠ v := by

  unfold rev4
  omega

/--
The 180-degree rotational partner inside the current 4×4 block.
-/
def partner
    (s : Site) :
    Site :=
  (⟨rev4 s.1.val,
     rev4_lt s.1.isLt⟩,
   ⟨rev4 s.2.val,
     rev4_lt s.2.isLt⟩)

lemma partner_partner
    (s : Site) :
    partner (partner s) = s := by

  rw [Prod.ext_iff]

  refine
    ⟨Fin.ext ?_,
     Fin.ext ?_⟩

  · simpa [partner] using
      rev4_rev4 s.1.isLt

  · simpa [partner] using
      rev4_rev4 s.2.isLt

lemma partner_ne
    (s : Site) :
    partner s ≠ s := by

  intro h

  have h1 :
      rev4 s.1.val =
        s.1.val := by

    have hx :=
      congrArg
        (fun p : Site =>
          p.1.val)
        h

    simpa [partner] using hx

  exact
    rev4_ne
      s.1.isLt
      h1

lemma partner_injective :
    Function.Injective partner := by

  intro s t h

  have h2 :=
    congrArg partner h

  rwa [
    partner_partner,
    partner_partner
  ] at h2

/-!
============================================================
8. The 100 quads
============================================================
-/

def quadTable :
    List (List ℕ) :=
  [
    [0, 2, 3, 1],
    [3, 1, 0, 2],
    [2, 0, 1, 3],
    [1, 3, 2, 0]
  ]

def quadLocal
    (i j : ℕ) :
    ℕ :=
  (quadTable.getD
      (i % 4)
      []).getD
    (j % 4)
    0

lemma quadLocal_lt
    (i j : ℕ) :
    quadLocal i j < 4 := by

  have hi :
      i % 4 = 0 ∨
      i % 4 = 1 ∨
      i % 4 = 2 ∨
      i % 4 = 3 := by
    omega

  have hj :
      j % 4 = 0 ∨
      j % 4 = 1 ∨
      j % 4 = 2 ∨
      j % 4 = 3 := by
    omega

  rcases hi with hi0 | hi1 | hi2 | hi3

  · rcases hj with hj0 | hj1 | hj2 | hj3
    · simp [quadLocal, quadTable, hi0, hj0]
    · simp [quadLocal, quadTable, hi0, hj1]
    · simp [quadLocal, quadTable, hi0, hj2]
    · simp [quadLocal, quadTable, hi0, hj3]

  · rcases hj with hj0 | hj1 | hj2 | hj3
    · simp [quadLocal, quadTable, hi1, hj0]
    · simp [quadLocal, quadTable, hi1, hj1]
    · simp [quadLocal, quadTable, hi1, hj2]
    · simp [quadLocal, quadTable, hi1, hj3]

  · rcases hj with hj0 | hj1 | hj2 | hj3
    · simp [quadLocal, quadTable, hi2, hj0]
    · simp [quadLocal, quadTable, hi2, hj1]
    · simp [quadLocal, quadTable, hi2, hj2]
    · simp [quadLocal, quadTable, hi2, hj3]

  · rcases hj with hj0 | hj1 | hj2 | hj3
    · simp [quadLocal, quadTable, hi3, hj0]
    · simp [quadLocal, quadTable, hi3, hj1]
    · simp [quadLocal, quadTable, hi3, hj2]
    · simp [quadLocal, quadTable, hi3, hj3]

lemma quadLocal_mod
    (i j : ℕ) :
    quadLocal
        (i % 4)
        (j % 4)
      =
    quadLocal i j := by

  have h1 :
      i % 4 % 4 =
        i % 4 := by
    omega

  have h2 :
      j % 4 % 4 =
        j % 4 := by
    omega

  unfold quadLocal

  rw [h1, h2]

/--
Which of the 100 four-element quads contains a site.
-/
def quadIdx
    (s : Site) :
    ℕ :=
  20 * (s.1.val / 4) +
    4 * (s.2.val / 4) +
    quadLocal
      s.1.val
      s.2.val

lemma quadIdx_lt
    (s : Site) :
    quadIdx s < 100 := by

  have h1 :=
    s.1.isLt

  have h2 :=
    s.2.isLt

  have h3 :=
    quadLocal_lt
      s.1.val
      s.2.val

  unfold quadIdx

  omega

/--
Finite 4×4 core.

Two distinct cells belonging to the same quad are either
√5 apart or are partners.
-/
lemma quad_local_key :
    ∀ i j i' j' : Fin 4,
      quadLocal i.val j.val =
          quadLocal i'.val j'.val →
      ¬
        (i.val = i'.val ∧
         j.val = j'.val) →
      (((i.val : ℤ) -
            (i'.val : ℤ)) ^ 2 +
          ((j.val : ℤ) -
            (j'.val : ℤ)) ^ 2
        =
       5)
      ∨
      (i'.val = 3 - i.val ∧
       j'.val = 3 - j.val) := by

  native_decide

lemma quad_key
    {s t : Site}
    (h :
      quadIdx s =
        quadIdx t)
    (hst :
      s ≠ t) :
    sq5 s t ∨
      partner s = t := by

  have hs1 :=
    s.1.isLt

  have hs2 :=
    s.2.isLt

  have ht1 :=
    t.1.isLt

  have ht2 :=
    t.2.isLt

  have hqs :=
    quadLocal_lt
      s.1.val
      s.2.val

  have hqt :=
    quadLocal_lt
      t.1.val
      t.2.val

  unfold quadIdx at h

  have hb1 :
      s.1.val / 4 =
        t.1.val / 4 := by
    omega

  have hb2 :
      s.2.val / 4 =
        t.2.val / 4 := by
    omega

  have hql :
      quadLocal
          s.1.val
          s.2.val
        =
      quadLocal
          t.1.val
          t.2.val := by
    omega

  have hne :
      ¬
      (s.1.val % 4 =
          t.1.val % 4 ∧
       s.2.val % 4 =
          t.2.val % 4) := by

    rintro ⟨e1, e2⟩

    apply hst

    rw [Prod.ext_iff]

    exact
      ⟨Fin.ext (by omega),
       Fin.ext (by omega)⟩

  have hloc :=
    quad_local_key
      ⟨s.1.val % 4,
       by omega⟩
      ⟨s.2.val % 4,
       by omega⟩
      ⟨t.1.val % 4,
       by omega⟩
      ⟨t.2.val % 4,
       by omega⟩
      (by
        simpa [quadLocal_mod]
          using hql)
      (by
        simpa using hne)

  simp only at hloc

  rcases hloc with
    hloc | hpartner

  · left

    unfold sq5

    have c1 :
        (s.1.val : ℤ) -
            (t.1.val : ℤ)
          =
        ((s.1.val % 4 : ℕ) : ℤ) -
          ((t.1.val % 4 : ℕ) : ℤ) := by
      omega

    have c2 :
        (s.2.val : ℤ) -
            (t.2.val : ℤ)
          =
        ((s.2.val % 4 : ℕ) : ℤ) -
          ((t.2.val % 4 : ℕ) : ℤ) := by
      omega

    rw [c1, c2]

    exact hloc

  · rcases hpartner with ⟨e1, e2⟩

    right

    rw [Prod.ext_iff]

    refine
      ⟨Fin.ext ?_,
       Fin.ext ?_⟩

    · show
        rev4 s.1.val =
          t.1.val

      unfold rev4

      omega

    · show
        rev4 s.2.val =
          t.2.val

      unfold rev4

      omega

/-!
============================================================
9. At most one red site per quad
============================================================
-/

lemma card_le_hundred
    {r : Finset Site}
    (hfree :
      ∀ s ∈ r,
        ∀ t ∈ r,
          s ≠ t →
          ¬ sq5 s t)
    (hpair :
      ∀ s ∈ r,
        partner s ∉ r) :
    r.card ≤ 100 := by

  have hinj :
      Set.InjOn
        quadIdx
        (r : Set Site) := by

    intro s hs t ht h

    simp only [
      Finset.mem_coe
    ] at hs ht

    by_contra hne

    rcases
      quad_key h hne
    with h1 | h1

    · exact
        hfree
          s
          hs
          t
          ht
          hne
          h1

    · exact
        hpair
          s
          hs
          (h1 ▸ ht)

  calc
    r.card =
        (r.image quadIdx).card :=
      (Finset.card_image_of_injOn
        hinj).symm

    _ ≤
        (Finset.range 100).card := by

      apply
        Finset.card_le_card

      intro x hx

      obtain ⟨s, _, rfl⟩ :=
        Finset.mem_image.mp hx

      exact
        Finset.mem_range.mpr
          (quadIdx_lt s)

    _ = 100 :=
      Finset.card_range 100

lemma pair_free
    {r b : Finset Site}
    (hb :
      b = r.image partner)
    (hd :
      Disjoint r b) :
    ∀ s ∈ r,
      partner s ∉ r := by

  intro s hs hc

  exact
    (Finset.disjoint_left.mp
      hd
      hc)
      (hb ▸
        Finset.mem_image_of_mem
          partner
          hs)

/-!
============================================================
10. Partner facts after Amy makes a move
============================================================
-/

lemma step_facts
    {r b : Finset Site}
    (hb :
      b = r.image partner)
    {s : Site}
    (hsr :
      s ∉ r)
    (hsb :
      s ∉ b) :
    partner s ∉ r ∧
    partner s ∉ b ∧
    partner s ≠ s := by

  refine
    ⟨?_,
     ?_,
     partner_ne s⟩

  · intro hc

    apply hsb

    rw [hb]

    have h2 :
        partner (partner s) ∈
          r.image partner :=
      Finset.mem_image_of_mem
        partner
        hc

    rwa [partner_partner] at h2

  · intro hc

    rw [
      hb,
      Finset.mem_image
    ] at hc

    obtain ⟨u, hu, hpu⟩ := hc

    have hus :
        u = s :=
      partner_injective hpu

    subst u

    exact hsr hu

/-!
============================================================
11. Ben's strategy
============================================================
-/

noncomputable def benStrat
    (r b : Finset Site) :
    Site :=
  if
    ((((r \ b.image partner).image partner) ∩
        benMoves r b).Nonempty)
  then
    pick
      (((r \ b.image partner).image partner) ∩
        benMoves r b)
  else
    pick (benMoves r b)

lemma benStrat_valid :
    ValidB benStrat := by

  intro r b h

  unfold benStrat

  split
  next hc =>
    exact
      (Finset.mem_inter.mp
        (pick_mem hc)).2

  next _ =>
    exact pick_mem h

/--
If the invariant `b = r.image partner` holds and Amy
plays `s`, then Ben chooses `partner s`.
-/
lemma benStrat_eq
    {r b : Finset Site}
    (hb :
      b = r.image partner)
    {s : Site}
    (hsr :
      s ∉ r)
    (hsb :
      s ∉ b) :
    benStrat
        (insert s r)
        b
      =
    partner s := by

  obtain ⟨hpnr, hpnb, hpns⟩ :=
    step_facts
      hb
      hsr
      hsb

  have h0 :
      b.image partner = r := by

    rw [
      hb,
      Finset.image_image
    ]

    have hcomp :
        partner ∘ partner = id := by

      funext x

      exact
        partner_partner x

    rw [
      hcomp,
      Finset.image_id
    ]

  have h1 :
      insert s r \
          b.image partner
        =
      {s} := by

    rw [h0]

    ext x

    simp only [
      Finset.mem_sdiff,
      Finset.mem_insert,
      Finset.mem_singleton
    ]

    constructor

    · rintro ⟨hx | hx, hxr⟩

      · exact hx

      · exact
          False.elim
            (hxr hx)

    · intro hx

      subst x

      exact
        ⟨Or.inl rfl,
         hsr⟩

  have h2 :
      (insert s r \
          b.image partner).image partner
        =
      {partner s} := by

    rw [
      h1,
      Finset.image_singleton
    ]

  have hmem :
      partner s ∈
        benMoves
          (insert s r)
          b := by

    simp only [
      benMoves,
      Finset.mem_filter,
      Finset.mem_univ,
      true_and
    ]

    constructor

    · intro hp

      rcases
        Finset.mem_insert.mp hp
      with hp | hp

      · exact
          hpns hp

      · exact
          hpnr hp

    · exact hpnb

  have h3 :
      ({partner s} : Finset Site) ∩
          benMoves
            (insert s r)
            b
        =
      {partner s} := by

    rw [Finset.inter_eq_left]

    intro x hx

    have hx' :
        x = partner s :=
      Finset.mem_singleton.mp hx

    subst x

    exact hmem

  unfold benStrat

  rw [h2, h3]

  have hnonempty :
      ({partner s} : Finset Site).Nonempty :=
    ⟨partner s,
     Finset.mem_singleton_self _⟩

  split
  next _ =>
    exact
      pick_singleton _

  next hbad =>
    exact
      False.elim
        (hbad hnonempty)

/-!
============================================================
12. Ben guarantees Amy gets at most 100
============================================================
-/

lemma upper_aux
    (A : Strat)
    (hA : ValidA A) :
    ∀ (n : ℕ) (r b : Finset Site),
      b = r.image partner →
      (∀ s ∈ r,
        ∀ t ∈ r,
          s ≠ t →
          ¬ sq5 s t) →
      Disjoint r b →
      play A benStrat n true r b +
          r.card ≤ 100 := by

  intro n

  refine
    Nat.strong_induction_on n ?_

  intro n ih r b hb hfree hd

  have hbase :
      r.card ≤ 100 :=
    card_le_hundred
      hfree
      (pair_free hb hd)

  cases n with

  | zero =>
      rw [play_zero]
      omega

  | succ n =>

      rw [play_amy]

      split

      next hmv =>

        have hsamy :
            A r b ∈ amyMoves r b :=
          hA r b hmv

        have hsamy' :=
          hsamy

        simp only [
          amyMoves,
          Finset.mem_filter,
          Finset.mem_univ,
          true_and
        ] at hsamy'

        obtain ⟨hpnr, hpnb, hpns⟩ :=
          step_facts
            hb
            hsamy'.1
            hsamy'.2.1

        have hcard' :
            (insert (A r b) r).card =
              r.card + 1 :=
          Finset.card_insert_of_notMem
            hsamy'.1

        have hfree' :
            ∀ u ∈ insert (A r b) r,
              ∀ v ∈ insert (A r b) r,
                u ≠ v →
                ¬ sq5 u v := by

          intro u hu v hv huv

          rcases Finset.mem_insert.mp hu with
            hu1 | hu1

          · rcases Finset.mem_insert.mp hv with
              hv1 | hv1

            · exact
                False.elim
                  (huv
                    (hu1.trans
                      hv1.symm))

            · subst u

              exact
                hsamy'.2.2
                  v
                  hv1

          · rcases Finset.mem_insert.mp hv with
              hv1 | hv1

            · subst v

              intro hc

              exact
                hsamy'.2.2
                  u
                  hu1
                  (sq5_symm hc)

            · exact
                hfree
                  u
                  hu1
                  v
                  hv1
                  huv

        have hpair' :
            ∀ u ∈ insert (A r b) r,
              partner u ∉
                insert (A r b) r := by

          intro u hu

          rw [Finset.mem_insert]

          rintro hpartner

          rcases hpartner with
            h3 | h3

          · rcases Finset.mem_insert.mp hu with
              hu1 | hu1

            · subst u

              exact hpns h3

            · have hu_eq :
                  u =
                    partner (A r b) := by

                have hh :=
                  congrArg partner h3

                simpa [partner_partner] using hh

              apply hpnr

              rw [← hu_eq]

              exact hu1

          · rcases Finset.mem_insert.mp hu with
              hu1 | hu1

            · subst u

              exact hpnr h3

            · exact
                pair_free
                  hb
                  hd
                  u
                  hu1
                  h3

        have hb100 :
            (insert (A r b) r).card ≤
              100 :=
          card_le_hundred
            hfree'
            hpair'

        cases n with

        | zero =>
            rw [play_zero]
            omega

        | succ k =>

            rw [play_ben]

            split

            next _ =>

              rw [
                benStrat_eq
                  hb
                  hsamy'.1
                  hsamy'.2.1
              ]

              have himg :
                  insert
                      (partner (A r b))
                      b
                    =
                  (insert
                    (A r b)
                    r).image
                    partner := by

                rw [
                  hb,
                  Finset.image_insert
                ]

              have hd' :
                  Disjoint
                    (insert (A r b) r)
                    (insert
                      (partner (A r b))
                      b) := by

                rw [Finset.disjoint_left]

                intro x hx hx2

                rcases
                  Finset.mem_insert.mp hx2
                with h3 | h3

                · rcases
                    Finset.mem_insert.mp hx
                  with h4 | h4

                  · have hEq :
                        partner (A r b) =
                          A r b :=
                      h3.symm.trans h4

                    exact
                      hpns hEq

                  · apply hpnr

                    rw [← h3]

                    exact h4

                · rcases
                    Finset.mem_insert.mp hx
                  with h4 | h4

                  · subst x

                    exact
                      hsamy'.2.1
                        h3

                  · exact
                      (Finset.disjoint_left.mp
                        hd
                        h4)
                        h3

              have hih :=
                ih
                  k
                  (by omega)
                  (insert (A r b) r)
                  (insert
                    (partner (A r b))
                    b)
                  himg
                  hfree'
                  hd'

              omega

            next _ =>
              omega

      next _ =>
        omega

/-!
============================================================
13. Final theorem
============================================================
-/

/--
IMO 2018 Problem 4.

100 is the largest number of red stones that Amy can
guarantee against every valid strategy of Ben.
-/
theorem imo2018_p4 :
    IsGreatest
      {K : ℕ |
        ∃ A : Strat,
          ValidA A ∧
          ∀ B : Strat,
            ValidB B →
            K ≤
              play A B 400 true ∅ ∅}
      100 := by

  constructor

  · refine
      ⟨amyStrat,
       amyStrat_valid,
       ?_⟩

    intro B hB

    exact
      lower_aux
        B
        hB
        100
        400
        ∅
        ∅
        (by norm_num)
        (by simp)
        (by simp)
        (by simp)
        (by simp)

  · rintro
      K
      ⟨A, hA, hK⟩

    have h1 :=
      hK
        benStrat
        benStrat_valid

    have h2 :=
      upper_aux
        A
        hA
        400
        ∅
        ∅
        (by simp)
        (by simp)
        (by simp)

    simp only [
      Finset.card_empty
    ] at h2

    omega

end Imo2018P4
