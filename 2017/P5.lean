import Mathlib

namespace IMO2017P5

open Finset

/--
A finite version of the induction lemma behind IMO 2017 P5.

`group p` records the height-block containing player `p`.
`rank p` records the player's height rank.
-/
structure PlayerData (m : ℕ) where
  Player : Type
  instFintype : Fintype Player
  instDecidableEq : DecidableEq Player
  group : Player → Fin m
  rank : Player → ℕ
  rank_injective : Function.Injective rank

attribute [instance]
  PlayerData.instFintype
  PlayerData.instDecidableEq

def groupSet {m : ℕ}
    (D : PlayerData m)
    (i : Fin m) : Finset D.Player :=
  Finset.univ.filter (fun p => D.group p = i)

/--
Every group contains at least `m + 1` players.
-/
def LargeGroups {m : ℕ}
    (D : PlayerData m) : Prop :=
  ∀ i : Fin m,
    m + 1 ≤ (groupSet D i).card

/--
Two selected players form an adjacent pair in height order
inside the selected set.
-/
def HeightAdjacent {m : ℕ}
    (D : PlayerData m)
    (S : Finset D.Player)
    (a b : D.Player) : Prop :=
  a ∈ S ∧
  b ∈ S ∧
  a ≠ b ∧
  ∀ c ∈ S,
    c ≠ a →
    c ≠ b →
    ¬ (
      (D.rank a < D.rank c ∧ D.rank c < D.rank b) ∨
      (D.rank b < D.rank c ∧ D.rank c < D.rank a)
    )

end IMO2017P5
