import Mathlib

/-!
# IMO 1993, Problem 3 — the impossibility half

On an `n × n` board every square holds a piece. A move takes a piece, jumps it over an adjacent
piece into the empty square immediately beyond, and removes the jumped piece. Determine the `n`
for which the game can end with a single piece.

The answer is: exactly the `n` **not** divisible by `3`.

## What is in this file

The impossibility half — if `3 ∣ n` the game cannot end with one piece — is proved in full, with
no `sorry`, as `imo1993_p3_of_three_dvd`.

The other half (explicit play for every `n` not divisible by `3`) is **not** formalized; see the
note at the end.

## The invariant

Colour a square by `(i + j) mod 3`. Any three squares consecutive in a line carry the three
different colours. A jump removes a piece from two of the colours and adds one to the third, so
*every* colour count changes parity. Hence

  `w 0 S = w 1 S = w 2 S`  (parities of the three colour counts)

is preserved by play. On the full board with `3 ∣ n` the three counts are equal, so the relation
holds at the start; for a single piece the three parities are `1, 0, 0` in some order, so it
fails. Note the board bounds play no role: the argument is run on all of `ℤ × ℤ`, where there are
*more* legal moves, so the conclusion applies a fortiori to the real game.
-/

namespace Imo1993P3

/-- A square, as a point of the integer lattice. -/
abbrev Pos := ℤ × ℤ

/-- The colour of a square. -/
def color (p : Pos) : ZMod 3 := ((p.1 + p.2 : ℤ) : ZMod 3)

/-- One jump: a piece at `p` hops over the piece at `p + d` into the empty square `p + 2d`. -/
def Move (S T : Finset Pos) : Prop :=
  ∃ p d : Pos, (d = (1, 0) ∨ d = (-1, 0) ∨ d = (0, 1) ∨ d = (0, -1)) ∧
    p ∈ S ∧ (p.1 + d.1, p.2 + d.2) ∈ S ∧
    (p.1 + 2 * d.1, p.2 + 2 * d.2) ∉ S ∧
    T = insert (p.1 + 2 * d.1, p.2 + 2 * d.2)
      ((S.erase p).erase (p.1 + d.1, p.2 + d.2))

/-- Parity of the number of pieces of colour `c`. -/
def w (c : ZMod 3) (S : Finset Pos) : ZMod 2 := ∑ p ∈ S, (if color p = c then 1 else 0)

/-- Of three squares carrying the three different colours, exactly one has colour `c`. -/
theorem colors_sum (e : ZMod 3) (he : e = 1 ∨ e = 2) (x c : ZMod 3) :
    (if x = c then (1 : ZMod 2) else 0) + (if x + e = c then 1 else 0)
      + (if x + 2 * e = c then 1 else 0) = 1 := by
  rcases he with rfl | rfl <;> revert x c <;> decide

/-- Every colour parity flips on each jump. -/
theorem w_move {S T : Finset Pos} (h : Move S T) (c : ZMod 3) : w c T = w c S + 1 := by
  obtain ⟨p, d, hd, hp, hq, hr, rfl⟩ := h
  have hcq : color (p.1 + d.1, p.2 + d.2) = color p + ((d.1 + d.2 : ℤ) : ZMod 3) := by
    simp only [color]
    push_cast
    ring
  have hcr : color (p.1 + 2 * d.1, p.2 + 2 * d.2)
      = color p + 2 * ((d.1 + d.2 : ℤ) : ZMod 3) := by
    simp only [color]
    push_cast
    ring
  have he : ((d.1 + d.2 : ℤ) : ZMod 3) = 1 ∨ ((d.1 + d.2 : ℤ) : ZMod 3) = 2 := by
    rcases hd with rfl | rfl | rfl | rfl <;> norm_num <;> decide
  have hqp : (p.1 + d.1, p.2 + d.2) ≠ p := by
    intro hcon
    rcases hd with rfl | rfl | rfl | rfl <;> simp [Prod.ext_iff] at hcon
  have hqmem : (p.1 + d.1, p.2 + d.2) ∈ S.erase p := Finset.mem_erase.2 ⟨hqp, hq⟩
  have hrmem : (p.1 + 2 * d.1, p.2 + 2 * d.2)
      ∉ (S.erase p).erase (p.1 + d.1, p.2 + d.2) := by
    intro hcon
    exact hr (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hcon))
  unfold w
  rw [Finset.sum_insert hrmem]
  have e1 := Finset.add_sum_erase S (fun x : Pos => if color x = c then (1 : ZMod 2) else 0) hp
  have e2 := Finset.add_sum_erase (S.erase p)
    (fun x : Pos => if color x = c then (1 : ZMod 2) else 0) hqmem
  have hsum := colors_sum _ he (color p) c
  rw [hcq] at e2
  rw [hcr]
  have hchar : ∀ z : ZMod 2, z + z = 0 := by decide
  linear_combination e1 + e2 + hsum
    - hchar (if color p = c then (1 : ZMod 2) else 0)
    - hchar (if color p + ((d.1 + d.2 : ℤ) : ZMod 3) = c then (1 : ZMod 2) else 0)

/-- The full `n × n` board. -/
def board (n : ℕ) : Finset Pos :=
  (Finset.range n ×ˢ Finset.range n).image (fun q : ℕ × ℕ => ((q.1 : ℤ), (q.2 : ℤ)))

theorem color_nat (i j : ℕ) : color ((i : ℤ), (j : ℤ)) = ((i + j : ℕ) : ZMod 3) := by
  simp only [color]
  push_cast
  ring

/-- Each row of length `3m` contains `m` squares of each colour. -/
theorem row_sum (m i : ℕ) (c : ZMod 3) :
    ∑ j ∈ Finset.range (3 * m), (if ((i + j : ℕ) : ZMod 3) = c then (1 : ZMod 2) else 0)
      = (m : ZMod 2) := by
  have h30 : (3 : ZMod 3) = 0 := by decide
  induction m with
  | zero => simp
  | succ m ih =>
    have h3 : 3 * (m + 1) = 3 * m + 1 + 1 + 1 := by ring
    rw [h3, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, ih]
    have c0 : ((i + 3 * m : ℕ) : ZMod 3) = ((i : ℕ) : ZMod 3) := by
      push_cast
      rw [h30]
      ring
    have c1 : ((i + (3 * m + 1) : ℕ) : ZMod 3) = ((i : ℕ) : ZMod 3) + 1 := by
      push_cast
      rw [h30]
      ring
    have c2 : ((i + (3 * m + 1 + 1) : ℕ) : ZMod 3) = ((i : ℕ) : ZMod 3) + 2 * 1 := by
      push_cast
      rw [h30]
      ring
    rw [c0, c1, c2]
    have hsum := colors_sum 1 (Or.inl rfl) ((i : ℕ) : ZMod 3) c
    push_cast
    linear_combination hsum

theorem w_board (m : ℕ) (c : ZMod 3) : w c (board (3 * m)) = ((3 * m * m : ℕ) : ZMod 2) := by
  unfold w board
  rw [Finset.sum_image (by intro x _ y _ hxy; simpa [Prod.ext_iff] using hxy)]
  rw [Finset.sum_product]
  have hrow : ∀ i ∈ Finset.range (3 * m),
      (∑ j ∈ Finset.range (3 * m),
        (if color (((i : ℕ) : ℤ), ((j : ℕ) : ℤ)) = c then (1 : ZMod 2) else 0))
      = (m : ZMod 2) := by
    intro i _
    rw [← row_sum m i c]
    exact Finset.sum_congr rfl fun j _ => by rw [color_nat]
  rw [Finset.sum_congr rfl hrow, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring

/-- **IMO 1993 P3, impossibility half.** If `3 ∣ n` the game on the `n × n` board can never be
reduced to a single piece. -/
theorem imo1993_p3_of_three_dvd (m : ℕ) (S : Finset Pos)
    (h : Relation.ReflTransGen Move (board (3 * m)) S) : S.card ≠ 1 := by
  have key : ∀ T, Relation.ReflTransGen Move (board (3 * m)) T →
      ∃ k : ZMod 2, ∀ c, w c T = ((3 * m * m : ℕ) : ZMod 2) + k := by
    intro T hT
    induction hT with
    | refl => exact ⟨0, fun c => by rw [w_board]; ring⟩
    | tail _ hstep ih =>
      obtain ⟨k, hk⟩ := ih
      exact ⟨k + 1, fun c => by rw [w_move hstep c, hk c]; ring⟩
  obtain ⟨k, hk⟩ := key S h
  intro hcard
  obtain ⟨p, rfl⟩ := Finset.card_eq_one.1 hcard
  have hw : ∀ c, w c ({p} : Finset Pos) = if color p = c then 1 else 0 := by
    intro c
    rw [w, Finset.sum_singleton]
  have heq01 : (if color p = (0 : ZMod 3) then (1 : ZMod 2) else 0)
      = (if color p = (1 : ZMod 3) then (1 : ZMod 2) else 0) := by
    rw [← hw, ← hw, hk 0, hk 1]
  have heq02 : (if color p = (0 : ZMod 3) then (1 : ZMod 2) else 0)
      = (if color p = (2 : ZMod 3) then (1 : ZMod 2) else 0) := by
    rw [← hw, ← hw, hk 0, hk 2]
  have hc3 : ∀ x : ZMod 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
  rcases hc3 (color p) with hc | hc | hc <;> rw [hc] at heq01 heq02 <;>
    revert heq01 heq02 <;> decide

/-!
### The other half

For `n` not divisible by `3` the game *can* be finished, but the proof is an explicit strategy:
a base construction for `n = 2` and `n = 4`, a routine for clearing three border rows that
reduces an `(r+3) × s` rectangle to an `r × s` one, and a routine for shortening a `2 × s`
rectangle by three. Formalizing it means exhibiting and verifying concrete move sequences by
induction on `n`, which is a separate and much larger development; it is not attempted here.
-/

end Imo1993P3
