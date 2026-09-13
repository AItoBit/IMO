import Mathlib

/-!
# IMO 1996, Problem 1

A `20 × 12` board of unit squares; a move goes between squares whose centres are at distance
`√r`. Starting from the corner square `A`, can one reach the corner square `B`?

Centres get integer coordinates, `A = (1,1)`, `B = (20,1)`, with `1 ≤ x ≤ 20`, `1 ≤ y ≤ 12`.

* (a) impossible when `2 ∣ r` or `3 ∣ r`;
* (b) possible when `r = 73`;
* (c) impossible when `r = 97`.

All three are proved, with no `sorry`.

## Invariants

* `2 ∣ r`: then `Δx ≡ Δy (mod 2)`, so `x - y mod 2` never changes. It is `0` at `A` and `1` at `B`.
* `3 ∣ r`: then `Δx ≡ Δy ≡ 0 (mod 3)`, so `x mod 3` never changes. It is `1` at `A` and `2` at `B`.
* `r = 97`: the only representation is `97 = 9² + 4²`, so a move shifts one coordinate by `9` and
  the other by `4`. Cut the board into three horizontal bands `1–4`, `5–8`, `9–12` and let
  `blk y` be the parity of the band index. A `(±9, ±4)` move flips both `x mod 2` and `blk y`; a
  `(±4, ±9)` move preserves both — the second because a `±9` step in `y` staying inside
  `1 ≤ y ≤ 12` must go between the bands `1–4` and `9–12`, which have the same parity. So
  `x mod 2 + blk y` is invariant; it is `0` at `A` and `1` at `B`.
-/

set_option maxHeartbeats 1000000

namespace Imo1996P1

abbrev Pos := ℤ × ℤ

/-- The centre of a square of the board. -/
def OnBoard (p : Pos) : Prop := 1 ≤ p.1 ∧ p.1 ≤ 20 ∧ 1 ≤ p.2 ∧ p.2 ≤ 12

/-- A legal move for the parameter `r`. -/
def Move (r : ℤ) (p q : Pos) : Prop :=
  OnBoard p ∧ OnBoard q ∧
    (q.1 - p.1) * (q.1 - p.1) + (q.2 - p.2) * (q.2 - p.2) = r

/-- Reachability by legal moves. -/
def Reach (r : ℤ) : Pos → Pos → Prop := Relation.ReflTransGen (Move r)

/-- Anything constant along moves is constant along reachability. -/
theorem inv_of_reach {r : ℤ} {α : Type*} (f : Pos → α)
    (hinv : ∀ p q, Move r p q → f p = f q) {p q : Pos} (h : Reach r p q) : f p = f q := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact ih.trans (hinv _ _ hstep)

/-! ### Part (a) -/

theorem sq_add_sq_zmod_two {a b : ℤ}
    (h : ((a : ZMod 2)) * (a : ZMod 2) + ((b : ZMod 2)) * (b : ZMod 2) = 0) :
    ((a : ZMod 2)) = ((b : ZMod 2)) := by
  revert h
  generalize ((a : ZMod 2)) = A
  generalize ((b : ZMod 2)) = B
  revert A B
  decide

theorem sq_add_sq_zmod_three {a b : ℤ}
    (h : ((a : ZMod 3)) * (a : ZMod 3) + ((b : ZMod 3)) * (b : ZMod 3) = 0) :
    ((a : ZMod 3)) = 0 ∧ ((b : ZMod 3)) = 0 := by
  revert h
  generalize ((a : ZMod 3)) = A
  generalize ((b : ZMod 3)) = B
  revert A B
  decide

/-- **Part (a), the case `2 ∣ r`.** -/
theorem part_a_two (r : ℤ) (hr : (2 : ℤ) ∣ r) : ¬ Reach r (1, 1) (20, 1) := by
  intro hreach
  have hinv : ∀ p q : Pos, Move r p q →
      ((p.1 - p.2 : ℤ) : ZMod 2) = ((q.1 - q.2 : ℤ) : ZMod 2) := by
    rintro p q ⟨-, -, heq⟩
    have hz : (((q.1 - p.1) * (q.1 - p.1) + (q.2 - p.2) * (q.2 - p.2) : ℤ) : ZMod 2) = 0 := by
      rw [heq]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd r 2).2 (by exact_mod_cast hr)
    push_cast at hz
    have hab := sq_add_sq_zmod_two (a := q.1 - p.1) (b := q.2 - p.2)
      (by push_cast; linear_combination hz)
    push_cast at hab ⊢
    linear_combination -hab
  have h := inv_of_reach _ hinv hreach
  norm_num at h
  revert h
  decide

/-- **Part (a), the case `3 ∣ r`.** -/
theorem part_a_three (r : ℤ) (hr : (3 : ℤ) ∣ r) : ¬ Reach r (1, 1) (20, 1) := by
  intro hreach
  have hinv : ∀ p q : Pos, Move r p q → ((p.1 : ℤ) : ZMod 3) = ((q.1 : ℤ) : ZMod 3) := by
    rintro p q ⟨-, -, heq⟩
    have hz : (((q.1 - p.1) * (q.1 - p.1) + (q.2 - p.2) * (q.2 - p.2) : ℤ) : ZMod 3) = 0 := by
      rw [heq]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd r 3).2 (by exact_mod_cast hr)
    push_cast at hz
    have hab := sq_add_sq_zmod_three (a := q.1 - p.1) (b := q.2 - p.2)
      (by push_cast; linear_combination hz)
    have h1 := hab.1
    push_cast at h1 ⊢
    linear_combination -h1
  have h := inv_of_reach _ hinv hreach
  norm_num at h
  revert h
  decide

/-! ### Part (b) -/

/-- **Part (b).** The eleven moves of the AoPS solution. -/
theorem part_b : Reach 73 (1, 1) (20, 1) := by
  refine Relation.ReflTransGen.head (b := ((4 : ℤ), (9 : ℤ))) (by norm_num [Move, OnBoard]) ?_
  refine Relation.ReflTransGen.head (b := ((12 : ℤ), (6 : ℤ))) (by norm_num [Move, OnBoard]) ?_
  refine Relation.ReflTransGen.head (b := ((20 : ℤ), (3 : ℤ))) (by norm_num [Move, OnBoard]) ?_
  refine Relation.ReflTransGen.head (b := ((17 : ℤ), (11 : ℤ))) (by norm_num [Move, OnBoard]) ?_
  refine Relation.ReflTransGen.head (b := ((9 : ℤ), (8 : ℤ))) (by norm_num [Move, OnBoard]) ?_
  refine Relation.ReflTransGen.head (b := ((1 : ℤ), (5 : ℤ))) (by norm_num [Move, OnBoard]) ?_
  refine Relation.ReflTransGen.head (b := ((9 : ℤ), (2 : ℤ))) (by norm_num [Move, OnBoard]) ?_
  refine Relation.ReflTransGen.head (b := ((12 : ℤ), (10 : ℤ))) (by norm_num [Move, OnBoard]) ?_
  refine Relation.ReflTransGen.head (b := ((4 : ℤ), (7 : ℤ))) (by norm_num [Move, OnBoard]) ?_
  refine Relation.ReflTransGen.head (b := ((12 : ℤ), (4 : ℤ))) (by norm_num [Move, OnBoard]) ?_
  refine Relation.ReflTransGen.head (b := ((20 : ℤ), (1 : ℤ))) (by norm_num [Move, OnBoard]) ?_
  exact Relation.ReflTransGen.refl

/-! ### Part (c) -/

/-- `97 = 9² + 4²` is the only representation. -/
theorem sol97 {a b : ℤ} (h : a * a + b * b = 97) :
    ((a = 9 ∨ a = -9) ∧ (b = 4 ∨ b = -4)) ∨ ((a = 4 ∨ a = -4) ∧ (b = 9 ∨ b = -9)) := by
  have ha1 : -9 ≤ a := by nlinarith [mul_self_nonneg b, mul_self_nonneg (a + 10)]
  have ha2 : a ≤ 9 := by nlinarith [mul_self_nonneg b, mul_self_nonneg (a - 10)]
  have hb1 : -9 ≤ b := by nlinarith [mul_self_nonneg a, mul_self_nonneg (b + 10)]
  have hb2 : b ≤ 9 := by nlinarith [mul_self_nonneg a, mul_self_nonneg (b - 10)]
  interval_cases a <;> interval_cases b <;> omega

/-- Parity of the horizontal band `1–4`, `5–8`, `9–12`. -/
def blk (y : ℤ) : ZMod 2 := if y ≤ 4 then 1 else if y ≤ 8 then 0 else 1

theorem blk_add_four {y : ℤ} (h1 : 1 ≤ y) (h2 : y + 4 ≤ 12) : blk (y + 4) = blk y + 1 := by
  have h3 : y ≤ 8 := by omega
  interval_cases y <;> norm_num [blk] <;> decide

theorem blk_sub_four {y : ℤ} (h1 : 1 ≤ y - 4) (h2 : y ≤ 12) : blk (y - 4) = blk y + 1 := by
  have h3 : 5 ≤ y := by omega
  interval_cases y <;> norm_num [blk] <;> decide

theorem blk_add_nine {y : ℤ} (h1 : 1 ≤ y) (h2 : y + 9 ≤ 12) : blk (y + 9) = blk y := by
  have h3 : y ≤ 3 := by omega
  interval_cases y <;> norm_num [blk]

theorem blk_sub_nine {y : ℤ} (h1 : 1 ≤ y - 9) (h2 : y ≤ 12) : blk (y - 9) = blk y := by
  have h3 : 10 ≤ y := by omega
  interval_cases y <;> norm_num [blk]

/-- The invariant for `r = 97`. -/
def inv97 (p : Pos) : ZMod 2 := ((p.1 : ℤ) : ZMod 2) + blk p.2

/-- **Part (c).** -/
theorem part_c : ¬ Reach 97 (1, 1) (20, 1) := by
  intro hreach
  have hc2 : (2 : ZMod 2) = 0 := by decide
  have hinv : ∀ p q : Pos, Move 97 p q → inv97 p = inv97 q := by
    rintro p q ⟨⟨hp1, hp2, hp3, hp4⟩, ⟨hq1, hq2, hq3, hq4⟩, heq⟩
    rcases sol97 heq with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · -- `x` shifts by `±9`, `y` by `±4`: both parities flip
      have hxs : ((q.1 : ℤ) : ZMod 2) = ((p.1 : ℤ) : ZMod 2) + 1 := by
        rcases ha with h | h
        · have hq : q.1 = p.1 + 9 := by omega
          rw [hq]; push_cast; linear_combination (4 : ZMod 2) * hc2
        · have hq : q.1 = p.1 - 9 := by omega
          rw [hq]; push_cast; linear_combination (-5 : ZMod 2) * hc2
      have hys : blk q.2 = blk p.2 + 1 := by
        rcases hb with h | h
        · have hq : q.2 = p.2 + 4 := by omega
          rw [hq]; exact blk_add_four hp3 (by omega)
        · have hq : q.2 = p.2 - 4 := by omega
          rw [hq]; exact blk_sub_four (by omega) hp4
      unfold inv97
      rw [hxs, hys]
      linear_combination -hc2
    · -- `x` shifts by `±4`, `y` by `±9`: both parities are preserved
      have hxs : ((q.1 : ℤ) : ZMod 2) = ((p.1 : ℤ) : ZMod 2) := by
        rcases ha with h | h
        · have hq : q.1 = p.1 + 4 := by omega
          rw [hq]; push_cast; linear_combination (2 : ZMod 2) * hc2
        · have hq : q.1 = p.1 - 4 := by omega
          rw [hq]; push_cast; linear_combination (-2 : ZMod 2) * hc2
      have hys : blk q.2 = blk p.2 := by
        rcases hb with h | h
        · have hq : q.2 = p.2 + 9 := by omega
          rw [hq]; exact blk_add_nine hp3 (by omega)
        · have hq : q.2 = p.2 - 9 := by omega
          rw [hq]; exact blk_sub_nine (by omega) hp4
      unfold inv97
      rw [hxs, hys]
  have h := inv_of_reach _ hinv hreach
  unfold inv97 at h
  norm_num [blk] at h
  revert h
  decide

end Imo1996P1
