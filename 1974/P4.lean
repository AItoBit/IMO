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
# IMO 1974, Problem 4

Consider decompositions of an `8 × 8` chessboard into `p` non-overlapping rectangles subject to
the following conditions:

* (i) each rectangle has as many white squares as black squares;
* (ii) if `a i` is the number of white squares in the `i`-th rectangle, then
  `a 1 < a 2 < ⋯ < a p`.

Find the maximum value of `p` for which such a decomposition is possible.  For this value of `p`,
determine all possible sequences `a 1, a 2, …, a p`.

The answer is `p = 7`, and the possible sequences are

`1,2,3,4,5,7,10`,  `1,2,3,4,5,8,9`,  `1,2,3,4,6,7,9`,  `1,2,3,5,6,7,8`.
-/

namespace Imo1974P4

/-- An axis-parallel rectangle of cells, consisting of the cells `(r, c)` with
`r1 ≤ r < r2` and `c1 ≤ c < c2`. -/
structure Rect where
  r1 : ℕ
  r2 : ℕ
  c1 : ℕ
  c2 : ℕ
deriving DecidableEq

/-- The set of cells of a rectangle. -/
def Rect.cells (R : Rect) : Finset (ℕ × ℕ) := Finset.Ico R.r1 R.r2 ×ˢ Finset.Ico R.c1 R.c2

/-- The cells of the `8 × 8` chessboard. -/
def board : Finset (ℕ × ℕ) := Finset.range 8 ×ˢ Finset.range 8

/-- The number of white cells of a rectangle; a cell `(r, c)` is white when `r + c` is even. -/
def whiteCount (R : Rect) : ℕ := (R.cells.filter (fun q => (q.1 + q.2) % 2 = 0)).card

/-- The number of black cells of a rectangle; a cell `(r, c)` is black when `r + c` is odd. -/
def blackCount (R : Rect) : ℕ := (R.cells.filter (fun q => (q.1 + q.2) % 2 = 1)).card

/-- `R` is a decomposition of the chessboard into `p` non-empty, non-overlapping rectangles. -/
def IsDecomposition {p : ℕ} (R : Fin p → Rect) : Prop :=
  (∀ i, (R i).cells.Nonempty) ∧
  (∀ i j, i ≠ j → Disjoint (R i).cells (R j).cells) ∧
  Finset.univ.biUnion (fun i => (R i).cells) = board

/-- A decomposition of the chessboard satisfying conditions (i) and (ii) of the problem. -/
def IsGood {p : ℕ} (R : Fin p → Rect) : Prop :=
  IsDecomposition R ∧
  (∀ i, whiteCount (R i) = blackCount (R i)) ∧
  StrictMono (fun i => whiteCount (R i))

/-- The four sequences claimed to be the possible ones. -/
def answerSeqs : List (List ℕ) :=
  [[1, 2, 3, 4, 5, 7, 10], [1, 2, 3, 4, 5, 8, 9], [1, 2, 3, 4, 6, 7, 9], [1, 2, 3, 5, 6, 7, 8]]

/-! ### Basic counting lemmas -/

lemma Rect.card_cells (R : Rect) : R.cells.card = (R.r2 - R.r1) * (R.c2 - R.c1) := by
  simp [Rect.cells, Finset.card_product]

lemma card_board : board.card = 64 := by decide

lemma white_add_black (R : Rect) : whiteCount R + blackCount R = R.cells.card := by
  classical
  have h : (R.cells.filter (fun q => (q.1 + q.2) % 2 = 1))
      = (R.cells.filter (fun q => ¬ ((q.1 + q.2) % 2 = 0))) :=
    Finset.filter_congr (fun x _ => by omega)
  rw [whiteCount, blackCount, h, Finset.card_filter_add_card_filter_not]

lemma card_cells_eq_two_mul_white {R : Rect} (h : whiteCount R = blackCount R) :
    R.cells.card = 2 * whiteCount R := by
  have := white_add_black R
  omega

/-- In a nonempty rectangle contained in the board, both side lengths are at most `8`. -/
lemma rect_dims_le {R : Rect} (hs : R.cells ⊆ board) (hne : R.cells.Nonempty) :
    R.r2 - R.r1 ≤ 8 ∧ R.c2 - R.c1 ≤ 8 := by
  obtain ⟨⟨r, c⟩, hmem⟩ := hne
  simp only [Rect.cells, Finset.mem_product, Finset.mem_Ico] at hmem
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hmem
  have hr : (R.r2 - 1, R.c1) ∈ R.cells := by
    simp only [Rect.cells, Finset.mem_product, Finset.mem_Ico]
    omega
  have hc : (R.r1, R.c2 - 1) ∈ R.cells := by
    simp only [Rect.cells, Finset.mem_product, Finset.mem_Ico]
    omega
  have hr' := hs hr
  have hc' := hs hc
  simp only [board, Finset.mem_product, Finset.mem_range] at hr' hc'
  omega

/-- Each rectangle of a decomposition is contained in the board. -/
lemma cells_subset_board {p : ℕ} {R : Fin p → Rect} (hd : IsDecomposition R) (i : Fin p) :
    (R i).cells ⊆ board := by
  rw [← hd.2.2]
  exact Finset.subset_biUnion_of_mem (fun i => (R i).cells) (Finset.mem_univ i)

/-- The white counts of a decomposition satisfying (i) sum to `32`. -/
lemma sum_white_eq {p : ℕ} {R : Fin p → Rect} (hd : IsDecomposition R)
    (hb : ∀ i, whiteCount (R i) = blackCount (R i)) :
    ∑ i, whiteCount (R i) = 32 := by
  classical
  have hpw : ((Finset.univ : Finset (Fin p)) : Set (Fin p)).PairwiseDisjoint
      (fun i => (R i).cells) := by
    intro i _ j _ hij
    exact hd.2.1 i j hij
  have h1 : (Finset.univ.biUnion (fun i => (R i).cells)).card = ∑ i, ((R i).cells).card :=
    Finset.card_biUnion hpw
  rw [hd.2.2, card_board] at h1
  have h2 : ∑ i, ((R i).cells).card = ∑ i, 2 * whiteCount (R i) :=
    Finset.sum_congr rfl (fun i _ => card_cells_eq_two_mul_white (hb i))
  rw [h2, ← Finset.mul_sum] at h1
  omega

/-- Every rectangle of a good decomposition contains at least one white cell. -/
lemma one_le_white {p : ℕ} {R : Fin p → Rect} (hd : IsDecomposition R)
    (hb : ∀ i, whiteCount (R i) = blackCount (R i)) (i : Fin p) : 1 ≤ whiteCount (R i) := by
  have hne := hd.1 i
  have hcard : 0 < ((R i).cells).card := Finset.card_pos.mpr hne
  have := card_cells_eq_two_mul_white (hb i)
  omega

/-- Strict monotonicity forces `a i ≥ i + 1`. -/
lemma le_of_strictMono {p : ℕ} (a : Fin p → ℕ) (hmono : StrictMono a) (h1 : ∀ i, 1 ≤ a i) :
    ∀ i : Fin p, (i : ℕ) + 1 ≤ a i := by
  have key : ∀ n : ℕ, ∀ i : Fin p, (i : ℕ) = n → n + 1 ≤ a i := by
    intro n
    induction n with
    | zero => intro i _; exact h1 i
    | succ k ih =>
      intro i hi
      have hk : k < p := by have := i.isLt; omega
      have h2 := ih ⟨k, hk⟩ rfl
      have h3 : a ⟨k, hk⟩ < a i := by
        apply hmono
        simp [Fin.lt_def, hi]
      omega
  intro i
  exact key i i rfl

lemma sum_range_succ_two_mul (n : ℕ) : 2 * ∑ i ∈ Finset.range n, (i + 1) = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, Nat.mul_add, ih]
    ring

/-! ### The bound `p ≤ 7` -/

theorem imo1974_p4_le_seven {p : ℕ} {R : Fin p → Rect} (h : IsGood R) : p ≤ 7 := by
  obtain ⟨hd, hb, hmono⟩ := h
  have hsum := sum_white_eq hd hb
  have hle : ∀ i : Fin p, (i : ℕ) + 1 ≤ whiteCount (R i) :=
    le_of_strictMono _ hmono (one_le_white hd hb)
  have hbig : ∑ i : Fin p, ((i : ℕ) + 1) ≤ ∑ i : Fin p, whiteCount (R i) :=
    Finset.sum_le_sum (fun i _ => hle i)
  have hgauss : ∑ i : Fin p, ((i : ℕ) + 1) = ∑ i ∈ Finset.range p, (i + 1) := by
    rw [Finset.sum_range fun i => i + 1]
  rw [hgauss, hsum] at hbig
  have h2 := sum_range_succ_two_mul p
  by_contra hcon
  push_neg at hcon
  have : 8 * 9 ≤ p * (p + 1) := Nat.mul_le_mul (by omega) (by omega)
  omega

/-! ### The maximum `p = 7` is attained -/

/-- A decomposition realizing the sequence `1, 2, 3, 4, 5, 7, 10`. -/
def tilingA : Fin 7 → Rect
  | 0 => ⟨5, 7, 0, 1⟩
  | 1 => ⟨5, 7, 1, 3⟩
  | 2 => ⟨5, 7, 3, 6⟩
  | 3 => ⟨7, 8, 0, 8⟩
  | 4 => ⟨0, 5, 4, 6⟩
  | 5 => ⟨0, 7, 6, 8⟩
  | 6 => ⟨0, 5, 0, 4⟩

/-- A decomposition realizing the sequence `1, 2, 3, 4, 5, 8, 9`. -/
def tilingB : Fin 7 → Rect
  | 0 => ⟨6, 8, 0, 1⟩
  | 1 => ⟨0, 4, 5, 6⟩
  | 2 => ⟨4, 6, 3, 6⟩
  | 3 => ⟨0, 4, 3, 5⟩
  | 4 => ⟨6, 8, 1, 6⟩
  | 5 => ⟨0, 8, 6, 8⟩
  | 6 => ⟨0, 6, 0, 3⟩

/-- A decomposition realizing the sequence `1, 2, 3, 4, 6, 7, 9`. -/
def tilingC : Fin 7 → Rect
  | 0 => ⟨7, 8, 6, 8⟩
  | 1 => ⟨0, 4, 5, 6⟩
  | 2 => ⟨4, 6, 3, 6⟩
  | 3 => ⟨0, 4, 3, 5⟩
  | 4 => ⟨6, 8, 0, 6⟩
  | 5 => ⟨0, 7, 6, 8⟩
  | 6 => ⟨0, 6, 0, 3⟩

/-- A decomposition realizing the sequence `1, 2, 3, 5, 6, 7, 8`. -/
def tilingD : Fin 7 → Rect
  | 0 => ⟨7, 8, 2, 4⟩
  | 1 => ⟨6, 8, 4, 6⟩
  | 2 => ⟨5, 8, 6, 8⟩
  | 3 => ⟨0, 5, 6, 8⟩
  | 4 => ⟨0, 6, 4, 6⟩
  | 5 => ⟨0, 7, 2, 4⟩
  | 6 => ⟨0, 8, 0, 2⟩

lemma isGood_tilingA : IsGood tilingA := by
  refine ⟨⟨by decide, by decide, by decide⟩, by decide, ?_⟩
  rw [Fin.strictMono_iff_lt_succ]
  decide

lemma isGood_tilingB : IsGood tilingB := by
  refine ⟨⟨by decide, by decide, by decide⟩, by decide, ?_⟩
  rw [Fin.strictMono_iff_lt_succ]
  decide

lemma isGood_tilingC : IsGood tilingC := by
  refine ⟨⟨by decide, by decide, by decide⟩, by decide, ?_⟩
  rw [Fin.strictMono_iff_lt_succ]
  decide

lemma isGood_tilingD : IsGood tilingD := by
  refine ⟨⟨by decide, by decide, by decide⟩, by decide, ?_⟩
  rw [Fin.strictMono_iff_lt_succ]
  decide

theorem imo1974_p4_seven_attained : ∃ R : Fin 7 → Rect, IsGood R :=
  ⟨tilingA, isGood_tilingA⟩

/-! ### Determination of the sequences for `p = 7` -/

/-- A rectangle in the board cannot have exactly `11` white cells. -/
lemma white_ne_eleven {R : Rect} (hs : R.cells ⊆ board) (hne : R.cells.Nonempty)
    (hb : whiteCount R = blackCount R) : whiteCount R ≠ 11 := by
  intro h11
  have hcard := card_cells_eq_two_mul_white hb
  rw [h11, Rect.card_cells] at hcard
  obtain ⟨h1, h2⟩ := rect_dims_le hs hne
  set w := R.r2 - R.r1 with hw
  set h := R.c2 - R.c1 with hh
  interval_cases w <;> omega

theorem imo1974_p4_sequences {R : Fin 7 → Rect} (h : IsGood R) :
    List.ofFn (fun i => whiteCount (R i)) ∈ answerSeqs := by
  obtain ⟨hd, hb, hmono⟩ := h
  have hsum := sum_white_eq hd hb
  rw [Fin.sum_univ_seven] at hsum
  have hle : ∀ i : Fin 7, (i : ℕ) + 1 ≤ whiteCount (R i) :=
    le_of_strictMono _ hmono (one_le_white hd hb)
  have h0 := hle 0
  have h1 := hle 1
  have h2 := hle 2
  have h3 := hle 3
  have h4 := hle 4
  have h5 := hle 5
  have h6 := hle 6
  have hne : whiteCount (R 6) ≠ 11 :=
    white_ne_eleven (cells_subset_board hd 6) (hd.1 6) (hb 6)
  have hm01 : whiteCount (R 0) < whiteCount (R 1) := hmono (by decide)
  have hm12 : whiteCount (R 1) < whiteCount (R 2) := hmono (by decide)
  have hm23 : whiteCount (R 2) < whiteCount (R 3) := hmono (by decide)
  have hm34 : whiteCount (R 3) < whiteCount (R 4) := hmono (by decide)
  have hm45 : whiteCount (R 4) < whiteCount (R 5) := hmono (by decide)
  have hm56 : whiteCount (R 5) < whiteCount (R 6) := hmono (by decide)
  have hofn : List.ofFn (fun i => whiteCount (R i))
      = [whiteCount (R 0), whiteCount (R 1), whiteCount (R 2), whiteCount (R 3),
        whiteCount (R 4), whiteCount (R 5), whiteCount (R 6)] := rfl
  rw [hofn]
  simp only [answerSeqs, List.mem_cons, List.not_mem_nil, or_false, List.cons.injEq, and_true]
  omega

/-- **IMO 1974, Problem 4.** The maximum number of rectangles in such a decomposition is `7`. -/
theorem imo1974_p4_max_eq_seven :
    IsGreatest {p : ℕ | ∃ R : Fin p → Rect, IsGood R} 7 :=
  ⟨imo1974_p4_seven_attained, fun _ hp => by
    obtain ⟨R, hR⟩ := hp
    exact imo1974_p4_le_seven hR⟩

theorem imo1974_p4_sequences_attained :
    ∀ L ∈ answerSeqs, ∃ R : Fin 7 → Rect, IsGood R ∧ List.ofFn (fun i => whiteCount (R i)) = L := by
  intro L hL
  simp only [answerSeqs, List.mem_cons, List.not_mem_nil, or_false] at hL
  rcases hL with h | h | h | h
  · exact ⟨tilingA, isGood_tilingA, by subst h; decide⟩
  · exact ⟨tilingB, isGood_tilingB, by subst h; decide⟩
  · exact ⟨tilingC, isGood_tilingC, by subst h; decide⟩
  · exact ⟨tilingD, isGood_tilingD, by subst h; decide⟩

/-- **IMO 1974, Problem 4**, second part: for the maximal value `p = 7`, the set of sequences
`a 1 < a 2 < ⋯ < a 7` arising from such a decomposition is exactly the set of the four sequences
`1,2,3,4,5,7,10`, `1,2,3,4,5,8,9`, `1,2,3,4,6,7,9`, `1,2,3,5,6,7,8`. -/
theorem imo1974_p4_seq_set :
    {L : List ℕ | ∃ R : Fin 7 → Rect, IsGood R ∧ List.ofFn (fun i => whiteCount (R i)) = L} =
      {L : List ℕ | L ∈ answerSeqs} := by
  ext L
  constructor
  · rintro ⟨R, hR, rfl⟩
    exact imo1974_p4_sequences hR
  · intro hL
    exact imo1974_p4_sequences_attained L hL

end Imo1974P4
