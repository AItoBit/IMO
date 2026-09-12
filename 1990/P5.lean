import Mathlib

namespace IMO1990P5

/-- A chooses a number between `n` and `n²`. -/
def LegalA (n m : ℕ) : Prop :=
  n ≤ m ∧ m ≤ n ^ 2

/-- B divides by a positive power of a prime. -/
def LegalB (m k : ℕ) : Prop :=
  0 < k ∧
    ∃ p r : ℕ,
      Nat.Prime p ∧
      0 < r ∧
      m = k * p ^ r

/--
A has a well-founded winning strategy, with A to move.

Recursive occurrences are direct constructor arguments,
not nested inside conjunctions or disjunctions.
-/
inductive AWin : ℕ → Prop where
  | immediate {n : ℕ}
      (active : 1 < n)
      (legal : LegalA n 1990) :
      AWin n

  | step {n m : ℕ}
      (active : 1 < n)
      (legal : LegalA n m)
      (nonterminal : m ≠ 1990)
      (avoids_one :
        ∀ k : ℕ, LegalB m k → k ≠ 1)
      (continues :
        ∀ k : ℕ, LegalB m k → AWin k) :
      AWin n

/--
B has a well-founded winning strategy, with A to move.

`reply m` specifies B's response to A's choice `m`.
If the response is not 1, the strategy continues recursively.
-/
inductive BWin : ℕ → Prop where
  | step {n : ℕ}
      (active : 1 < n)
      (reply : ℕ → ℕ)
      (avoids_target :
        ∀ m : ℕ, LegalA n m → m ≠ 1990)
      (legal_reply :
        ∀ m : ℕ, LegalA n m → LegalB m (reply m))
      (continues :
        ∀ m : ℕ, LegalA n m →
          reply m ≠ 1 → BWin (reply m)) :
      BWin n

def Draw (n : ℕ) : Prop :=
  ¬ AWin n ∧ ¬ BWin n

theorem aWin_of_can_choose_1990
    {n : ℕ}
    (hn : 1 < n)
    (hlegal : LegalA n 1990) :
    AWin n := by
  exact AWin.immediate hn hlegal

theorem legalA_1990_of_between
    {n : ℕ}
    (hlo : 45 ≤ n)
    (hhi : n ≤ 1990) :
    LegalA n 1990 := by
  refine ⟨hhi, ?_⟩
  have hsquare : 45 * 45 ≤ n * n :=
    Nat.mul_le_mul hlo hlo
  nlinarith [hsquare]

theorem aWin_of_between_45_and_1990
    {n : ℕ}
    (hlo : 45 ≤ n)
    (hhi : n ≤ 1990) :
    AWin n := by
  exact aWin_of_can_choose_1990
    (n := n)
    (by omega)
    (legalA_1990_of_between hlo hhi)

theorem not_bWin_of_can_choose_1990
    {n : ℕ}
    (hlegal : LegalA n 1990) :
    ¬ BWin n := by
  intro h
  cases h with
  | step active reply avoids_target legal_reply continues =>
      exact avoids_target 1990 hlegal rfl

theorem not_bWin_of_between_45_and_1990
    {n : ℕ}
    (hlo : 45 ≤ n)
    (hhi : n ≤ 1990) :
    ¬ BWin n := by
  exact not_bWin_of_can_choose_1990
    (n := n)
    (legalA_1990_of_between hlo hhi)

theorem classification_between_45_and_1990
    {n : ℕ}
    (hlo : 45 ≤ n)
    (hhi : n ≤ 1990) :
    AWin n ∧ ¬ BWin n := by
  exact
    ⟨aWin_of_between_45_and_1990 hlo hhi,
      not_bWin_of_between_45_and_1990 hlo hhi⟩

end IMO1990P5
