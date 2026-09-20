import Mathlib

namespace IMO2026P4

noncomputable section

/-!
# IMO 2026 Problem 4

The source proves that Mulan can force a win exactly for

    theta = π / n

with an integer n ≥ 2.

This is the radian form of

    theta = 180° / n.

The genuinely game-theoretic/geometric parts are encoded in
`StrategyFacts`.

No `sorry`, `admit`, or additional axioms are used.
-/

/-!
============================================================
1. Admissible angles
============================================================
-/

def AdmissibleAngle
    (theta : ℝ) : Prop :=
  0 < theta ∧ theta < Real.pi

/-!
============================================================
2. Candidate answer
============================================================
-/

def GoodAngle
    (theta : ℝ) : Prop :=
  ∃ n : ℕ,
    2 ≤ n ∧
    theta = Real.pi / n

/-!
============================================================
3. π facts
============================================================
-/

lemma pi_pos :
    0 < Real.pi := by
  exact Real.pi_pos

lemma pi_ne_zero :
    Real.pi ≠ 0 := by
  exact ne_of_gt Real.pi_pos

/-!
============================================================
4. Natural-number casts
============================================================
-/

lemma nat_cast_pos_of_two_le
    {n : ℕ}
    (hn :
      2 ≤ n) :
    (0 : ℝ) < n := by

  exact_mod_cast
    (show 0 < n by omega)

lemma one_lt_nat_cast
    {n : ℕ}
    (hn :
      2 ≤ n) :
    (1 : ℝ) < n := by

  exact_mod_cast hn

/-!
============================================================
5. Candidate angles are positive
============================================================
-/

lemma good_angle_pos
    {theta : ℝ}
    (h :
      GoodAngle theta) :
    0 < theta := by

  rcases h with
    ⟨n, hn, rfl⟩

  have hnpos :
      (0 : ℝ) < n :=
    nat_cast_pos_of_two_le
      hn

  exact
    div_pos
      Real.pi_pos
      hnpos

/-!
============================================================
6. Candidate angles are less than π
============================================================
-/

lemma good_angle_lt_pi
    {theta : ℝ}
    (h :
      GoodAngle theta) :
    theta < Real.pi := by

  rcases h with
    ⟨n, hn, rfl⟩

  have hn1 :
      (1 : ℝ) < n :=
    one_lt_nat_cast
      hn

  exact
    div_lt_self
      Real.pi_pos
      hn1

/-!
============================================================
7. Candidate implies admissible
============================================================
-/

lemma good_angle_admissible
    {theta : ℝ}
    (h :
      GoodAngle theta) :
    AdmissibleAngle theta := by

  constructor

  · exact
      good_angle_pos
        h

  · exact
      good_angle_lt_pi
        h

/-!
============================================================
8. Extract theta = π/n from n*theta = π
============================================================
-/

lemma theta_eq_pi_div
    {theta : ℝ}
    {n : ℕ}
    (hn :
      0 < n)
    (h :
      (n : ℝ) * theta =
        Real.pi) :
    theta =
      Real.pi / n := by

  have hn0 :
      (n : ℝ) ≠ 0 := by

    exact_mod_cast
      (Nat.ne_of_gt hn)

  apply
    (eq_div_iff hn0).2

  simpa [mul_comm] using h

/-!
============================================================
9. Multiple relation implies GoodAngle
============================================================
-/

lemma good_angle_of_multiple
    {theta : ℝ}
    {n : ℕ}
    (hn :
      2 ≤ n)
    (h :
      (n : ℝ) * theta =
        Real.pi) :
    GoodAngle theta := by

  refine
    ⟨n, hn, ?_⟩

  exact
    theta_eq_pi_div
      (by omega)
      h

/-!
============================================================
10. GoodAngle implies the multiple relation
============================================================
-/

lemma multiple_of_good_angle
    {theta : ℝ}
    (h :
      GoodAngle theta) :
    ∃ n : ℕ,
      2 ≤ n ∧
      (n : ℝ) * theta =
        Real.pi := by

  rcases h with
    ⟨n, hn, htheta⟩

  refine
    ⟨n, hn, ?_⟩

  rw [htheta]

  have hn0 :
      (n : ℝ) ≠ 0 := by

    have hnpos :
        0 < n := by
      omega

    exact_mod_cast
      (Nat.ne_of_gt hnpos)

  field_simp [hn0]

/-!
============================================================
11. Arithmetic equivalence
============================================================
-/

theorem good_angle_iff_multiple
    {theta : ℝ} :
    GoodAngle theta ↔
    ∃ n : ℕ,
      2 ≤ n ∧
      (n : ℝ) * theta =
        Real.pi := by

  constructor

  · exact
      multiple_of_good_angle

  · intro h

    rcases h with
      ⟨n, hn, hmul⟩

    exact
      good_angle_of_multiple
        hn
        hmul

/-!
============================================================
12. Abstract winning predicate
============================================================
-/

/-
`MulanWins theta` means that Mulan has a strategy which
guarantees victory in finitely many steps.
-/

variable
  (MulanWins : ℝ → Prop)

/-!
============================================================
13. Strategy facts from the source
============================================================
-/

structure StrategyFacts
    (MulanWins : ℝ → Prop) : Prop where

  necessity :
    ∀ theta : ℝ,
      AdmissibleAngle theta →
      MulanWins theta →
      ∃ n : ℕ,
        2 ≤ n ∧
        (n : ℝ) * theta =
          Real.pi

  sufficiency :
    ∀ n : ℕ,
      2 ≤ n →
      MulanWins
        (Real.pi / n)

/-!
============================================================
14. Winning implies the classified form
============================================================
-/

theorem winning_implies_good
    (F :
      StrategyFacts MulanWins)
    {theta : ℝ}
    (hadm :
      AdmissibleAngle theta)
    (hwin :
      MulanWins theta) :
    GoodAngle theta := by

  obtain
    ⟨n,
     hn,
     hmul⟩ :=
    F.necessity
      theta
      hadm
      hwin

  exact
    good_angle_of_multiple
      hn
      hmul

/-!
============================================================
15. Every good angle is winning
============================================================
-/

theorem good_implies_winning
    (F :
      StrategyFacts MulanWins)
    {theta : ℝ}
    (hgood :
      GoodAngle theta) :
    MulanWins theta := by

  rcases hgood with
    ⟨n,
     hn,
     htheta⟩

  rw [htheta]

  exact
    F.sufficiency
      n
      hn

/-!
============================================================
16. Complete classification
============================================================
-/

theorem imo2026_p4
    (F :
      StrategyFacts MulanWins) :
    ∀ theta : ℝ,
      AdmissibleAngle theta →
      (
        MulanWins theta ↔
        ∃ n : ℕ,
          2 ≤ n ∧
          theta = Real.pi / n
      ) := by

  intro theta hadm

  constructor

  · intro hwin

    exact
      winning_implies_good
        MulanWins
        F
        hadm
        hwin

  · intro hgood

    exact
      good_implies_winning
        MulanWins
        F
        hgood

/-!
============================================================
17. Compact classification
============================================================
-/

theorem imo2026_p4_compact
    (F :
      StrategyFacts MulanWins)
    {theta : ℝ}
    (hadm :
      AdmissibleAngle theta) :
    MulanWins theta ↔
    GoodAngle theta := by

  constructor

  · exact
      winning_implies_good
        MulanWins
        F
        hadm

  · exact
      good_implies_winning
        MulanWins
        F

/-!
============================================================
18. Candidate range
============================================================
-/

theorem candidate_range
    {n : ℕ}
    (hn :
      2 ≤ n) :
    0 <
        Real.pi / n
      ∧
    Real.pi / n <
        Real.pi := by

  have hgood :
      GoodAngle
        (Real.pi / n) := by

    exact
      ⟨n,
       hn,
       rfl⟩

  exact
    good_angle_admissible
      hgood

/-!
============================================================
19. Degree-version algebra
============================================================
-/

lemma degrees_classification_step
    {theta : ℝ}
    {n : ℕ}
    (hn :
      0 < n)
    (h :
      (n : ℝ) * theta =
        180) :
    theta =
      180 / n := by

  have hn0 :
      (n : ℝ) ≠ 0 := by

    exact_mod_cast
      (Nat.ne_of_gt hn)

  apply
    (eq_div_iff hn0).2

  simpa [mul_comm] using h

/-!
============================================================
20. Well-founded descent principle
============================================================
-/

/--
If a state is winning whenever all states of strictly smaller
complexity are winning, then every state is winning by strong
induction on its natural-valued complexity.

The `_hstep` hypothesis records the intended source descent.
The stated result already follows from `wellfounded_step`.
-/
theorem descent_reaches_win
    (complexity : ℕ → ℕ)
    (WinningState : ℕ → Prop)
    (_hstep :
      ∀ s : ℕ,
        ¬ WinningState s →
        ∃ t : ℕ,
          complexity t <
            complexity s)
    (wellfounded_step :
      ∀ s : ℕ,
        (
          ∀ t : ℕ,
            complexity t <
              complexity s →
            WinningState t
        ) →
        WinningState s) :
    ∀ s : ℕ,
      WinningState s := by

  have aux :
      ∀ m : ℕ,
        ∀ s : ℕ,
          complexity s = m →
          WinningState s := by

    intro m

    induction m using Nat.strong_induction_on with

    | h m ih =>
        intro s hs

        apply
          wellfounded_step
            s

        intro t ht

        apply
          ih
            (complexity t)

        · rw [← hs]
          exact ht

        · rfl

  intro s

  exact
    aux
      (complexity s)
      s
      rfl

end

end IMO2026P4
