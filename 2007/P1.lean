import Mathlib

/-!
IMO 2007, Problem 1.

We index a nonempty sequence of length n + 1 by Fin (n + 1), starting
at zero. This is just a relabelling of the problem's indices 1, ..., N.
The definitions below use the actual finite maxima and minima.
-/

namespace IMO2007P1

variable {n : ℕ}

noncomputable def prefixMax (a : Fin (n + 1) → ℝ) (i : Fin (n + 1)) : ℝ :=
  (Finset.Iic i).sup' ⟨i, by simp⟩ a

noncomputable def suffixMin (a : Fin (n + 1) → ℝ) (i : Fin (n + 1)) : ℝ :=
  (Finset.Ici i).inf' ⟨i, by simp⟩ a

noncomputable def gap (a : Fin (n + 1) → ℝ) (i : Fin (n + 1)) : ℝ :=
  prefixMax a i - suffixMin a i

noncomputable def d (a : Fin (n + 1) → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (gap a)

noncomputable def error (a x : Fin (n + 1) → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => |x i - a i|)

lemma le_prefixMax (a : Fin (n + 1) → ℝ)
    {i j : Fin (n + 1)} (h : j ≤ i) : a j ≤ prefixMax a i := by
  exact Finset.le_sup' a (Finset.mem_Iic.mpr h)

lemma suffixMin_le (a : Fin (n + 1) → ℝ)
    {i j : Fin (n + 1)} (h : i ≤ j) : suffixMin a i ≤ a j := by
  exact Finset.inf'_le a (Finset.mem_Ici.mpr h)

lemma gap_le_d (a : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    gap a i ≤ d a := by
  exact Finset.le_sup' (gap a) (Finset.mem_univ i)

lemma abs_le_error (a x : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    |x i - a i| ≤ error a x := by
  exact Finset.le_sup' (fun j => |x j - a j|) (Finset.mem_univ i)

lemma prefixMax_monotone (a : Fin (n + 1) → ℝ) :
    Monotone (prefixMax a) := by
  intro i j hij
  unfold prefixMax
  apply Finset.sup'_le
  intro k hk
  exact Finset.le_sup' a
    (Finset.mem_Iic.mpr (le_trans (Finset.mem_Iic.mp hk) hij))

/-- Part (a): every nondecreasing sequence has error at least d / 2. -/
theorem part_a (a x : Fin (n + 1) → ℝ) (hx : Monotone x) :
    d a / 2 ≤ error a x := by
  have hgap : ∀ i, gap a i ≤ 2 * error a x := by
    intro i
    have hp : prefixMax a i ≤ x i + error a x := by
      unfold prefixMax
      apply Finset.sup'_le
      intro j hj
      have hjx := hx (Finset.mem_Iic.mp hj)
      have hjerr := (abs_le.mp (abs_le_error a x j)).1
      linarith
    have hs : x i - error a x ≤ suffixMin a i := by
      unfold suffixMin
      apply Finset.le_inf'
      intro j hj
      have hjx := hx (Finset.mem_Ici.mp hj)
      have hjerr := (abs_le.mp (abs_le_error a x j)).2
      linarith
    unfold gap
    linarith
  have hd : d a ≤ 2 * error a x := by
    unfold d
    apply Finset.sup'_le
    intro i _
    exact hgap i
  linarith

/-- The explicit optimal nondecreasing sequence. -/
noncomputable def optimal (a : Fin (n + 1) → ℝ) (i : Fin (n + 1)) : ℝ :=
  prefixMax a i - d a / 2

theorem optimal_monotone (a : Fin (n + 1) → ℝ) :
    Monotone (optimal a) := by
  intro i j hij
  exact sub_le_sub_right (prefixMax_monotone a hij) (d a / 2)

theorem optimal_error (a : Fin (n + 1) → ℝ) :
    error a (optimal a) = d a / 2 := by
  apply le_antisymm
  · unfold error
    apply Finset.sup'_le
    intro i _
    have hp : a i ≤ prefixMax a i := le_prefixMax a le_rfl
    have hs : suffixMin a i ≤ a i := suffixMin_le a le_rfl
    have hg : prefixMax a i - suffixMin a i ≤ d a := gap_le_d a i
    change |prefixMax a i - d a / 2 - a i| ≤ d a / 2
    apply abs_le.mpr
    constructor <;> linarith
  · exact part_a a (optimal a) (optimal_monotone a)

/-- Part (b): the lower bound is attained. -/
theorem part_b (a : Fin (n + 1) → ℝ) :
    ∃ x : Fin (n + 1) → ℝ, Monotone x ∧ error a x = d a / 2 := by
  exact ⟨optimal a, optimal_monotone a, optimal_error a⟩

/-- Both conclusions of IMO 2007 Problem 1. -/
theorem imo2007_p1 (a : Fin (n + 1) → ℝ) :
    (∀ x : Fin (n + 1) → ℝ, Monotone x → d a / 2 ≤ error a x) ∧
    (∃ x : Fin (n + 1) → ℝ, Monotone x ∧ error a x = d a / 2) := by
  exact ⟨fun x hx => part_a a x hx, part_b a⟩

end IMO2007P1
