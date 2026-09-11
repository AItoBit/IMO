import Mathlib

/-!
# IMO 1987, Problem 5

Let `n ≥ 3`. Prove that there is a set of `n` points in the plane such that the distance
between any two points is irrational and each set of three points determines a
non-degenerate triangle with rational area.

We use the points `(m, m²)` for `m = 0, …, n-1`.

* Distance: `√((a-b)² + (a²-b²)²) = |a-b| · √(1 + (a+b)²)`, and `1 + m²` is not a square
  for `m ≥ 1` (it lies strictly between `m²` and `(m+1)²`).
* Area (shoelace): `|(b-a)(c-a)(c-b)| / 2`, which is a nonzero rational.
  (This replaces Pick's theorem by a direct computation.)
-/

namespace Imo1987P5

/-- Euclidean distance between two points of `ℝ × ℝ`.
(Mathlib's `dist` on `ℝ × ℝ` is the sup metric, so we write it out.) -/
noncomputable def eDist (p q : ℝ × ℝ) : ℝ :=
  Real.sqrt ((p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2)

/-- Area of the triangle `pqr` (shoelace formula). It is `0` iff the points are collinear. -/
noncomputable def triArea (p q r : ℝ × ℝ) : ℝ :=
  |(q.1 - p.1) * (r.2 - p.2) - (r.1 - p.1) * (q.2 - p.2)| / 2

lemma not_isSquare_one_add_sq (m : ℕ) (hm : 1 ≤ m) : ¬ IsSquare (1 + m ^ 2) := by
  rintro ⟨s, hs⟩
  rcases le_or_gt s m with h | h
  · have := Nat.mul_le_mul h h
    nlinarith
  · have h' : m + 1 ≤ s := h
    have := Nat.mul_le_mul h' h'
    nlinarith

lemma irrational_eDist {a b : ℕ} (hab : a ≠ b) :
    Irrational (eDist ((a : ℝ), (a : ℝ) ^ 2) ((b : ℝ), (b : ℝ) ^ 2)) := by
  simp only [eDist]
  have key : ((a : ℝ) - b) ^ 2 + ((a : ℝ) ^ 2 - (b : ℝ) ^ 2) ^ 2
      = ((a : ℝ) - b) ^ 2 * ((1 + (a + b) ^ 2 : ℕ) : ℝ) := by
    push_cast
    ring
  rw [key, Real.sqrt_mul' _ (Nat.cast_nonneg _), Real.sqrt_sq_eq_abs]
  have hN : Irrational (Real.sqrt ((1 + (a + b) ^ 2 : ℕ) : ℝ)) := by
    rw [irrational_sqrt_natCast_iff]
    exact not_isSquare_one_add_sq (a + b) (by omega)
  have hq : |(a : ℝ) - b| = ((|(a : ℚ) - b| : ℚ) : ℝ) := by
    push_cast <;> ring
  have hab' : (a : ℚ) ≠ b := by exact_mod_cast hab
  have hq0 : |(a : ℚ) - b| ≠ 0 := (abs_pos.mpr (sub_ne_zero.mpr hab')).ne'
  rw [hq]
  exact hN.ratCast_mul hq0

lemma triArea_facts {a b c : ℕ} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    triArea ((a : ℝ), (a : ℝ) ^ 2) ((b : ℝ), (b : ℝ) ^ 2) ((c : ℝ), (c : ℝ) ^ 2) ≠ 0 ∧
      ∃ q : ℚ,
        triArea ((a : ℝ), (a : ℝ) ^ 2) ((b : ℝ), (b : ℝ) ^ 2) ((c : ℝ), (c : ℝ) ^ 2) = q := by
  have key : triArea ((a : ℝ), (a : ℝ) ^ 2) ((b : ℝ), (b : ℝ) ^ 2) ((c : ℝ), (c : ℝ) ^ 2) =
      |((b : ℝ) - a) * ((c : ℝ) - a) * ((c : ℝ) - b)| / 2 := by
    simp only [triArea]
    rw [show ((b : ℝ) - a) * ((c : ℝ) ^ 2 - (a : ℝ) ^ 2) - ((c : ℝ) - a) * ((b : ℝ) ^ 2 - (a : ℝ) ^ 2)
        = ((b : ℝ) - a) * ((c : ℝ) - a) * ((c : ℝ) - b) by ring]
  rw [key]
  have hab' : (b : ℝ) - a ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hab.symm)
  have hac' : (c : ℝ) - a ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hac.symm)
  have hbc' : (c : ℝ) - b ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hbc.symm)
  have hprod : ((b : ℝ) - a) * ((c : ℝ) - a) * ((c : ℝ) - b) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hab' hac') hbc'
  refine ⟨(div_pos (abs_pos.mpr hprod) two_pos).ne',
    |((b : ℚ) - a) * ((c : ℚ) - a) * ((c : ℚ) - b)| / 2, ?_⟩
  push_cast <;> ring

/-- **IMO 1987 P5.** -/
theorem imo1987_p5 (n : ℕ) (hn : 3 ≤ n) :
    ∃ P : Fin n → ℝ × ℝ, Function.Injective P ∧
      (∀ i j, i ≠ j → Irrational (eDist (P i) (P j))) ∧
      (∀ i j k, i ≠ j → j ≠ k → i ≠ k →
        triArea (P i) (P j) (P k) ≠ 0 ∧ ∃ q : ℚ, triArea (P i) (P j) (P k) = q) := by
  refine ⟨fun i => (((i : ℕ) : ℝ), ((i : ℕ) : ℝ) ^ 2), ?_, ?_, ?_⟩
  · intro i j h
    simp only [Prod.mk.injEq] at h
    exact Fin.ext (by exact_mod_cast h.1)
  · intro i j hij
    have hne : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
    exact irrational_eDist hne
  · intro i j k hij hjk hik
    have h1 : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
    have h2 : (j : ℕ) ≠ (k : ℕ) := fun h => hjk (Fin.ext h)
    have h3 : (i : ℕ) ≠ (k : ℕ) := fun h => hik (Fin.ext h)
    exact triArea_facts h1 h2 h3

end Imo1987P5
