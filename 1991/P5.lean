import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push

/-!
# IMO 1991, Problem 5

The predicate `angleLE30 P A B` is an algebraic encoding of
`∠PAB ≤ 30°`.  For an interior point on the consistently oriented side of
the three edges, the oriented determinant is the sine numerator and the dot
product is the cosine numerator, so the comparison is exactly

  `sqrt 3 * sin(∠PAB) ≤ cos(∠PAB)`.
-/

namespace IMO1991P5

abbrev Point := ℝ × ℝ

def orient (A B P : Point) : ℝ :=
  (B.1 - A.1) * (P.2 - A.2) - (B.2 - A.2) * (P.1 - A.1)

def dotAt (A B P : Point) : ℝ :=
  (B.1 - A.1) * (P.1 - A.1) + (B.2 - A.2) * (P.2 - A.2)

/-- Algebraic form of `∠PAB ≤ 30°`. -/
def angleLE30 (P A B : Point) : Prop :=
  Real.sqrt 3 * |orient A B P| ≤ dotAt A B P

/-- Strict barycentric interior, allowing either orientation of the vertices. -/
def StrictlyInside (P A B C : Point) : Prop :=
  (0 < orient A B P ∧ 0 < orient B C P ∧ 0 < orient C A P) ∨
  (orient A B P < 0 ∧ orient B C P < 0 ∧ orient C A P < 0)

theorem imo_1991_p5 (A B C P : Point) (hP : StrictlyInside P A B C) :
    angleLE30 P A B ∨ angleLE30 P B C ∨ angleLE30 P C A := by
  rcases A with ⟨ax, ay⟩
  rcases B with ⟨bx, bY⟩
  rcases C with ⟨cx, cy⟩
  rcases P with ⟨px, py⟩
  let s : ℝ := Real.sqrt 3
  have hs0 : 0 ≤ s := Real.sqrt_nonneg 3
  have hs2 : s ^ 2 = 3 := by
    dsimp [s]
    norm_num

  have hweitz_pos :
      2 * s * ((bx - ax) * (cy - ay) - (bY - ay) * (cx - ax)) ≤
        ((bx - ax) ^ 2 + (bY - ay) ^ 2) +
        ((cx - bx) ^ 2 + (cy - bY) ^ 2) +
        ((ax - cx) ^ 2 + (ay - cy) ^ 2) := by
    have hsq₁ :
        0 ≤ (2 * (bx - ax) - (cx - ax) - s * (cy - ay)) ^ 2 := sq_nonneg _
    have hsq₂ :
        0 ≤ (2 * (bY - ay) + s * (cx - ax) - (cy - ay)) ^ 2 := sq_nonneg _
    nlinarith

  have hweitz_neg :
      -(2 * s * ((bx - ax) * (cy - ay) - (bY - ay) * (cx - ax))) ≤
        ((bx - ax) ^ 2 + (bY - ay) ^ 2) +
        ((cx - bx) ^ 2 + (cy - bY) ^ 2) +
        ((ax - cx) ^ 2 + (ay - cy) ^ 2) := by
    have hsq₁ :
        0 ≤ (2 * (bx - ax) - (cx - ax) + s * (cy - ay)) ^ 2 := sq_nonneg _
    have hsq₂ :
        0 ≤ (2 * (bY - ay) - s * (cx - ax) - (cy - ay)) ^ 2 := sq_nonneg _
    nlinarith

  rcases hP with hccw | hcw
  · rcases hccw with ⟨hAB, hBC, hCA⟩
    by_contra h
    push_neg at h
    rcases h with ⟨h₁, h₂, h₃⟩
    unfold angleLE30 at h₁ h₂ h₃
    simp only [not_le] at h₁ h₂ h₃
    change s * |orient (ax, ay) (bx, bY) (px, py)| >
        dotAt (ax, ay) (bx, bY) (px, py) at h₁
    change s * |orient (bx, bY) (cx, cy) (px, py)| >
        dotAt (bx, bY) (cx, cy) (px, py) at h₂
    change s * |orient (cx, cy) (ax, ay) (px, py)| >
        dotAt (cx, cy) (ax, ay) (px, py) at h₃
    rw [abs_of_pos hAB] at h₁
    rw [abs_of_pos hBC] at h₂
    rw [abs_of_pos hCA] at h₃
    unfold orient dotAt at h₁ h₂ h₃
    nlinarith
  · rcases hcw with ⟨hAB, hBC, hCA⟩
    by_contra h
    push_neg at h
    rcases h with ⟨h₁, h₂, h₃⟩
    unfold angleLE30 at h₁ h₂ h₃
    simp only [not_le] at h₁ h₂ h₃
    change s * |orient (ax, ay) (bx, bY) (px, py)| >
        dotAt (ax, ay) (bx, bY) (px, py) at h₁
    change s * |orient (bx, bY) (cx, cy) (px, py)| >
        dotAt (bx, bY) (cx, cy) (px, py) at h₂
    change s * |orient (cx, cy) (ax, ay) (px, py)| >
        dotAt (cx, cy) (ax, ay) (px, py) at h₃
    rw [abs_of_neg hAB] at h₁
    rw [abs_of_neg hBC] at h₂
    rw [abs_of_neg hCA] at h₃
    unfold orient dotAt at h₁ h₂ h₃
    nlinarith

end IMO1991P5
