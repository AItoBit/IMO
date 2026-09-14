import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

noncomputable section

namespace IMO1998P1

abbrev Point := ℝ × ℝ

def sqDist (U V : Point) : ℝ :=
  (U.1 - V.1)^2 + (U.2 - V.2)^2

def area (U V W : Point) : ℝ :=
  |(V.1 - U.1) * (W.2 - U.2) -
    (V.2 - U.2) * (W.1 - U.1)| / 2

def Cyclic (A B C D : Point) : Prop :=
  ∃ O : Point, ∃ r2 : ℝ, 0 < r2 ∧
    sqDist A O = r2 ∧ sqDist B O = r2 ∧
    sqDist C O = r2 ∧ sqDist D O = r2

/-
The supplied PDF is IMO 1998 Problem 1 (not 1988).

Coordinate formulation: put the diagonal intersection at the origin and
choose the perpendicular diagonals as coordinate axes. Then
  A = (a,0), B = (0,b), C = (-c,0), D = (0,-d), P = (x,y),
with a,b,c,d positive. This file proves the theorem in those coordinates;
it does not formalize the change of coordinates from an abstract Euclidean plane.

Inside gives the four strict half-plane conditions for interior membership.
a*d-b*c is the determinant of the direction vectors of AB and CD.
The two sqDist equalities express membership in their perpendicular bisectors.
Cyclic means membership of all four points in a circle of positive radius
squared; area is the ordinary unsigned triangle area.
-/

/-- With the diagonal intersection as origin and the diagonals as axes,
    the vertices are (a,0), (0,b), (-c,0), (0,-d). -/
theorem cyclic_iff (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    Cyclic (a,0) (0,b) (-c,0) (0,-d) ↔ a*c = b*d := by
  constructor
  · rintro ⟨⟨u,v⟩, r, _, hA, hB, hC, hD⟩
    dsimp [sqDist] at hA hB hC hD
    have hu : 2*u = a-c := by
      have h : (a+c) * (2*u-a+c) = 0 := by nlinarith [hA, hC]
      have hn : a+c ≠ 0 := ne_of_gt (add_pos ha hc)
      have := (mul_eq_zero.mp h).resolve_left hn
      linarith
    have hBD : (b+d) * (2*v-b+d) = 0 := by nlinarith [hB, hD]
    have hv : 2*v = b-d := by
      have hn : b+d ≠ 0 := ne_of_gt (add_pos hb hd)
      have := (mul_eq_zero.mp hBD).resolve_left hn
      linarith
    nlinarith [hA, hB]
  · intro h
    refine ⟨((a-c)/2, (b-d)/2),
      sqDist (a,0) ((a-c)/2, (b-d)/2), ?_, rfl, ?_, ?_, ?_⟩
    · dsimp [sqDist]
      have : 0 < a - (a-c)/2 := by linarith
      nlinarith [sq_pos_of_pos this, sq_nonneg ((0:ℝ)-(b-d)/2)]
    all_goals dsimp [sqDist]; nlinarith

/-- P is strictly inside the quadrilateral, expressed by its four side inequalities. -/
def Inside (a b c d x y : ℝ) : Prop :=
  0 < a*b - b*x - a*y ∧
  0 < b*c + b*x - c*y ∧
  0 < c*d + d*x + c*y ∧
  0 < a*d - d*x + a*y

/-- IMO 1998, Problem 1, in coordinates along the perpendicular diagonals. -/
theorem imo1998_p1
    (a b c d x y : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hnotparallel : a*d - b*c ≠ 0)
    (hinside : Inside a b c d x y)
    (hAB : sqDist (a,0) (x,y) = sqDist (0,b) (x,y))
    (hCD : sqDist (-c,0) (x,y) = sqDist (0,-d) (x,y)) :
    Cyclic (a,0) (0,b) (-c,0) (0,-d) ↔
      area (a,0) (0,b) (x,y) = area (-c,0) (0,-d) (x,y) := by
  have h1 : 2*a*x - 2*b*y - a^2 + b^2 = 0 := by
    dsimp [sqDist] at hAB
    nlinarith
  have h2 : -2*c*x + 2*d*y - c^2 + d^2 = 0 := by
    dsimp [sqDist] at hCD
    nlinarith
  have harea :
      area (a,0) (0,b) (x,y) = area (-c,0) (0,-d) (x,y) ↔
      (b+d)*x + (a+c)*y - a*b + c*d = 0 := by
    rcases hinside with ⟨hpos1, _, hpos2, _⟩
    have e1 : (0-a)* (y-0) - (b-0)*(x-a) = a*b-b*x-a*y := by ring
    have e2 : (0- -c)*(y-0) - (-d-0)*(x- -c) = c*d+d*x+c*y := by ring
    change |(0-a)*(y-0)-(b-0)*(x-a)|/2 =
      |(0- -c)*(y-0)-(-d-0)*(x- -c)|/2 ↔ _
    rw [e1, e2, abs_of_pos hpos1, abs_of_pos hpos2]
    constructor <;> intro h <;> linarith
  rw [cyclic_iff a b c d ha hb hc hd, harea]
  have hid :
      (a*c-b*d)*((a+c)^2+(b+d)^2) =
      2*(a*d-b*c)*((b+d)*x+(a+c)*y-a*b+c*d) := by
    linear_combination
      -(d*(b+d)+c*(a+c))*h1 - (b*(b+d)+a*(a+c))*h2
  constructor
  · intro h
    have hz : 2*(a*d-b*c)*((b+d)*x+(a+c)*y-a*b+c*d) = 0 := by
      rw [h] at hid
      nlinarith [hid]
    exact (mul_eq_zero.mp hz).resolve_left (mul_ne_zero (by norm_num) hnotparallel)
  · intro h
    rw [h, mul_zero] at hid
    have hp : 0 < (a+c)^2+(b+d)^2 := by
      have hs := sq_pos_of_pos (add_pos ha hc)
      nlinarith [sq_nonneg (b+d)]
    have hz := (mul_eq_zero.mp hid).resolve_right (ne_of_gt hp)
    linarith

end IMO1998P1
