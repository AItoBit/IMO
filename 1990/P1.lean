import Mathlib

/-!
# IMO 1990, Problem 1 — metric core

Chords `AB` and `CD` of a circle meet at an interior point `E`. `M` is an interior point of
`EB`. The circle through `D`, `E`, `M` has tangent at `E` meeting `BC` at `F` and `AC` at `G`.
Given `AM/AB = t`, find `EG/EF`.

Answer: `EG/EF = t/(1-t)`.

## What is formalized here

Mathlib has no API for the circle through three given points, for the tangent line at a point of
a circle, or for the intersection of that tangent with a side line, so the synthetic part cannot
be carried out. What is formalized is everything AoPS "Solution 1" does once the two
similarities are in hand.

Solution 1 establishes, by angle chasing:

* `△CEG ∼ △BMD`, hence `MB/EC = MD/EG`;
* `△CEF ∼ △AMD`, hence `MA/EC = MD/EF`.

Dividing one by the other gives `EG/EF = MA/MB`, and `M` lying between `A` and `B` with
`AM/AB = t` gives `MA/MB = t/(1-t)`.

Proved below  :

* `ratio_of_sbtw`   : `M` strictly between `A` and `B` with `AM/AB = t` forces `0 < t < 1` and
  `MA/MB = t/(1-t)`;
* `ratio_of_similar`: the two similarity relations give `EG/EF = MA/MB`;
* `imo1990_p1_core` : the two combined, stated for points of the Euclidean plane.
-/

namespace Imo1990P1

/-- If `M` lies strictly between `A` and `B` and `AM/AB = t`, then `0 < t < 1` and
`MA/MB = t/(1-t)`. -/
theorem ratio_of_sbtw {A M B : EuclideanSpace ℝ (Fin 2)} {t : ℝ}
    (h : Sbtw ℝ A M B) (ht : dist A M / dist A B = t) :
    0 < t ∧ t < 1 ∧ dist M A / dist M B = t / (1 - t) := by
  have hsum : dist A M + dist M B = dist A B := h.wbtw.dist_add_dist
  have hAM : 0 < dist A M := dist_pos.2 h.left_ne
  have hMB : 0 < dist M B := dist_pos.2 h.ne_right
  have hAB : 0 < dist A B := by linarith
  have hABne : dist A B ≠ 0 := hAB.ne'
  have hMBne : dist M B ≠ 0 := hMB.ne'
  have ht' : t = dist A M / dist A B := ht.symm
  have htpos : 0 < t := by rw [ht']; positivity
  have htlt : t < 1 := by
    rw [ht', div_lt_one hAB]
    linarith
  refine ⟨htpos, htlt, ?_⟩
  have h1t : 1 - t = dist M B / dist A B := by
    rw [ht']
    field_simp
    linarith
  rw [h1t, ht', dist_comm M A]
  field_simp

/-- The two similarity relations of Solution 1 give `EG/EF = MA/MB`. -/
theorem ratio_of_similar {MA MB EC MD EG EF : ℝ}
    (hMB : 0 < MB) (hEC : 0 < EC) (hEG : 0 < EG) (hEF : 0 < EF)
    (h₁ : MB / EC = MD / EG) (h₂ : MA / EC = MD / EF) :
    EG / EF = MA / MB := by
  have e₁ : MB * EG = MD * EC := (div_eq_div_iff hEC.ne' hEG.ne').1 h₁
  have e₂ : MA * EF = MD * EC := (div_eq_div_iff hEC.ne' hEF.ne').1 h₂
  rw [div_eq_div_iff hEF.ne' hMB.ne']
  linear_combination e₁ - e₂

/-- **Metric core of IMO 1990 P1.** With the two similarities of Solution 1 as hypotheses,
`EG/EF = t/(1-t)`. -/
theorem imo1990_p1_core {A B C D E F G M : EuclideanSpace ℝ (Fin 2)} {t : ℝ}
    (hM : Sbtw ℝ A M B) (ht : dist A M / dist A B = t)
    (hEC : 0 < dist E C) (hEG : 0 < dist E G) (hEF : 0 < dist E F)
    -- `△CEG ∼ △BMD`
    (h₁ : dist M B / dist E C = dist M D / dist E G)
    -- `△CEF ∼ △AMD`
    (h₂ : dist M A / dist E C = dist M D / dist E F) :
    dist E G / dist E F = t / (1 - t) := by
  obtain ⟨-, -, hratio⟩ := ratio_of_sbtw hM ht
  have hMB : 0 < dist M B := dist_pos.2 hM.ne_right
  rw [ratio_of_similar hMB hEC hEG hEF h₁ h₂]
  exact hratio

end Imo1990P1
