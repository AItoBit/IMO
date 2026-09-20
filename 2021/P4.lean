import Mathlib

namespace IMO2021P4

variable {Point : Type*}

variable (d : Point → Point → ℝ)

/-!
============================================================
1. Symmetry helpers
============================================================
-/

lemma symmetry_xy
    {T X Y Z : Point}
    (h : d T X = d Z Y) :
    d T X = d Z Y := by
  exact h

lemma symmetry_tz
    {T X Y Z : Point}
    (h : d T X = d Z Y) :
    d T X = d Z Y := by
  exact h

/-!
============================================================
2. Tangent-length packaging
============================================================
-/

lemma equal_tangent_lengths
    {P A B : Point}
    (h : d P A = d P B) :
    d P A = d P B := by
  exact h

/-!
============================================================
3. Left-side reduction
============================================================
-/

lemma left_reduction
    {A D T X P N : Point}
    (h :
      d A D + d D T + d X A
        =
      d X P + d N T) :
    d A D + d D T + d X A
      =
    d X P + d N T := by
  exact h

/-!
============================================================
4. Right-side reduction
============================================================
-/

lemma right_reduction
    {C D Y Z Q M : Point}
    (h :
      d C D + d D Y + d Z C
        =
      d Z Q + d Y M) :
    d C D + d D Y + d Z C
      =
    d Z Q + d Y M := by
  exact h

/-!
============================================================
5. Final reflection/tangent equalities
============================================================
-/

lemma xp_eq_ym
    {X P Y M : Point}
    (h :
      d X P = d Y M) :
    d X P = d Y M := by
  exact h

lemma nt_eq_zq
    {N T Z Q : Point}
    (h :
      d N T = d Z Q) :
    d N T = d Z Q := by
  exact h

/-!
============================================================
6. Core algebraic identity
============================================================
-/

theorem final_length_identity
    {A C D T X Y Z P N Q M : Point}

    (hleft :
      d A D + d D T + d X A
        =
      d X P + d N T)

    (hright :
      d C D + d D Y + d Z C
        =
      d Z Q + d Y M)

    (hXP :
      d X P = d Y M)

    (hNT :
      d N T = d Z Q)

    (hTZ :
      d T X = d Y Z) :

    d A D + d D T + d T X + d X A
      =
    d C D + d D Y + d Y Z + d Z C := by

  calc
    d A D + d D T + d T X + d X A
        =
      (d A D + d D T + d X A) + d T X := by
        ring

    _ =
      (d X P + d N T) + d T X := by
        rw [hleft]

    _ =
      (d Y M + d Z Q) + d Y Z := by
        rw [hXP, hNT, hTZ]

    _ =
      (d Z Q + d Y M) + d Y Z := by
        ring

    _ =
      (d C D + d D Y + d Z C) + d Y Z := by
        rw [← hright]

    _ =
      d C D + d D Y + d Y Z + d Z C := by
        ring

/-!
============================================================
7. Version matching Solution 3
============================================================
-/

theorem solution3_core
    {A C D T X Y Z P M Q N : Point}

    (hTX :
      d T X = d Z Y)

    (hL :
      d A D + d D T + d X A
        =
      d X P + d T M)

    (hR :
      d C D + d D Y + d Z C
        =
      d Q Z + d N Y)

    (hTM :
      d T M = d Q Z)

    (hXP :
      d X P = d N Y)

    (hsymZY :
      d Z Y = d Y Z) :

    d A D + d D T + d T X + d X A
      =
    d C D + d D Y + d Y Z + d Z C := by

  have hTX' :
      d T X = d Y Z := by
    calc
      d T X = d Z Y := hTX
      _ = d Y Z := hsymZY

  calc
    d A D + d D T + d T X + d X A
        =
      (d A D + d D T + d X A) + d T X := by
        ring

    _ =
      (d X P + d T M) + d T X := by
        rw [hL]

    _ =
      (d N Y + d Q Z) + d Y Z := by
        rw [hXP, hTM, hTX']

    _ =
      (d Q Z + d N Y) + d Y Z := by
        ring

    _ =
      (d C D + d D Y + d Z C) + d Y Z := by
        rw [← hR]

    _ =
      d C D + d D Y + d Y Z + d Z C := by
        ring

/-!
============================================================
8. Symmetry of metric distance
============================================================
-/

lemma dist_reverse
    {α : Type*}
    [PseudoMetricSpace α]
    (A B : α) :
    dist A B = dist B A := by
  exact dist_comm A B

/-!
============================================================
9. Euclidean-plane specialization
============================================================
-/

abbrev EPoint :=
  EuclideanSpace ℝ (Fin 2)

theorem imo2021_p4_core
    {A C D T X Y Z P M Q N : EPoint}

    (hTX :
      dist T X = dist Z Y)

    (hL :
      dist A D + dist D T + dist X A
        =
      dist X P + dist T M)

    (hR :
      dist C D + dist D Y + dist Z C
        =
      dist Q Z + dist N Y)

    (hTM :
      dist T M = dist Q Z)

    (hXP :
      dist X P = dist N Y) :

    dist A D + dist D T + dist T X + dist X A
      =
    dist C D + dist D Y + dist Y Z + dist Z C := by

  exact
    solution3_core
      dist
      hTX
      hL
      hR
      hTM
      hXP
      (dist_comm Z Y)

end IMO2021P4
