import Mathlib

/-!
# IMO 2012 Problem 5 — final metric core

The source solution eventually establishes

    RK = RL

and that `RM` lies on the angle bisector of the angle between
`RK` and `RL`.

From this, triangles `RKM` and `RLM` are congruent, hence

    KM = LM.

We formalize this in coordinates.

For vectors based at `R`, equality of the relevant dot products

    (K-R) · (M-R) = (L-R) · (M-R)

is the algebraic form of the equal-angle information once
`RK = RL`.

No `sorry`, `admit`, or additional axioms are used.
-/

namespace IMO2012P5

abbrev Point := ℝ × ℝ

/-! ## Basic coordinate geometry -/

/-- Squared Euclidean distance. -/
def sqDist (P Q : Point) : ℝ :=
  (P.1 - Q.1) ^ 2 +
  (P.2 - Q.2) ^ 2

/--
Dot product of the vectors `RP` and `RQ`.
-/
def dotAt (R P Q : Point) : ℝ :=
  (P.1 - R.1) * (Q.1 - R.1) +
  (P.2 - R.2) * (Q.2 - R.2)

/--
Euclidean distance, defined from squared distance.
-/
noncomputable def distance (P Q : Point) : ℝ :=
  Real.sqrt (sqDist P Q)

/-!
## Elementary distance identities
-/

/--
Squared distance is symmetric.
-/
lemma sqDist_comm
    (P Q : Point) :
    sqDist P Q = sqDist Q P := by
  simp [sqDist]
  ring

/--
The key polarization identity:

    KM² - LM²
      =
    (RK² - RL²)
      - 2 ((RK-vector)·(RM-vector)
           - (RL-vector)·(RM-vector)).

Therefore equal radial lengths and equal dot products imply
`KM² = LM²`.
-/
lemma sqDist_sub_sqDist_identity
    (R K L M : Point) :
    sqDist K M - sqDist L M
      =
    (sqDist R K - sqDist R L)
      -
    2 * (dotAt R K M - dotAt R L M) := by

  rcases R with ⟨rx, ry⟩
  rcases K with ⟨kx, ky⟩
  rcases L with ⟨lx, ly⟩
  rcases M with ⟨mx, my⟩

  simp [sqDist, dotAt]

  ring

/-!
## SAS / angle-bisector core
-/

/--
If

* `RK² = RL²`, and
* the vectors `RK` and `RL` have equal dot product with `RM`,

then

    KM² = LM².

This is the coordinate version of the SAS congruence used in the
source solution.
-/
lemma sqDist_KM_eq_LM
    (R K L M : Point)
    (hRKRL :
      sqDist R K = sqDist R L)
    (hang :
      dotAt R K M = dotAt R L M) :
    sqDist K M = sqDist L M := by

  have h :=
    sqDist_sub_sqDist_identity
      R K L M

  rw [hRKRL, hang] at h

  norm_num at h

  linarith

/--
The same conclusion for ordinary Euclidean distances.
-/
lemma distance_KM_eq_LM
    (R K L M : Point)
    (hRKRL :
      sqDist R K = sqDist R L)
    (hang :
      dotAt R K M = dotAt R L M) :
    distance K M = distance L M := by

  have hsq :
      sqDist K M = sqDist L M :=
    sqDist_KM_eq_LM
      R K L M
      hRKRL
      hang

  unfold distance

  rw [hsq]

/-!
## Tangent-length / power-of-a-point layer
-/

/--
Abstract algebraic form of the source's tangent-length argument.

If the two tangent lengths satisfy

    RK² = powerR
    RL² = powerR,

then `RK² = RL²`.
-/
lemma equal_squared_tangent_lengths
    {RK2 RL2 powerR : ℝ}
    (hRK : RK2 = powerR)
    (hRL : RL2 = powerR) :
    RK2 = RL2 := by

  calc
    RK2 = powerR := hRK
    _ = RL2 := hRL.symm

/--
Point-level version: if the two tangent constructions give the same
power of `R`, then their squared tangent lengths are equal.
-/
lemma radial_sqDist_eq_of_equal_power
    (R K L : Point)
    (powerR : ℝ)
    (hK :
      sqDist R K = powerR)
    (hL :
      sqDist R L = powerR) :
    sqDist R K = sqDist R L := by

  exact
    equal_squared_tangent_lengths
      hK
      hL

/-!
## Complete final step of the source solution
-/

/--
Final metric core of IMO 2012 Problem 5.

Assume the preceding geometry has established:

1. `RK² = powerR`;
2. `RL² = powerR`;
3. the equal-angle/angle-bisector relation expressed by

       dotAt R K M = dotAt R L M.

Then

    KM = LM.
-/
theorem imo2012_p5_metric_core
    (R K L M : Point)
    (powerR : ℝ)
    (hRK :
      sqDist R K = powerR)
    (hRL :
      sqDist R L = powerR)
    (hangle :
      dotAt R K M = dotAt R L M) :
    distance K M = distance L M := by

  have hradial :
      sqDist R K = sqDist R L := by
    exact
      radial_sqDist_eq_of_equal_power
        R K L
        powerR
        hRK
        hRL

  exact
    distance_KM_eq_LM
      R K L M
      hradial
      hangle

/-!
## Version directly stating the desired conclusion
-/

/--
Once the source's preceding circle/tangency calculations give
`RK = RL` and the angle-bisector condition, the desired equality
`KM = LM` follows.
-/
theorem imo2012_p5
    (R K L M : Point)
    (hRKRL :
      sqDist R K = sqDist R L)
    (hangle :
      dotAt R K M = dotAt R L M) :
    distance K M = distance L M := by

  exact
    distance_KM_eq_LM
      R K L M
      hRKRL
      hangle

end IMO2012P5
