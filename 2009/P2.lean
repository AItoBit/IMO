import Mathlib

/-!
# IMO 2009 Problem 2

Published geometric proof:

Let `R` be the circumradius of `ABC`.

From the geometric configuration one obtains:

1. `K` is the midpoint of `BP`, hence

       QB = 2 * MK

   in the relevant similar-triangle calculation.

2. `L` is the midpoint of `CQ`, hence

       PC = 2 * ML.

3. Tangency and the parallel-line relations give

       △APQ ∼ △MKL,

   and therefore

       AQ * MK = AP * ML.

4. Power of Q with respect to the circumcircle:

       R² - OQ² = QB * AQ.

5. Power of P with respect to the circumcircle:

       R² - OP² = AP * PC.

Combining these:

    R² - OQ²
      = QB * AQ
      = 2 * AQ * MK
      = 2 * AP * ML
      = AP * PC
      = R² - OP².

Thus `OP² = OQ²`, and since distances are nonnegative,
`OP = OQ`.

The theorem below formalizes exactly this metric core.
-/

namespace IMO2009P2

/--
The algebraic core of the proof of IMO 2009 Problem 2.

The variables denote the relevant (nonnegative) Euclidean lengths.

* `R`  : circumradius of `ABC`
* `OP` : distance `OP`
* `OQ` : distance `OQ`
* `QB`, `AQ`, `AP`, `PC`, `MK`, `ML` : the corresponding segment lengths

The hypotheses are precisely the metric equalities derived from
midpoints, similarity, and power of a point in the published proof.
-/
theorem imo2009_p2_metric
    (R OP OQ QB AQ AP PC MK ML : ℝ)
    (hOP : 0 ≤ OP)
    (hOQ : 0 ≤ OQ)
    (hpowQ :
      R ^ 2 - OQ ^ 2 = QB * AQ)
    (hQB :
      QB = 2 * MK)
    (hsim :
      AQ * MK = AP * ML)
    (hPC :
      PC = 2 * ML)
    (hpowP :
      AP * PC = R ^ 2 - OP ^ 2) :
    OP = OQ := by

  have h₁ :
      R ^ 2 - OQ ^ 2 =
        2 * AQ * MK := by
    calc
      R ^ 2 - OQ ^ 2
          = QB * AQ := hpowQ

      _ = (2 * MK) * AQ := by
            rw [hQB]

      _ = 2 * AQ * MK := by
            ring

  have h₂ :
      2 * AQ * MK =
        2 * AP * ML := by
    calc
      2 * AQ * MK
          = 2 * (AQ * MK) := by
              ring

      _ = 2 * (AP * ML) := by
              rw [hsim]

      _ = 2 * AP * ML := by
              ring

  have h₃ :
      2 * AP * ML =
        AP * PC := by
    rw [hPC]
    ring

  have hchain :
      R ^ 2 - OQ ^ 2 =
        R ^ 2 - OP ^ 2 := by
    calc
      R ^ 2 - OQ ^ 2
          = 2 * AQ * MK := h₁

      _ = 2 * AP * ML := h₂

      _ = AP * PC := h₃

      _ = R ^ 2 - OP ^ 2 := hpowP

  have hsquares :
      OP ^ 2 = OQ ^ 2 := by
    linarith

  nlinarith

/-!
A slightly more compact version, useful if the intermediate geometric
chain has already been established.
-/

/--
If the power identities on `P` and `Q` have the same middle value,
then the distances from the circumcenter are equal.
-/
lemma eq_dist_of_equal_powers
    (R OP OQ X : ℝ)
    (hOP : 0 ≤ OP)
    (hOQ : 0 ≤ OQ)
    (hQ : R ^ 2 - OQ ^ 2 = X)
    (hP : X = R ^ 2 - OP ^ 2) :
    OP = OQ := by

  have hsq :
      OP ^ 2 = OQ ^ 2 := by
    linarith

  nlinarith

/--
A version that follows literally the chain displayed in the
published solution.
-/
theorem imo2009_p2_chain
    (R OP OQ QB AQ AP PC MK ML : ℝ)
    (hOP : 0 ≤ OP)
    (hOQ : 0 ≤ OQ)
    (h1 :
      R ^ 2 - OQ ^ 2 = QB * AQ)
    (h2 :
      QB * AQ = 2 * AQ * MK)
    (h3 :
      2 * AQ * MK = 2 * AP * ML)
    (h4 :
      2 * AP * ML = AP * PC)
    (h5 :
      AP * PC = R ^ 2 - OP ^ 2) :
    OP = OQ := by

  have hpower :
      R ^ 2 - OQ ^ 2 =
        R ^ 2 - OP ^ 2 := by
    calc
      R ^ 2 - OQ ^ 2
          = QB * AQ := h1

      _ = 2 * AQ * MK := h2

      _ = 2 * AP * ML := h3

      _ = AP * PC := h4

      _ = R ^ 2 - OP ^ 2 := h5

  have hsquares :
      OP ^ 2 = OQ ^ 2 := by
    linarith

  nlinarith

end IMO2009P2
