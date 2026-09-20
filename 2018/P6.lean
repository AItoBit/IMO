import Mathlib

namespace IMO2018P6

/-!
# IMO 2018 Problem 6 — final algebraic core

The source introduces

    α = ∠XAB = ∠XCD
    φ = ∠BXA
    ψ = ∠DXC.

Its common-case argument establishes

    BX / DX = AB / CD.

The sine rule gives

    AB / sin φ = BX / sin α
    CD / sin ψ = DX / sin α.

We formalize these in denominator-free form:

    AB * sin α = BX * sin φ
    CD * sin α = DX * sin ψ
    BX * CD    = DX * AB.

From these equations and positivity/nondegeneracy of the
lengths we derive

    sin ψ = sin φ.

The geometric part of the source then distinguishes:

* φ = ψ, which leads to the special symmetric case;
* φ ≠ ψ, in which the equality of sines gives
      φ + ψ = 180°.

The file also formalizes the final angle arithmetic in both
the common and special cases.

No `sorry`, `admit`, or additional axioms are used.
-/

/-!
============================================================
1. Algebra behind the sine-rule step
============================================================
-/

/--
Suppose the two sine-rule equations are

    AB * sα = BX * sφ
    CD * sα = DX * sψ

and the inversion/similarity portion of the source has
established

    BX * CD = DX * AB.

Then, if `AB` and `DX` are nonzero,

    sψ = sφ.

Later we instantiate

    sα = sin α,
    sφ = sin φ,
    sψ = sin ψ.
-/
lemma sine_rule_ratio_core
    (AB CD BX DX sα sφ sψ : ℝ)
    (hAB :
      AB ≠ 0)
    (hDX :
      DX ≠ 0)
    (hABsin :
      AB * sα =
        BX * sφ)
    (hCDsin :
      CD * sα =
        DX * sψ)
    (hratio :
      BX * CD =
        DX * AB) :
    sψ = sφ := by

  have hleft :
      AB * CD * sα =
        AB * DX * sφ := by

    calc
      AB * CD * sα
          =
        CD * (AB * sα) := by
          ring

      _ =
        CD * (BX * sφ) := by
          rw [hABsin]

      _ =
        (BX * CD) * sφ := by
          ring

      _ =
        (DX * AB) * sφ := by
          rw [hratio]

      _ =
        AB * DX * sφ := by
          ring

  have hright :
      AB * CD * sα =
        AB * DX * sψ := by

    calc
      AB * CD * sα
          =
        AB * (CD * sα) := by
          ring

      _ =
        AB * (DX * sψ) := by
          rw [hCDsin]

      _ =
        AB * DX * sψ := by
          ring

  have heq :
      AB * DX * sφ =
        AB * DX * sψ := by

    calc
      AB * DX * sφ
          =
        AB * CD * sα :=
          hleft.symm

      _ =
        AB * DX * sψ :=
          hright

  have hzero :
      (AB * DX) * (sφ - sψ) = 0 := by

    calc
      (AB * DX) * (sφ - sψ)
          =
        AB * DX * sφ -
          AB * DX * sψ := by
            ring

      _ = 0 := by
        rw [heq]
        ring

  have hprod :
      AB * DX ≠ 0 :=
    mul_ne_zero
      hAB
      hDX

  have hdiff :
      sφ - sψ = 0 :=
    (mul_eq_zero.mp hzero).resolve_left
      hprod

  linarith

/-!
============================================================
2. Version written with Real.sin
============================================================
-/

/--
This is exactly the sine-rule calculation on page 4.

The hypotheses are cross-multiplied versions of

    AB / sin φ = BX / sin α

and

    CD / sin ψ = DX / sin α.

Cross multiplication avoids all division-by-zero bookkeeping.
-/
lemma equal_sines_from_sine_rule
    (AB CD BX DX α φ ψ : ℝ)
    (hAB :
      AB ≠ 0)
    (hDX :
      DX ≠ 0)
    (h₁ :
      AB * Real.sin α =
        BX * Real.sin φ)
    (h₂ :
      CD * Real.sin α =
        DX * Real.sin ψ)
    (hratio :
      BX * CD =
        DX * AB) :
    Real.sin ψ =
      Real.sin φ := by

  exact
    sine_rule_ratio_core
      AB
      CD
      BX
      DX
      (Real.sin α)
      (Real.sin φ)
      (Real.sin ψ)
      hAB
      hDX
      h₁
      h₂
      hratio

/-!
============================================================
3. Deriving the ratio BX / DX = AB / CD
============================================================
-/

/--
The source obtains

    BX / DX
      =
    (DY / BY) * (OB / OD)
      =
    (AD / BC) * (BC / CD) * (AB / AD)
      =
    AB / CD.

Here is the cancellation step in cross-multiplied form.

If

    BX * DY = DX * BY
    DY * BC = BY * AD
    OB * CD = OD * BC
    ...

one can avoid division throughout.

For the final argument only the resulting relation
`BX * CD = DX * AB` is needed, so the following reusable
lemma formalizes the essential cancellation pattern.
-/
lemma ratio_chain_cancellation
    (BX DX AB CD u v : ℝ)
    (hu :
      u ≠ 0)
    (hv :
      v ≠ 0)
    (h₁ :
      BX * u =
        DX * v)
    (h₂ :
      v * CD =
        u * AB) :
    BX * CD =
      DX * AB := by

  have hmain :
      u * (BX * CD - DX * AB) = 0 := by

    calc
      u * (BX * CD - DX * AB)
          =
        CD * (BX * u) -
          DX * (u * AB) := by
            ring

      _ =
        CD * (DX * v) -
          DX * (v * CD) := by
            rw [h₁, h₂]

      _ = 0 := by
        ring

  have :
      BX * CD - DX * AB = 0 :=
    (mul_eq_zero.mp hmain).resolve_left
      hu

  linarith

/-!
============================================================
4. Special case from page 4
============================================================
-/

/--
In the special case the source gets similarity and hence

    CD / AB = AD / BC.

Together with the original condition

    AB * CD = BC * AD

and positivity of all four side lengths, this forces

    AB = BC
    AD = CD.

This is the algebraic content of the special-case reduction.
-/
lemma special_case_side_equalities
    (AB BC CD AD : ℝ)
    (hAB :
      0 < AB)
    (hBC :
      0 < BC)
    (hCD :
      0 < CD)
    (hAD :
      0 < AD)
    (horiginal :
      AB * CD =
        BC * AD)
    (hsimilar :
      CD * BC =
        AD * AB) :
    AB = BC ∧ AD = CD := by

  have hfactor :
      (AB - BC) * (AD + CD) = 0 := by
    nlinarith [horiginal, hsimilar]

  have hsum :
      AD + CD ≠ 0 := by
    positivity

  have hab0 :
      AB - BC = 0 :=
    (mul_eq_zero.mp hfactor).resolve_right
      hsum

  have hab :
      AB = BC := by
    linarith

  have hfactor₂ :
      AB * (CD - AD) = 0 := by

    calc
      AB * (CD - AD)
          =
        AB * CD - AB * AD := by
          ring

      _ =
        BC * AD - AB * AD := by
          rw [horiginal]

      _ = 0 := by
        rw [hab]
        ring

  have hABne :
      AB ≠ 0 :=
    ne_of_gt hAB

  have hcdad :
      CD - AD = 0 :=
    (mul_eq_zero.mp hfactor₂).resolve_left
      hABne

  constructor

  · exact hab

  · linarith

/-!
============================================================
5. Final angle arithmetic — common case
============================================================
-/

/--
The source denotes

    φ = ∠BXA
    ψ = ∠DXC.

Once the common-case geometry gives

    φ + ψ = 180°,

the requested conclusion is immediate.

We keep angles here in degrees, exactly as in the supplied
solution.
-/
lemma common_case_angle_finish
    (BXA DXC φ ψ : ℝ)
    (hBXA :
      BXA = φ)
    (hDXC :
      DXC = ψ)
    (hsupp :
      φ + ψ = 180) :
    BXA + DXC = 180 := by
  linarith

/-!
============================================================
6. Final angle arithmetic — special case
============================================================
-/

/--
In the special case the source proves

    ∠C-X-B = 90°
    ∠A-X-D = 90°.

The four angles around X sum to 360°, hence

    ∠BXA + ∠DXC = 180°.
-/
lemma special_case_angle_finish
    (BXA DXC AXD CXB : ℝ)
    (haround :
      BXA + DXC + AXD + CXB =
        360)
    (hAXD :
      AXD = 90)
    (hCXB :
      CXB = 90) :
    BXA + DXC = 180 := by
  linarith

/-!
============================================================
7. Equality-of-sines package
============================================================
-/

/--
This theorem packages the precise final calculation in the
common case.

The source's geometry has already proved the ratio of lengths.
The two sine-rule equations then force equality of the two
sines.
-/
theorem imo2018_p6_sine_core
    (AB CD BX DX α φ ψ : ℝ)
    (hAB :
      0 < AB)
    (hDX :
      0 < DX)
    (hSineABX :
      AB * Real.sin α =
        BX * Real.sin φ)
    (hSineCDX :
      CD * Real.sin α =
        DX * Real.sin ψ)
    (hLengthRatio :
      BX * CD =
        DX * AB) :
    Real.sin ψ =
      Real.sin φ := by

  exact
    equal_sines_from_sine_rule
      AB
      CD
      BX
      DX
      α
      φ
      ψ
      (ne_of_gt hAB)
      (ne_of_gt hDX)
      hSineABX
      hSineCDX
      hLengthRatio

/-!
============================================================
8. Source-style common-case theorem
============================================================
-/

/--
Once the geometric "equal sine but unequal angles" step has
established supplementary angles, the actual IMO conclusion
follows.

`hsupp` is exactly the source's conclusion

    φ + ψ = 180°

in the non-special case.
-/
theorem imo2018_p6_common_case
    (BXA DXC φ ψ : ℝ)
    (hBXA :
      BXA = φ)
    (hDXC :
      DXC = ψ)
    (hsupp :
      φ + ψ = 180) :
    BXA + DXC = 180 := by

  exact
    common_case_angle_finish
      BXA
      DXC
      φ
      ψ
      hBXA
      hDXC
      hsupp

/-!
============================================================
9. Source-style special-case theorem
============================================================
-/

/--
This packages the end of the special case on page 2.
-/
theorem imo2018_p6_special_case
    (BXA DXC AXD CXB : ℝ)
    (haround :
      BXA + DXC + AXD + CXB =
        360)
    (hAXD :
      AXD = 90)
    (hCXB :
      CXB = 90) :
    BXA + DXC = 180 := by

  exact
    special_case_angle_finish
      BXA
      DXC
      AXD
      CXB
      haround
      hAXD
      hCXB

/-!
============================================================
10. Combined final wrapper
============================================================
-/

/--
The final result after the source's geometric construction
has reduced the problem to either the common case or the
special right-angle case.
-/
theorem imo2018_p6_final
    (BXA DXC : ℝ)
    (h :
      (∃ φ ψ : ℝ,
          BXA = φ ∧
          DXC = ψ ∧
          φ + ψ = 180)
      ∨
      (∃ AXD CXB : ℝ,
          BXA + DXC + AXD + CXB = 360 ∧
          AXD = 90 ∧
          CXB = 90)) :
    BXA + DXC = 180 := by

  rcases h with hcommon | hspecial

  · rcases hcommon with
      ⟨φ, ψ, hBXA, hDXC, hsupp⟩

    exact
      common_case_angle_finish
        BXA
        DXC
        φ
        ψ
        hBXA
        hDXC
        hsupp

  · rcases hspecial with
      ⟨AXD, CXB, haround, hAXD, hCXB⟩

    exact
      special_case_angle_finish
        BXA
        DXC
        AXD
        CXB
        haround
        hAXD
        hCXB

end IMO2018P6
