import Mathlib

/-!
# IMO 2011 Problem 5

Let `f : ℤ → ℤ` be positive-valued and suppose that

    f (m - n) ∣ f m - f n

for all integers `m,n`.

Prove that whenever

    f m ≤ f n,

we have

    f m ∣ f n.

The original problem has codomain the positive integers.  We model this
as an integer-valued function together with

    0 < f x

for every `x`.

No `sorry`, `admit`, or additional axioms are used.
-/

namespace IMO2011P5

/-!
## A small arithmetic lemma

Suppose

    0 < a < b
    0 < c < b

and

    b ∣ a - c.

Since `a-c` lies strictly between `-b` and `b`, the only multiple
of `b` it can be is zero.  Hence `a = c`.
-/

lemma eq_of_dvd_sub_of_lt
    {a b c : ℤ}
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (hab : a < b)
    (hcb : c < b)
    (hdiv : b ∣ a - c) :
    a = c := by

  rcases hdiv with ⟨q, hq⟩

  rcases lt_trichotomy q 0 with hqneg | hqzero | hqpos

  /- q < 0 -/
  · have hqle :
        q ≤ -1 := by
      omega

    have hmul :
        b * q ≤ b * (-1) := by
      exact
        mul_le_mul_of_nonneg_left
          hqle
          (le_of_lt hb)

    have hlower :
        -b < a - c := by
      linarith

    have hupper :
        a - c ≤ -b := by
      calc
        a - c = b * q := hq
        _ ≤ b * (-1) := hmul
        _ = -b := by ring

    linarith

  /- q = 0 -/
  · rw [hqzero] at hq
    simp at hq
    linarith

  /- q > 0 -/
  · have hqge :
        1 ≤ q := by
      omega

    have hmul :
        b ≤ b * q := by
      have h :=
        mul_le_mul_of_nonneg_left
          hqge
          (le_of_lt hb)

      simpa using h

    have hupper :
        a - c < b := by
      linarith

    have hlower :
        b ≤ a - c := by
      calc
        b ≤ b * q := hmul
        _ = a - c := hq.symm

    linarith

/-!
## Main theorem
-/

/--
**IMO 2011 Problem 5.**

If

    f(m-n) ∣ f(m)-f(n)

for all integers `m,n`, and all values of `f` are positive, then

    f(m) ≤ f(n)  →  f(m) ∣ f(n).
-/
theorem imo2011_p5
    (f : ℤ → ℤ)
    (hpos :
      ∀ x : ℤ,
        0 < f x)
    (hdiv :
      ∀ m n : ℤ,
        f (m - n) ∣ f m - f n) :
    ∀ m n : ℤ,
      f m ≤ f n →
      f m ∣ f n := by

  intro m n hmn

  /-
  If f(m)=f(n), divisibility is immediate.
  -/
  by_cases heq :
      f m = f n

  · rw [heq]

  /-
  Hence assume

      f(m) < f(n).
  -/
  · have hlt :
        f m < f n := by
      exact lt_of_le_of_ne hmn heq

    /-
    First use

        f(m-n) ∣ f(m)-f(n).

    Since the right side is negative and nonzero, write

        f(m)-f(n) = f(m-n) * q

    with q < 0.

    This implies

        f(m-n) ≤ f(n)-f(m) < f(n),

    so

        f(m-n) < f(n).
    -/
    have hmnDiv :
        f (m - n) ∣ f m - f n :=
      hdiv m n

    rcases hmnDiv with ⟨q, hq⟩

    have hqneg :
        q < 0 := by

      by_contra hnot

      have hqnonneg :
          0 ≤ q := by
        exact le_of_not_gt hnot

      have hprod :
          0 ≤ f (m - n) * q := by
        exact
          mul_nonneg
            (le_of_lt (hpos (m - n)))
            hqnonneg

      linarith

    have hminusq :
        1 ≤ -q := by
      omega

    have hmul :
        f (m - n)
          ≤
        f (m - n) * (-q) := by

      have h :=
        mul_le_mul_of_nonneg_left
          hminusq
          (le_of_lt (hpos (m - n)))

      simpa using h

    have hrewrite :
        f (m - n) * (-q)
          =
        f n - f m := by

      calc
        f (m - n) * (-q)
            =
          -(f (m - n) * q) := by
            ring

        _ =
          -(f m - f n) := by
            rw [← hq]

        _ =
          f n - f m := by
            ring

    have hcdiff :
        f (m - n)
          ≤
        f n - f m := by

      calc
        f (m - n)
            ≤
          f (m - n) * (-q) :=
            hmul

        _ =
          f n - f m :=
            hrewrite

    have hclt :
        f (m - n) < f n := by
      have hmpos :
          0 < f m :=
        hpos m

      linarith

    /-
    Now apply the original condition to

        (m, m-n).

    Since

        m - (m-n) = n,

    we obtain

        f(n) ∣ f(m) - f(m-n).
    -/
    have hsecond :=
      hdiv m (m - n)

    have hindex :
        m - (m - n) = n := by
      ring

    rw [hindex] at hsecond

    /-
    We now have

        0 < f(m) < f(n)
        0 < f(m-n) < f(n)

    and

        f(n) ∣ f(m)-f(m-n).

    The small-multiple lemma forces

        f(m) = f(m-n).
    -/
    have hsame :
        f m = f (m - n) := by

      exact
        eq_of_dvd_sub_of_lt
          (hpos m)
          (hpos n)
          (hpos (m - n))
          hlt
          hclt
          hsecond

    /-
    Return to

        f(m-n) ∣ f(m)-f(n).

    Since f(m-n)=f(m), we have

        f(m) ∣ f(m)-f(n).

    Therefore f(m) divides f(n).
    -/
    have hfinalDiv :
        f m ∣ f m - f n := by

      have htemp :
          f (m - n) ∣ f m - f n := by
        exact hdiv m n

      rw [← hsame] at htemp

      exact htemp

    rcases hfinalDiv with ⟨r, hr⟩

    refine ⟨1 - r, ?_⟩

    calc
      f n
          =
        f m - (f m - f n) := by
          ring

      _ =
        f m - f m * r := by
          rw [hr]

      _ =
        f m * (1 - r) := by
          ring

end IMO2011P5
