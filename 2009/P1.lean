import Mathlib

/-!
# IMO 2009 Problem 1

Let `n` be a positive integer and let

    a₁, ..., aₖ     (k ≥ 2)

be distinct integers in `{1, ..., n}` such that

    n ∣ aᵢ (aᵢ₊₁ - 1)

for `i = 1, ..., k - 1`.

Prove that

    n ∤ aₖ (a₁ - 1).

We use zero-based indexing:

    a 0       = a₁
    ...
    a (k - 1) = aₖ.

Only the first `k` values of `a : ℕ → ℤ` matter.

The proof uses congruences modulo `n`.

From

    n ∣ aᵢ(aᵢ₊₁ - 1)

we obtain

    aᵢ ≡ aᵢ aᵢ₊₁  [ZMOD n].

Chaining these congruences shows

    a₁ ≡ a₁ a₂ ... aₖ  [ZMOD n].

If the forbidden final divisibility held, we would also get

    aₖ ≡ a₁ a₂ ... aₖ  [ZMOD n],

hence

    a₁ ≡ aₖ [ZMOD n].

Since both lie in `{1, ..., n}`, they must be equal, contradicting
the assumption that the `aᵢ` are distinct.
-/

namespace IMO2009P1

/-!
## Initial products
-/

/--
`chainProd a m` is

    a 0 * a 1 * ... * a m.
-/
def chainProd (a : ℕ → ℤ) : ℕ → ℤ
  | 0 => a 0
  | m + 1 => chainProd a m * a (m + 1)

/-!
## One step in the congruence chain
-/

/--
If

    a m ≡ a m * a (m + 1) [ZMOD n],

then the product through `m` is congruent to the product through `m+1`.
-/
lemma chainProd_step
    (n : ℤ)
    (a : ℕ → ℤ)
    (m : ℕ)
    (h :
      a m ≡ a m * a (m + 1) [ZMOD n]) :
    chainProd a m ≡ chainProd a (m + 1) [ZMOD n] := by
  cases m with

  | zero =>
      simpa [chainProd] using h

  | succ j =>
      have hm :=
        h.mul_left (chainProd a j)

      simpa [chainProd, mul_assoc] using hm

/--
All the consecutive congruences imply

    a 0 ≡ a 0 * ... * a m [ZMOD n].
-/
lemma first_modeq_chainProd
    (n : ℤ)
    (k : ℕ)
    (a : ℕ → ℤ)
    (hrel :
      ∀ i : ℕ,
        i + 1 < k →
          a i ≡ a i * a (i + 1) [ZMOD n]) :
    ∀ m : ℕ,
      m < k →
        a 0 ≡ chainProd a m [ZMOD n] := by

  intro m

  induction m with

  | zero =>
      intro _
      exact Int.ModEq.refl _

  | succ m ih =>
      intro hm

      have hm' : m < k := by
        omega

      have h₁ :
          a 0 ≡ chainProd a m [ZMOD n] :=
        ih hm'

      have h₂ :
          chainProd a m ≡
            chainProd a (m + 1) [ZMOD n] := by
        apply chainProd_step
        exact hrel m hm

      exact h₁.trans h₂

/-!
## Convert divisibility to congruence
-/

/--
From

    n ∣ x * (y - 1)

we obtain

    x ≡ x*y [ZMOD n].
-/
lemma modeq_of_chain_dvd
    {n x y : ℤ}
    (h : n ∣ x * (y - 1)) :
    x ≡ x * y [ZMOD n] := by

  apply Int.modEq_of_dvd

  have heq :
      x * y - x = x * (y - 1) := by
    ring

  rw [heq]

  exact h

/-!
## Congruence inside `[1,n]` implies equality
-/

/--
If `x,y ∈ [1,n]` and

    x ≡ y [ZMOD n],

then `x = y`.
-/
lemma eq_of_modeq_of_mem_interval
    {n x y : ℤ}
    (hx₁ : 1 ≤ x)
    (hxn : x ≤ n)
    (hy₁ : 1 ≤ y)
    (hyn : y ≤ n)
    (hxy : x ≡ y [ZMOD n]) :
    x = y := by

  by_cases hle : x ≤ y

  · have hdvd : n ∣ y - x := by
      exact hxy.dvd

    have hnonneg : 0 ≤ y - x := by
      omega

    have hlt : y - x < n := by
      omega

    have hz : y - x = 0 := by
      exact
        Int.eq_zero_of_dvd_of_nonneg_of_lt
          hnonneg
          hlt
          hdvd

    omega

  · have hdvd : n ∣ x - y := by
      exact hxy.symm.dvd

    have hnonneg : 0 ≤ x - y := by
      omega

    have hlt : x - y < n := by
      omega

    have hz : x - y = 0 := by
      exact
        Int.eq_zero_of_dvd_of_nonneg_of_lt
          hnonneg
          hlt
          hdvd

    omega

/-!
## IMO 2009 Problem 1
-/

/--
**IMO 2009 Problem 1.**

Zero-based formulation.

`a 0, ..., a (k-1)` are distinct integers in `{1, ..., n}` and

    n ∣ a i * (a (i+1) - 1)

for every consecutive pair.

Then

    n ∤ a (k-1) * (a 0 - 1).
-/
theorem imo2009_p1
    (n : ℤ)
    (k : ℕ)
    (a : ℕ → ℤ)
    (hn : 0 < n)
    (hk : 2 ≤ k)
    (hbound :
      ∀ i : ℕ,
        i < k →
          1 ≤ a i ∧ a i ≤ n)
    (hdistinct :
      ∀ i j : ℕ,
        i < k →
        j < k →
        i ≠ j →
        a i ≠ a j)
    (hchain :
      ∀ i : ℕ,
        i + 1 < k →
          n ∣ a i * (a (i + 1) - 1)) :
    ¬ n ∣ a (k - 1) * (a 0 - 1) := by

  intro hlast

  /-
  Turn every consecutive divisibility hypothesis into

      aᵢ ≡ aᵢ aᵢ₊₁ [ZMOD n].
  -/
  have hrel :
      ∀ i : ℕ,
        i + 1 < k →
          a i ≡ a i * a (i + 1) [ZMOD n] := by

    intro i hi

    exact
      modeq_of_chain_dvd
        (hchain i hi)

  /-
  By chaining,

      a₁ ≡ a₁ a₂ ... aₖ.
  -/
  have hfirst_full :
      a 0 ≡
        chainProd a (k - 1) [ZMOD n] := by

    apply first_modeq_chainProd n k a hrel

    omega

  /-
  We also need the product ending one position earlier:

      a₁ ≡ a₁ a₂ ... a_{k-1}.
  -/
  have hfirst_previous :
      a 0 ≡
        chainProd a (k - 2) [ZMOD n] := by

    apply first_modeq_chainProd n k a hrel

    omega

  /-
  Multiply by `aₖ`:

      a₁ aₖ ≡ a₁ a₂ ... aₖ.

  The auxiliary equality `hprod` deliberately isolates the
  `k - 1 = (k - 2) + 1` rewrite.  This avoids rewriting the
  occurrence inside `a (k - 1)`.
  -/
  have hfirst_last_to_full :
      a 0 * a (k - 1) ≡
        chainProd a (k - 1) [ZMOD n] := by

    have hm :
        a 0 * a (k - 1) ≡
          chainProd a (k - 2) * a (k - 1) [ZMOD n] :=
      hfirst_previous.mul_right (a (k - 1))

    have hk' :
        k - 1 = (k - 2) + 1 := by
      omega

    have hprod :
        chainProd a (k - 1) =
          chainProd a (k - 2) * a (k - 1) := by

      calc
        chainProd a (k - 1)
            =
          chainProd a ((k - 2) + 1) := by
            rw [hk']

        _ =
          chainProd a (k - 2) *
            a ((k - 2) + 1) := by
              rfl

        _ =
          chainProd a (k - 2) *
            a (k - 1) := by
              rw [← hk']

    rw [hprod]

    exact hm

  /-
  Assume the forbidden final divisibility

      n ∣ aₖ(a₁ - 1).

  This gives

      aₖ ≡ aₖ a₁ [ZMOD n].
  -/
  have hlast_modeq :
      a (k - 1) ≡
        a (k - 1) * a 0 [ZMOD n] := by

    exact
      modeq_of_chain_dvd hlast

  /-
  Since multiplication is commutative,

      aₖ a₁ ≡ a₁ a₂ ... aₖ,

  and therefore

      aₖ ≡ a₁ a₂ ... aₖ.
  -/
  have hlast_full :
      a (k - 1) ≡
        chainProd a (k - 1) [ZMOD n] := by

    have hcomm :
        a (k - 1) * a 0 ≡
          chainProd a (k - 1) [ZMOD n] := by

      calc
        a (k - 1) * a 0
            =
          a 0 * a (k - 1) := by
            ring

        _ ≡
          chainProd a (k - 1) [ZMOD n] :=
            hfirst_last_to_full

    exact
      hlast_modeq.trans hcomm

  /-
  Both endpoints are congruent to the same complete product.
  Hence

      a₁ ≡ aₖ [ZMOD n].
  -/
  have hends :
      a 0 ≡ a (k - 1) [ZMOD n] := by

    exact
      hfirst_full.trans
        hlast_full.symm

  /-
  Both relevant indices belong to `[0,k)`.
  -/
  have h0lt :
      0 < k := by
    omega

  have hlastlt :
      k - 1 < k := by
    omega

  /-
  Extract

      1 ≤ a₁ ≤ n
      1 ≤ aₖ ≤ n.
  -/
  have hb0 :
      1 ≤ a 0 ∧ a 0 ≤ n :=
    hbound 0 h0lt

  have hblast :
      1 ≤ a (k - 1) ∧
        a (k - 1) ≤ n :=
    hbound (k - 1) hlastlt

  /-
  Since they are congruent modulo `n` and both lie in `[1,n]`,
  they are actually equal.
  -/
  have heq :
      a 0 = a (k - 1) := by

    exact
      eq_of_modeq_of_mem_interval
        hb0.1
        hb0.2
        hblast.1
        hblast.2
        hends

  /-
  But `0 ≠ k-1` because `k ≥ 2`, and the entries are distinct.
  -/
  have hne :
      a 0 ≠ a (k - 1) := by

    apply
      hdistinct
        0
        (k - 1)

    · exact h0lt

    · exact hlastlt

    · omega

  exact hne heq

end IMO2009P1
