import Mathlib

namespace IMO2014P2

/-!
IMO 2014 Problem 2 — arithmetic/counting core.

The official solution sets

    k = ⌈√n⌉ - 1.

Writing q = k + 1 = ⌈√n⌉, we have

    (q - 1)^2 < n ≤ q^2.

Hence

    k^2 < n

and consequently

    n - k + 1 > k(k - 1) + 1.

This is the key numerical inequality in the pigeonhole
argument from the official solution.
-/

/-!
## Elementary arithmetic
-/

/--
If `1 ≤ k` and `k² < n`, then `k < n`.
-/
lemma k_lt_n_of_sq_lt
    {n k : ℕ}
    (hk : 1 ≤ k)
    (hkn : k * k < n) :
    k < n := by

  have hkle :
      k ≤ k * k := by
    nlinarith

  omega

/--
For positive `k`,

    k * (k - 1) = k² - k.
-/
lemma mul_pred_eq
    {k : ℕ}
    (hk : 1 ≤ k) :
    k * (k - 1) = k * k - k := by

  rw [Nat.mul_sub_left_distrib]

  simp

/--
The main numerical inequality used in the official proof:

    k(k - 1) + 1 < n - k + 1.
-/
lemma key_counting_inequality
    {n k : ℕ}
    (hk : 1 ≤ k)
    (hkn : k * k < n) :
    k * (k - 1) + 1 <
      n - k + 1 := by

  have hident :
      k * (k - 1) =
        k * k - k :=
    mul_pred_eq hk

  have hkle :
      k ≤ k * k := by
    nlinarith

  rw [hident]

  omega

/--
Same inequality written in the orientation used in the PDF.
-/
lemma key_counting_inequality'
    {n k : ℕ}
    (hk : 1 ≤ k)
    (hkn : k * k < n) :
    n - k + 1 >
      k * (k - 1) + 1 := by

  exact
    key_counting_inequality
      hk
      hkn

/-!
## Passing from q = k+1
-/

/--
If

    k = q - 1

and

    (q - 1)^2 < n,

then `k² < n`.
-/
lemma sq_lt_of_eq_pred
    {n k q : ℕ}
    (hk : k = q - 1)
    (hsq :
      (q - 1) * (q - 1) < n) :
    k * k < n := by

  subst k

  exact hsq

/--
If `q ≥ 2`, `k=q-1`, and

    (q-1)^2 < n,

then the counting inequality follows.
-/
lemma counting_bound_from_ceiling_data
    {n k q : ℕ}
    (hq : 2 ≤ q)
    (hk : k = q - 1)
    (hlower :
      (q - 1) * (q - 1) < n) :
    n - k + 1 >
      k * (k - 1) + 1 := by

  have hkpos :
      1 ≤ k := by
    omega

  have hksq :
      k * k < n := by

    exact
      sq_lt_of_eq_pred
        hk
        hlower

  exact
    key_counting_inequality'
      hkpos
      hksq

/-!
## Abstract pigeonhole counting
-/

/--
Suppose there are `n-k+1` candidate squares and at most

    1 + k(k-1)

of them can be covered.

The counting inequality implies that not all candidates
can be covered.
-/
lemma uncovered_candidate_exists
    {n candidates covered k : ℕ}
    (hcandidates :
      candidates = n - k + 1)
    (hcovered :
      covered ≤
        1 + k * (k - 1))
    (hineq :
      1 + k * (k - 1) <
        n - k + 1) :
    covered < candidates := by

  omega

/--
Direct specialization of the counting argument.
-/
lemma rook_counting_core
    {n k covered : ℕ}
    (hk : 1 ≤ k)
    (hkn : k * k < n)
    (hcovered :
      covered ≤
        1 + k * (k - 1)) :
    covered < n - k + 1 := by

  have hcount :
      1 + k * (k - 1) <
        n - k + 1 := by

    have h :
        k * (k - 1) + 1 <
          n - k + 1 :=
      key_counting_inequality
        hk
        hkn

    simpa [Nat.add_comm] using h

  exact lt_of_le_of_lt hcovered hcount

/-!
## Square-root boundary
-/

/--
If `q` is minimal with respect to reaching the square threshold,
then its predecessor has square strictly below `n`.
-/
lemma pred_sq_lt_of_minimal_square
    {n q : ℕ}
    (hq : 0 < q)
    (hminimal :
      ∀ t : ℕ,
        t < q →
        t * t < n) :
    (q - 1) * (q - 1) < n := by

  have hpred :
      q - 1 < q := by
    omega

  exact
    hminimal
      (q - 1)
      hpred

/--
If

    (q-1)^2 < n ≤ q^2,

and `k=q-1`, then

    k² < n ≤ (k+1)².
-/
lemma sqrt_boundary
    {n q : ℕ}
    (hq : 0 < q)
    (hupper :
      n ≤ q * q)
    (hminimal :
      ∀ t : ℕ,
        t < q →
        t * t < n) :
    let k := q - 1
    k * k < n ∧
      n ≤ (k + 1) * (k + 1) := by

  let k := q - 1

  have hpred :
      (q - 1) * (q - 1) < n :=
    pred_sq_lt_of_minimal_square
      hq
      hminimal

  have hkq :
      k + 1 = q := by

    dsimp [k]

    omega

  constructor

  · simpa [k] using hpred

  · rw [hkq]

    exact hupper

/-!
## Maximality
-/

/--
If

    n ≤ (k+1)²

and

    m² < n,

then `m ≤ k`.
-/
lemma maximal_of_square_boundary
    {n k m : ℕ}
    (hright :
      n ≤ (k + 1) * (k + 1))
    (hm :
      m * m < n) :
    m ≤ k := by

  by_contra hnot

  have hmk :
      k + 1 ≤ m := by
    omega

  have hsq :
      (k + 1) * (k + 1) ≤
        m * m := by
    nlinarith

  omega

/--
Therefore, if

    k² < n ≤ (k+1)²,

then `k` is the largest natural number whose square is
strictly less than `n`.
-/
theorem unique_maximal_k
    {n k : ℕ}
    (hleft :
      k * k < n)
    (hright :
      n ≤ (k + 1) * (k + 1)) :
    k * k < n ∧
      ∀ m : ℕ,
        m * m < n →
        m ≤ k := by

  constructor

  · exact hleft

  · intro m hm

    exact
      maximal_of_square_boundary
        hright
        hm

/-!
## Final arithmetic theorem
-/

/--
Arithmetic core of IMO 2014 Problem 2.

If `q` is the least positive integer whose square reaches `n`
and `k=q-1`, then

* `k² < n`;
* `n ≤ (k+1)²`;
* `n-k+1 > k(k-1)+1`;
* every `m` with `m²<n` satisfies `m≤k`.

This is the numerical content behind

    k = ⌈√n⌉ - 1.
-/
theorem imo2014_p2_arithmetic
    {n q : ℕ}
    (hn : 2 ≤ n)
    (hq : 2 ≤ q)
    (hupper :
      n ≤ q * q)
    (hminimal :
      ∀ t : ℕ,
        t < q →
        t * t < n) :
    let k := q - 1
    k * k < n ∧
    n ≤ (k + 1) * (k + 1) ∧
    n - k + 1 >
      k * (k - 1) + 1 ∧
    ∀ m : ℕ,
      m * m < n →
      m ≤ k := by

  let k := q - 1

  have hqpos :
      0 < q := by
    omega

  have hkpos :
      1 ≤ k := by

    dsimp [k]

    omega

  have hpred :
      (q - 1) * (q - 1) < n :=
    pred_sq_lt_of_minimal_square
      hqpos
      hminimal

  have hksq :
      k * k < n := by

    simpa [k] using hpred

  have hkq :
      k + 1 = q := by

    dsimp [k]

    omega

  have hupperK :
      n ≤
        (k + 1) * (k + 1) := by

    rw [hkq]

    exact hupper

  have hcount :
      n - k + 1 >
        k * (k - 1) + 1 :=
    key_counting_inequality'
      hkpos
      hksq

  have hnpos :
      0 < n := by
    omega

  refine
    ⟨hksq,
     hupperK,
     hcount,
     ?_⟩

  intro m hm

  exact
    maximal_of_square_boundary
      hupperK
      hm

end IMO2014P2
