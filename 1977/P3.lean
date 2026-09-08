/-
# IMO 1977, Problem 3

Let `n > 2` and let `Vₙ = {1 + kn : k = 1, 2, …}`.  A number `m ∈ Vₙ` is
*indecomposable* if there are no `p, q ∈ Vₙ` with `m = pq`.  Prove that some
`r ∈ Vₙ` can be written as a product of indecomposables in more than one way.

## Modelling

`V n m` is `∃ j ≥ 1, m = 1 + j * n`, and `Indec n m` is `V n m` together with
the non-existence of a factorization inside `Vₙ`.  "In more than one way (up to
order)" is formalized by exhibiting `r = A * B = C * D` with all four factors
indecomposable and `A ≠ C`, `A ≠ D`: that is exactly what it means for the
multisets `{A, B}` and `{C, D}` to differ.

## Proof

The construction is the one from the "Remark and Solution 2" on AoPS: with
`a = n - 1` and `b = 2n - 1` (both `≡ -1 mod n`),

  `r = a² · b² = (ab) · (ab)`,

so `A = a²`, `B = b²`, `C = D = ab`, and `A ≠ C` because `a ≠ b`.

For indecomposability we use: if `m = pq` with `p, q ∈ Vₙ` then the smaller
factor `p` satisfies `p² ≤ m` and `p ∣ m`, and `p ≥ n + 1`.  Writing `n = u + 3`
(so `a = u + 2`, `b = 2u + 5`, `n + 1 = u + 4`):

* `a² = (u+2)²`: any `p ∈ Vₙ` has `p ≥ u + 4 > u + 2`, so `p² > a²`.
* `b² = (u+2... )`: a factor with `j ≥ 2` already exceeds `b`, so `p = u + 4`,
  and `b² = (u+4)·4(u+1) + 9` forces `(u+4) ∣ 9`, i.e. `u = 5`, i.e. `n = 8`.
* `ab`: likewise `p = u + 4`, and `ab = (u+4)(2u+1) + 6` forces `(u+4) ∣ 6`,
  i.e. `u = 2`, i.e. `n = 5`.

So the construction works for every `n ∉ {5, 8}`.  (The AoPS text notices the
exception `n = 8` but misses `n = 5`, where `ab = 4 · 9 = 36 = 6 · 6` really is
decomposable.)  The two exceptional cases are handled separately with
`b = 3n - 1`: `4, 14` for `n = 5` and `7, 23` for `n = 8`.
-/

import Mathlib

namespace Imo1977P3

/-- `m` belongs to `Vₙ`. -/
def V (n m : ℕ) : Prop := ∃ j : ℕ, 1 ≤ j ∧ m = 1 + j * n

/-- `m` is indecomposable in `Vₙ`. -/
def Indec (n m : ℕ) : Prop := V n m ∧ ¬ ∃ p q, V n p ∧ V n q ∧ m = p * q

private lemma V_mul {n a b : ℕ} (ha : V n a) (hb : V n b) : V n (a * b) := by
  obtain ⟨i, hi, rfl⟩ := ha
  obtain ⟨j, hj, rfl⟩ := hb
  exact ⟨i + j + i * j * n, by omega, by ring⟩

/-- To prove indecomposability it suffices to rule out the *smaller* factor. -/
private lemma indec_of (n m : ℕ) (hm : V n m)
    (h : ∀ p, V n p → p ∣ m → p * p ≤ m → False) : Indec n m := by
  refine ⟨hm, ?_⟩
  rintro ⟨p, q, hp, hq, hpq⟩
  rcases le_total p q with hle | hle
  · refine h p hp ⟨q, hpq⟩ ?_
    rw [hpq]
    exact Nat.mul_le_mul (le_refl p) hle
  · refine h q hq ⟨p, by rw [hpq]; ring⟩ ?_
    rw [hpq]
    exact Nat.mul_le_mul hle (le_refl q)

/-- **IMO 1977, Problem 3.** -/
theorem imo1977_p3 (n : ℕ) (hn : 2 < n) :
    ∃ r A B C D : ℕ, V n r ∧
      Indec n A ∧ Indec n B ∧ Indec n C ∧ Indec n D ∧
      r = A * B ∧ r = C * D ∧ A ≠ C ∧ A ≠ D := by
  by_cases h5 : n = 5
  · -- `n = 5`: use `4` and `14`
    subst h5
    have iA : Indec 5 16 := by
      refine indec_of _ _ ⟨3, by norm_num, by norm_num⟩ ?_
      rintro p ⟨j, hj, rfl⟩ hdvd hle
      nlinarith
    have iB : Indec 5 196 := by
      refine indec_of _ _ ⟨39, by norm_num, by norm_num⟩ ?_
      rintro p ⟨j, hj, rfl⟩ hdvd hle
      have hj2 : j ≤ 2 := by nlinarith
      interval_cases j <;> norm_num at hdvd
    have iC : Indec 5 56 := by
      refine indec_of _ _ ⟨11, by norm_num, by norm_num⟩ ?_
      rintro p ⟨j, hj, rfl⟩ hdvd hle
      have hj1 : j ≤ 1 := by nlinarith
      have hj' : j = 1 := by omega
      subst hj'
      norm_num at hdvd
    exact ⟨3136, 16, 196, 56, 56, ⟨627, by norm_num, by norm_num⟩, iA, iB, iC, iC,
      by norm_num, by norm_num, by norm_num, by norm_num⟩
  by_cases h8 : n = 8
  · -- `n = 8`: use `7` and `23`
    subst h8
    have iA : Indec 8 49 := by
      refine indec_of _ _ ⟨6, by norm_num, by norm_num⟩ ?_
      rintro p ⟨j, hj, rfl⟩ hdvd hle
      nlinarith
    have iB : Indec 8 529 := by
      refine indec_of _ _ ⟨66, by norm_num, by norm_num⟩ ?_
      rintro p ⟨j, hj, rfl⟩ hdvd hle
      have hj2 : j ≤ 2 := by nlinarith
      interval_cases j <;> norm_num at hdvd
    have iC : Indec 8 161 := by
      refine indec_of _ _ ⟨20, by norm_num, by norm_num⟩ ?_
      rintro p ⟨j, hj, rfl⟩ hdvd hle
      have hj1 : j ≤ 1 := by nlinarith
      have hj' : j = 1 := by omega
      subst hj'
      norm_num at hdvd
    exact ⟨25921, 49, 529, 161, 161, ⟨3240, by norm_num, by norm_num⟩, iA, iB, iC, iC,
      by norm_num, by norm_num, by norm_num, by norm_num⟩
  -- the general case
  obtain ⟨u, rfl⟩ : ∃ u, n = u + 3 := ⟨n - 3, by omega⟩
  have hu2 : u ≠ 2 := by omega
  have hu5 : u ≠ 5 := by omega
  have hA : V (u + 3) ((u + 2) * (u + 2)) := ⟨u + 1, by omega, by ring⟩
  have hB : V (u + 3) ((2 * u + 5) * (2 * u + 5)) := ⟨4 * u + 8, by omega, by ring⟩
  have hC : V (u + 3) ((u + 2) * (2 * u + 5)) := ⟨2 * u + 3, by omega, by ring⟩
  have iA : Indec (u + 3) ((u + 2) * (u + 2)) := by
    refine indec_of _ _ hA ?_
    rintro p ⟨j, hj, rfl⟩ hdvd hle
    have hp : u + 4 ≤ 1 + j * (u + 3) := by nlinarith
    nlinarith
  have iB : Indec (u + 3) ((2 * u + 5) * (2 * u + 5)) := by
    refine indec_of _ _ hB ?_
    rintro p ⟨j, hj, rfl⟩ hdvd hle
    have hj1 : j = 1 := by
      by_contra hne
      have h2 : 2 ≤ j := by omega
      have hbig : 2 * u + 7 ≤ 1 + j * (u + 3) := by nlinarith
      nlinarith
    subst hj1
    rw [show 1 + 1 * (u + 3) = u + 4 from by ring,
      show (2 * u + 5) * (2 * u + 5) = (u + 4) * (4 * (u + 1)) + 9 from by ring] at hdvd
    have h9 : (u + 4) ∣ 9 := (Nat.dvd_add_right ⟨4 * (u + 1), rfl⟩).mp hdvd
    have hle9 : u + 4 ≤ 9 := Nat.le_of_dvd (by norm_num) h9
    have hub : u ≤ 5 := by omega
    interval_cases u <;> omega
  have iC : Indec (u + 3) ((u + 2) * (2 * u + 5)) := by
    refine indec_of _ _ hC ?_
    rintro p ⟨j, hj, rfl⟩ hdvd hle
    have hj1 : j = 1 := by
      by_contra hne
      have h2 : 2 ≤ j := by omega
      have hbig : 2 * u + 7 ≤ 1 + j * (u + 3) := by nlinarith
      nlinarith
    subst hj1
    rw [show 1 + 1 * (u + 3) = u + 4 from by ring,
      show (u + 2) * (2 * u + 5) = (u + 4) * (2 * u + 1) + 6 from by ring] at hdvd
    have h6 : (u + 4) ∣ 6 := (Nat.dvd_add_right ⟨2 * u + 1, rfl⟩).mp hdvd
    have hle6 : u + 4 ≤ 6 := Nat.le_of_dvd (by norm_num) h6
    have hub : u ≤ 2 := by omega
    interval_cases u <;> omega
  refine ⟨(u + 2) * (u + 2) * ((2 * u + 5) * (2 * u + 5)), (u + 2) * (u + 2),
    (2 * u + 5) * (2 * u + 5), (u + 2) * (2 * u + 5), (u + 2) * (2 * u + 5),
    V_mul hA hB, iA, iB, iC, iC, rfl, by ring, ?_, ?_⟩
  · intro h; nlinarith
  · intro h; nlinarith

end Imo1977P3
