import Mathlib

/-!
# IMO 1993, Problem 1

`f(x) = xⁿ + 5xⁿ⁻¹ + 3` with `n > 1` is not a product of two non-constant polynomials with
integer coefficients.

Writing `n = m + 2` avoids natural subtraction; the polynomial is `X^(m+2) + 5X^(m+1) + 3`.

## Proof

Suppose `f = g·h` with both factors non-constant.

* Reduce mod `3`. There `f ≡ X^(m+1)(X + 2)`.
* The constant terms satisfy `g(0)·h(0) = 3`, so `3` divides exactly one of them — if it divided
  both, `9` would divide `3`.
* Say `3 ∤ h(0)`. Then `X` does not divide `h mod 3`, and since `X` is prime in `(ZMod 3)[X]`,
  all of `X^(m+1)` divides `g mod 3`. Hence `deg (g mod 3) ≥ m+1`, and as the two reductions have
  degrees summing to `m+2`, `deg h ≤ 1`. With `deg h ≥ 1` this gives `deg h = 1`.
* A degree-one factor of a monic polynomial has leading coefficient `±1`, so `f` has an integer
  root `r`.
* But `f` has no integer root: mod `2`, neither `0` nor `1` is a root.
-/

open Polynomial

namespace Imo1993P1

/-- The polynomial `X^(m+2) + 5X^(m+1) + 3` over `ℤ`. -/
noncomputable def f (m : ℕ) : ℤ[X] := X ^ (m + 2) + C 5 * X ^ (m + 1) + C 3

theorem f_monic (m : ℕ) : (f m).Monic := by
  unfold f
  monicity!

theorem f_natDegree (m : ℕ) : (f m).natDegree = m + 2 := by
  unfold f
  compute_degree!

theorem f_ne_zero (m : ℕ) : f m ≠ 0 := (f_monic m).ne_zero

theorem f_coeff_zero (m : ℕ) : (f m).coeff 0 = 3 := by
  unfold f
  simp

theorem f_eval (m : ℕ) (r : ℤ) : (f m).eval r = r ^ (m + 2) + 5 * r ^ (m + 1) + 3 := by
  unfold f
  simp

/-- The reduction of `f` modulo `3`. -/
theorem f_map3 (m : ℕ) :
    (f m).map (Int.castRingHom (ZMod 3)) = X ^ (m + 1) * (X + C 2) := by
  have h5 : (Int.castRingHom (ZMod 3)) (5 : ℤ) = 2 := by rw [eq_intCast]; decide
  have h3 : (Int.castRingHom (ZMod 3)) (3 : ℤ) = 0 := by rw [eq_intCast]; decide
  unfold f
  rw [Polynomial.map_add, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, Polynomial.map_C, h5, h3,
    Polynomial.C_0, add_zero]
  ring

/-- `f` has no integer root. -/
theorem f_no_root (m : ℕ) (r : ℤ) : (f m).eval r ≠ 0 := by
  rw [f_eval]
  intro hr
  have h2 : ((r : ZMod 2)) ^ (m + 2) + 5 * (r : ZMod 2) ^ (m + 1) + 3 = 0 := by
    have := congrArg (fun z : ℤ => (z : ZMod 2)) hr
    push_cast at this
    exact this
  have hcases : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide
  rcases hcases ((r : ZMod 2)) with hc | hc <;> rw [hc] at h2 <;> simp at h2 <;>
    revert h2 <;> decide

/-- If `3` does not divide the constant term of `h`, then `h` has degree at most one. -/
theorem natDegree_le_one_of_not_dvd (m : ℕ) (g h : ℤ[X]) (hgh : g * h = f m)
    (hc : ¬ ((3 : ℤ) ∣ h.coeff 0)) : h.natDegree ≤ 1 := by
  set φ := Int.castRingHom (ZMod 3) with hφ
  set G := g.map φ with hG
  set H := h.map φ with hH
  have hprod : G * H = X ^ (m + 1) * (X + C 2) := by
    rw [hG, hH, ← Polynomial.map_mul, hgh, f_map3]
  have hH0 : H.coeff 0 ≠ 0 := by
    rw [hH, Polynomial.coeff_map, hφ]
    simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using hc
  have hXH : ¬ (X : (ZMod 3)[X]) ∣ H := by
    rw [Polynomial.X_dvd_iff]
    exact hH0
  have hdvd : (X : (ZMod 3)[X]) ^ (m + 1) ∣ G * H := by
    rw [hprod]
    exact Dvd.intro _ rfl
  have hGdvd : (X : (ZMod 3)[X]) ^ (m + 1) ∣ G :=
    Polynomial.prime_X.pow_dvd_of_dvd_mul_right (m + 1) hXH hdvd
  have hne : G * H ≠ 0 := by
    rw [hprod]
    exact mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) (Polynomial.X_add_C_ne_zero _)
  have hG0 : G ≠ 0 := fun h0 => hne (by rw [h0, zero_mul])
  have hH0' : H ≠ 0 := fun h0 => hne (by rw [h0, mul_zero])
  have hGdeg : m + 1 ≤ G.natDegree := by
    have hd := Polynomial.natDegree_le_of_dvd hGdvd hG0
    simpa using hd
  have hsum : G.natDegree + H.natDegree = m + 2 := by
    rw [← Polynomial.natDegree_mul hG0 hH0', hprod,
      Polynomial.natDegree_mul (pow_ne_zero _ Polynomial.X_ne_zero)
        (Polynomial.X_add_C_ne_zero _),
      Polynomial.natDegree_X_pow, Polynomial.natDegree_X_add_C]
  have hlead : g.leadingCoeff * h.leadingCoeff = 1 := by
    have hl := congrArg Polynomial.leadingCoeff hgh
    rwa [Polynomial.leadingCoeff_mul, (f_monic m).leadingCoeff] at hl
  have hdvd1 : h.leadingCoeff ∣ 1 := ⟨g.leadingCoeff, by rw [← hlead]; ring⟩
  have hu : IsUnit h.leadingCoeff := isUnit_of_dvd_one hdvd1
  have hnz : φ h.leadingCoeff ≠ 0 := by
    rcases Int.isUnit_iff.1 hu with h1 | h1 <;> rw [h1, hφ, eq_intCast] <;> decide
  have hkeep : H.natDegree = h.natDegree := by
    rw [hH]
    exact Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ hnz
  omega

/-- **IMO 1993 P1.** -/
theorem imo1993_p1 (n : ℕ) (hn : 1 < n) :
    ¬ ∃ g h : ℤ[X], 0 < g.natDegree ∧ 0 < h.natDegree ∧
      g * h = X ^ n + C 5 * X ^ (n - 1) + C 3 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hsub : m + 2 - 1 = m + 1 := by omega
  rw [hsub]
  rintro ⟨g, h, hg, hh, hgh⟩
  have hgh' : g * h = f m := hgh
  have hhg' : h * g = f m := by rw [mul_comm]; exact hgh'
  have hconst : g.coeff 0 * h.coeff 0 = 3 := by
    rw [← f_coeff_zero m, ← hgh', Polynomial.mul_coeff_zero]
  have hnotboth : ¬ ((3 : ℤ) ∣ g.coeff 0) ∨ ¬ ((3 : ℤ) ∣ h.coeff 0) := by
    by_contra hcon
    rw [not_or, not_not, not_not] at hcon
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hcon
    rw [ha, hb] at hconst
    obtain ⟨c, hc⟩ : ∃ c : ℤ, 9 * c = 3 := ⟨a * b, by linear_combination hconst⟩
    omega
  have hone : g.natDegree = 1 ∨ h.natDegree = 1 := by
    rcases hnotboth with hc | hc
    · have hle : g.natDegree ≤ 1 := natDegree_le_one_of_not_dvd m h g hhg' hc
      exact Or.inl (le_antisymm hle hg)
    · have hle : h.natDegree ≤ 1 := natDegree_le_one_of_not_dvd m g h hgh' hc
      exact Or.inr (le_antisymm hle hh)
  have hroot : ∃ r : ℤ, (f m).eval r = 0 := by
    have key : ∀ p q : ℤ[X], p * q = f m → q.natDegree = 1 → ∃ r : ℤ, (f m).eval r = 0 := by
      intro p q hpq hq1
      have hlead : p.leadingCoeff * q.leadingCoeff = 1 := by
        have hl := congrArg Polynomial.leadingCoeff hpq
        rwa [Polynomial.leadingCoeff_mul, (f_monic m).leadingCoeff] at hl
      have hdvd1 : q.leadingCoeff ∣ 1 := ⟨p.leadingCoeff, by rw [← hlead]; ring⟩
      have hu : IsUnit q.leadingCoeff := isUnit_of_dvd_one hdvd1
      have hlq : q.leadingCoeff = q.coeff 1 := by
        rw [Polynomial.leadingCoeff, hq1]
      have hsq : q.coeff 1 * q.coeff 1 = 1 := by
        rcases Int.isUnit_iff.1 hu with h1 | h1 <;> rw [hlq] at h1 <;> rw [h1] <;> norm_num
      have hdeg1 : q.degree ≤ 1 := by
        have hd := Polynomial.degree_le_natDegree (p := q)
        rw [hq1] at hd
        exact_mod_cast hd
      have hqform : q = C (q.coeff 1) * X + C (q.coeff 0) :=
        Polynomial.eq_X_add_C_of_degree_le_one hdeg1
      -- abstract the two coefficients, so that rewriting `q` cannot touch the root
      obtain ⟨a, b, hq_eq, ha1⟩ : ∃ a b : ℤ, q = C a * X + C b ∧ a * a = 1 :=
        ⟨q.coeff 1, q.coeff 0, hqform, hsq⟩
      refine ⟨-(a * b), ?_⟩
      rw [← hpq, Polynomial.eval_mul]
      have hq0 : q.eval (-(a * b)) = 0 := by
        rw [hq_eq]
        simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.eval_X]
        linear_combination (-b) * ha1
      rw [hq0, mul_zero]
    rcases hone with h1 | h1
    · exact key h g hhg' h1
    · exact key g h hgh' h1
  obtain ⟨r, hr⟩ := hroot
  exact f_no_root m r hr

end Imo1993P1
