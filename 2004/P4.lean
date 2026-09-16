import Mathlib

namespace Imo2004P4

/-- `(∑ tᵢ)(∑ 1/tᵢ) ≥ |s|²` for positive `tᵢ`. -/
theorem card_sq_le {ι : Type*} [DecidableEq ι] (t : ι → ℝ) (s : Finset ι) :
    (∀ i ∈ s, 0 < t i) → ((s.card : ℝ)) ^ 2 ≤ (∑ i ∈ s, t i) * (∑ i ∈ s, 1 / t i) := by
  classical
  induction s using Finset.induction_on with
  | empty => intro _; simp
  | @insert a s ha ih =>
      intro hpos
      have hta : 0 < t a := hpos a (Finset.mem_insert_self a s)
      have hps : ∀ i ∈ s, 0 < t i := fun i hi => hpos i (Finset.mem_insert_of_mem hi)
      have hih := ih hps
      have hR : 0 ≤ ∑ i ∈ s, t i := Finset.sum_nonneg fun i hi => (hps i hi).le
      have hU : 0 ≤ ∑ i ∈ s, 1 / t i :=
        Finset.sum_nonneg fun i hi => (one_div_pos.2 (hps i hi)).le
      have hcard : (0 : ℝ) ≤ (s.card : ℝ) := Nat.cast_nonneg _
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
      push_cast
      have hprod : (t a * (∑ i ∈ s, 1 / t i)) * ((∑ i ∈ s, t i) / t a)
          = (∑ i ∈ s, t i) * (∑ i ∈ s, 1 / t i) := by
        field_simp
        ring
      have hnn : 0 ≤ t a * (∑ i ∈ s, 1 / t i) + (∑ i ∈ s, t i) / t a := by positivity
      have hge : 2 * (s.card : ℝ)
          ≤ t a * (∑ i ∈ s, 1 / t i) + (∑ i ∈ s, t i) / t a := by
        nlinarith [sq_nonneg (t a * (∑ i ∈ s, 1 / t i) - (∑ i ∈ s, t i) / t a),
          hih, hnn, hprod, hcard]
      have hexp : (t a + ∑ i ∈ s, t i) * (1 / t a + ∑ i ∈ s, 1 / t i)
          = 1 + (t a * (∑ i ∈ s, 1 / t i) + (∑ i ∈ s, t i) / t a)
            + (∑ i ∈ s, t i) * (∑ i ∈ s, 1 / t i) := by
        field_simp
        ring
      rw [hexp]
      nlinarith [hge, hih]

/-- The `n = 3` core: if `a + b ≤ c` then `(a+b+c)(1/a+1/b+1/c) ≥ 10`. -/
theorem three_bound {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b ≤ c) :
    10 ≤ (a + b + c) * (1 / a + 1 / b + 1 / c) := by
  have hk : 0 ≤ c - a - b := by linarith
  have e1 : 0 ≤ (9 * c - a - b) * (a - b) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have e2 : 0 ≤ (a + b) ^ 2 * (c - a - b) := mul_nonneg (sq_nonneg _) hk
  have e3 : 0 ≤ (a + b) * (c - a - b) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have hpoly : 0 ≤ (a + b + c) * (a * b + b * c + c * a) - 10 * (a * b * c) := by
    nlinarith [e1, e2, e3]
  have hrw : (a + b + c) * (1 / a + 1 / b + 1 / c) - 10
      = ((a + b + c) * (a * b + b * c + c * a) - 10 * (a * b * c)) / (a * b * c) := by
    field_simp
    ring
  have : 0 ≤ (a + b + c) * (1 / a + 1 / b + 1 / c) - 10 := by
    rw [hrw]
    exact div_nonneg hpoly (by positivity)
  linarith

/-- **IMO 2004 P4.** -/
theorem imo2004_p4 (n : ℕ) (hn : 3 ≤ n) (t : Fin n → ℝ) (ht : ∀ i, 0 < t i)
    (hsum : (∑ i, t i) * (∑ i, 1 / t i) < (n : ℝ) ^ 2 + 1)
    (i j k : Fin n) (hij : i < j) (hjk : j < k) :
    t k < t i + t j ∧ t i < t j + t k ∧ t j < t i + t k := by
  classical
  have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have key : ∀ p q r : Fin n, p ≠ q → p ≠ r → q ≠ r → t r < t p + t q := by
    intro p q r hpq hpr hqr
    by_contra hcon
    push Not at hcon
    set s : Finset (Fin n) := {p, q, r} with hs
    have hsub : s ⊆ Finset.univ := Finset.subset_univ _
    have hpm : p ∉ ({q, r} : Finset (Fin n)) := by simp [hpq, hpr]
    have hqm : q ∉ ({r} : Finset (Fin n)) := by simp [hqr]
    have hcard : s.card = 3 := by
      rw [hs, Finset.card_insert_of_notMem hpm, Finset.card_insert_of_notMem hqm,
        Finset.card_singleton]
    have hsumt : ∑ x ∈ s, t x = t p + t q + t r := by
      rw [hs, Finset.sum_insert hpm, Finset.sum_insert hqm, Finset.sum_singleton]
      ring
    have hsumi : ∑ x ∈ s, 1 / t x = 1 / t p + 1 / t q + 1 / t r := by
      rw [hs, Finset.sum_insert hpm, Finset.sum_insert hqm, Finset.sum_singleton]
      ring
    have hcard' : (Finset.univ \ s).card = n - 3 := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hcard]
    have hcast : (((n - 3 : ℕ)) : ℝ) = (n : ℝ) - 3 := by
      rw [Nat.cast_sub hn]
      norm_num
    have hsplit1 : (∑ x, t x) = (t p + t q + t r) + ∑ x ∈ Finset.univ \ s, t x := by
      rw [← Finset.sum_sdiff hsub, hsumt]
      ring
    have hsplit2 : (∑ x, 1 / t x)
        = (1 / t p + 1 / t q + 1 / t r) + ∑ x ∈ Finset.univ \ s, 1 / t x := by
      rw [← Finset.sum_sdiff hsub, hsumi]
      ring
    have hXY : 10 ≤ (t p + t q + t r) * (1 / t p + 1 / t q + 1 / t r) :=
      three_bound (ht p) (ht q) (ht r) hcon
    have hRU : ((n : ℝ) - 3) ^ 2
        ≤ (∑ x ∈ Finset.univ \ s, t x) * (∑ x ∈ Finset.univ \ s, 1 / t x) := by
      have h1 := card_sq_le t (Finset.univ \ s) (fun x _ => ht x)
      rwa [hcard', hcast] at h1
    have hR0 : 0 ≤ ∑ x ∈ Finset.univ \ s, t x :=
      Finset.sum_nonneg fun x _ => (ht x).le
    have hU0 : 0 ≤ ∑ x ∈ Finset.univ \ s, 1 / t x :=
      Finset.sum_nonneg fun x _ => (one_div_pos.2 (ht x)).le
    have hX0 : 0 < t p + t q + t r := by
      have := ht p; have := ht q; have := ht r; linarith
    have hY0 : 0 < 1 / t p + 1 / t q + 1 / t r := by
      have := one_div_pos.2 (ht p); have := one_div_pos.2 (ht q); have := one_div_pos.2 (ht r)
      linarith
    have hm0 : (0 : ℝ) ≤ (n : ℝ) - 3 := by linarith
    have hcross : 6 * ((n : ℝ) - 3)
        ≤ (t p + t q + t r) * (∑ x ∈ Finset.univ \ s, 1 / t x)
          + (∑ x ∈ Finset.univ \ s, t x) * (1 / t p + 1 / t q + 1 / t r) := by
      have hnn : 0 ≤ (t p + t q + t r) * (∑ x ∈ Finset.univ \ s, 1 / t x)
          + (∑ x ∈ Finset.univ \ s, t x) * (1 / t p + 1 / t q + 1 / t r) := by positivity
      have hbig : 10 * ((n : ℝ) - 3) ^ 2
          ≤ ((t p + t q + t r) * (1 / t p + 1 / t q + 1 / t r))
            * ((∑ x ∈ Finset.univ \ s, t x) * (∑ x ∈ Finset.univ \ s, 1 / t x)) := by
        nlinarith [hXY, hRU, sq_nonneg ((n : ℝ) - 3), mul_nonneg hR0 hU0]
      nlinarith [sq_nonneg ((t p + t q + t r) * (∑ x ∈ Finset.univ \ s, 1 / t x)
          - (∑ x ∈ Finset.univ \ s, t x) * (1 / t p + 1 / t q + 1 / t r)),
        hbig, hnn, hm0]
    have hfinal : (n : ℝ) ^ 2 + 1 ≤ (∑ x, t x) * (∑ x, 1 / t x) := by
      rw [hsplit1, hsplit2]
      nlinarith [hXY, hRU, hcross]
    linarith
  have hij' : i ≠ j := ne_of_lt hij
  have hjk' : j ≠ k := ne_of_lt hjk
  have hik' : i ≠ k := ne_of_lt (lt_trans hij hjk)
  exact ⟨key i j k hij' hik' hjk',
    key j k i hjk' (Ne.symm hij') (Ne.symm hik'),
    key i k j hik' hij' (Ne.symm hjk')⟩

end Imo2004P4
