import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

/-!
# IMO 1969 Problem 6 and a generalization

The classical problem: for real numbers `x₁, x₂, y₁, y₂, z₁, z₂` with `x₁ > 0`, `x₂ > 0`,
`x₁ y₁ - z₁² > 0` and `x₂ y₂ - z₂² > 0`,
```
    8 / ((x₁ + x₂)(y₁ + y₂) - (z₁ + z₂)²) ≤ 1/(x₁y₁ - z₁²) + 1/(x₂y₂ - z₂²).
```

The generalization (with `n = m + 1`): for positive reals `a₁,…,a_n`, `b₁,…,b_n` with
`A = a₁⋯a_{n-1} - a_n^{n-1} > 0` and `B = b₁⋯b_{n-1} - b_n^{n-1} > 0`,
```
    2^n / (∏_{i<n} (aᵢ + bᵢ) - (a_n + b_n)^{n-1}) ≤ 1/A + 1/B.
```
Here the first `n - 1 = m` entries are indexed by `Finset.range m` and the last entry is
carried by the separate variables `an`, `bn`.

Remark on the proof.  The suggested intermediate step
`2^{n-2} (A + B) ≤ ∏_{i<n} (aᵢ + bᵢ) - (a_n + b_n)^{n-1}` is *false* in general (already for
`n = 3`: take `x₁ = y₁ = 1, z₁ = 0, x₂ = y₂ = 100, z₂ = 0`, where the left side is `20002`
and the right side is `10201`).  What is true, and what is proved below, is the weaker bound
`(A^{1/m} + B^{1/m})^m ≤ ∏_{i<n} (aᵢ + bᵢ) - (a_n + b_n)^{n-1}` (a consequence of the
superadditivity of the geometric mean together with Minkowski's inequality), which still
suffices since `2^{m+1} A B ≤ (A + B) (A^{1/m} + B^{1/m})^m`.
-/

namespace IMO1969P6

/-- Superadditivity of the geometric mean: `(∏ f)^{1/m} + (∏ g)^{1/m} ≤ (∏ (f + g))^{1/m}`. -/
lemma geom_mean_superadd {m : ℕ} (hm : 0 < m) (f g : ℕ → ℝ)
    (hf : ∀ i ∈ Finset.range m, 0 < f i) (hg : ∀ i ∈ Finset.range m, 0 < g i) :
    (∏ i ∈ Finset.range m, f i) ^ ((m : ℝ)⁻¹) + (∏ i ∈ Finset.range m, g i) ^ ((m : ℝ)⁻¹)
      ≤ (∏ i ∈ Finset.range m, (f i + g i)) ^ ((m : ℝ)⁻¹) := by
  have hmR : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  have hS : 0 < ∏ i ∈ Finset.range m, (f i + g i) :=
    Finset.prod_pos (fun i hi => by linarith [hf i hi, hg i hi])
  have hP : 0 < ∏ i ∈ Finset.range m, f i := Finset.prod_pos (fun i hi => hf i hi)
  have hQ : 0 < ∏ i ∈ Finset.range m, g i := Finset.prod_pos (fun i hi => hg i hi)
  set S := ∏ i ∈ Finset.range m, (f i + g i) with hSdef
  have key : ∀ h : ℕ → ℝ, (∀ i ∈ Finset.range m, 0 < h i) →
      ((∏ i ∈ Finset.range m, h i) / S) ^ ((m:ℝ)⁻¹)
        ≤ ∑ i ∈ Finset.range m, (m:ℝ)⁻¹ * (h i / (f i + g i)) := by
    intro h hh
    have hamgm := Real.geom_mean_le_arith_mean_weighted (Finset.range m)
      (fun _ => (m:ℝ)⁻¹) (fun i => h i / (f i + g i))
      (fun i _ => by positivity)
      (by simp [Finset.sum_const, Finset.card_range]; field_simp)
      (fun i hi => by
        have := hh i hi; have := hf i hi; have := hg i hi; positivity)
    calc ((∏ i ∈ Finset.range m, h i) / S) ^ ((m:ℝ)⁻¹)
        = ∏ i ∈ Finset.range m, (h i / (f i + g i)) ^ ((m:ℝ)⁻¹) := by
          rw [Real.finset_prod_rpow _ _ (fun i hi => by
            have := hh i hi; have := hf i hi; have := hg i hi; positivity)]
          congr 1
          rw [Finset.prod_div_distrib]
      _ ≤ _ := hamgm
  have h1 := key f hf
  have h2 := key g hg
  have hsum : (∑ i ∈ Finset.range m, (m:ℝ)⁻¹ * (f i / (f i + g i)))
      + (∑ i ∈ Finset.range m, (m:ℝ)⁻¹ * (g i / (f i + g i))) = 1 := by
    rw [← Finset.sum_add_distrib]
    have hpt : ∀ i ∈ Finset.range m,
        (m:ℝ)⁻¹ * (f i / (f i + g i)) + (m:ℝ)⁻¹ * (g i / (f i + g i)) = (m:ℝ)⁻¹ := by
      intro i hi
      have h0 : f i + g i ≠ 0 := by have := hf i hi; have := hg i hi; positivity
      field_simp
    rw [Finset.sum_congr rfl hpt]
    simp [Finset.card_range]
    field_simp
  have hSr : (0:ℝ) < S ^ ((m:ℝ)⁻¹) := Real.rpow_pos_of_pos hS _
  rw [Real.div_rpow hP.le hS.le] at h1
  rw [Real.div_rpow hQ.le hS.le] at h2
  have h3 := add_le_add h1 h2
  rw [hsum, ← add_div, div_le_one hSr] at h3
  linarith

/-- Minkowski's inequality for the `m`-norm on `ℝ²`. -/
lemma minkowski_two {m : ℕ} (hm : 0 < m) {x y z w : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hw : 0 ≤ w) :
    ((x + z) ^ m + (y + w) ^ m : ℝ) ^ ((m:ℝ)⁻¹)
      ≤ (x ^ m + y ^ m) ^ ((m:ℝ)⁻¹) + (z ^ m + w ^ m) ^ ((m:ℝ)⁻¹) := by
  have hp : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have h := Real.Lp_add_le (Finset.univ : Finset (Fin 2)) ![x, y] ![z, w] hp
  simp [Fin.sum_univ_two, abs_of_nonneg, hx, hy, hz, hw,
    abs_of_nonneg (add_nonneg hx hz), abs_of_nonneg (add_nonneg hy hw),
    Real.rpow_natCast, one_div] at h
  exact h

/-- The final algebraic step: `2^{m+1} A^m B^m ≤ (A^m + B^m)(A + B)^m`. -/
lemma key_alg (m : ℕ) {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    (2:ℝ) ^ (m + 1) * (A ^ m * B ^ m) ≤ (A ^ m + B ^ m) * (A + B) ^ m := by
  have h1 : 4 * (A^m * B^m) ≤ (A^m + B^m)^2 := by
    nlinarith [sq_nonneg (A^m - B^m), pow_pos hA m, pow_pos hB m]
  have h2 : (4*(A*B))^m ≤ ((A+B)^2)^m :=
    pow_le_pow_left₀ (by positivity) (by nlinarith [sq_nonneg (A-B)]) m
  have h2' : 4^m * (A^m * B^m) ≤ ((A+B)^m)^2 := by
    calc (4:ℝ)^m * (A^m*B^m) = (4*(A*B))^m := by rw [mul_pow, mul_pow]
      _ ≤ ((A+B)^2)^m := h2
      _ = ((A+B)^m)^2 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  have e2 : ((2:ℝ)^(m+1))^2 = 4 * 4^m := by
    rw [← pow_mul, mul_comm (m+1) 2, pow_mul]; norm_num [pow_succ]; ring
  have hsq : ((2:ℝ)^(m+1) * (A^m * B^m))^2 ≤ ((A^m + B^m) * (A + B)^m)^2 := by
    have e : ((2:ℝ)^(m+1) * (A^m * B^m))^2 = (4*(A^m*B^m)) * (4^m * (A^m*B^m)) := by
      rw [mul_pow, e2]; ring
    rw [e, mul_pow]
    exact mul_le_mul h1 h2' (by positivity) (by positivity)
  have hL : 0 ≤ (2:ℝ)^(m+1) * (A^m * B^m) := by positivity
  have hR : 0 ≤ (A^m + B^m) * (A + B)^m := by positivity
  nlinarith [hsq, hL, hR]

/-- The main geometric estimate:
`∏ (aᵢ + bᵢ) - (aₙ + bₙ)^m ≥ (A^{1/m} + B^{1/m})^m`, where `A = ∏ aᵢ - aₙ^m`,
`B = ∏ bᵢ - bₙ^m`. -/
lemma denom_lower_bound {m : ℕ} (hm : 0 < m) (a b : ℕ → ℝ) (an bn : ℝ)
    (ha : ∀ i ∈ Finset.range m, 0 < a i) (hb : ∀ i ∈ Finset.range m, 0 < b i)
    (han : 0 ≤ an) (hbn : 0 ≤ bn)
    (hA : 0 ≤ (∏ i ∈ Finset.range m, a i) - an ^ m)
    (hB : 0 ≤ (∏ i ∈ Finset.range m, b i) - bn ^ m) :
    (((∏ i ∈ Finset.range m, a i) - an ^ m) ^ ((m:ℝ)⁻¹)
        + ((∏ i ∈ Finset.range m, b i) - bn ^ m) ^ ((m:ℝ)⁻¹)) ^ m + (an + bn) ^ m
      ≤ ∏ i ∈ Finset.range m, (a i + b i) := by
  have hm' : m ≠ 0 := hm.ne'
  set A := (∏ i ∈ Finset.range m, a i) - an ^ m with hAdef
  set B := (∏ i ∈ Finset.range m, b i) - bn ^ m with hBdef
  set al := A ^ ((m:ℝ)⁻¹) with haldef
  set be := B ^ ((m:ℝ)⁻¹) with hbedef
  have hal : 0 ≤ al := Real.rpow_nonneg hA _
  have hbe : 0 ≤ be := Real.rpow_nonneg hB _
  have halm : al ^ m = A := Real.rpow_inv_natCast_pow hA hm'
  have hbem : be ^ m = B := Real.rpow_inv_natCast_pow hB hm'
  have hPa : 0 < ∏ i ∈ Finset.range m, a i := Finset.prod_pos (fun i hi => ha i hi)
  have hPb : 0 < ∏ i ∈ Finset.range m, b i := Finset.prod_pos (fun i hi => hb i hi)
  -- Minkowski
  have hmink := minkowski_two hm hal han hbe hbn
  rw [halm, hbem] at hmink
  have hea : A + an ^ m = ∏ i ∈ Finset.range m, a i := by rw [hAdef]; ring
  have heb : B + bn ^ m = ∏ i ∈ Finset.range m, b i := by rw [hBdef]; ring
  rw [hea, heb] at hmink
  -- geometric mean superadditivity
  have hgeo := geom_mean_superadd hm a b ha hb
  have hchain :
      ((al + be) ^ m + (an + bn) ^ m) ^ ((m:ℝ)⁻¹)
        ≤ (∏ i ∈ Finset.range m, (a i + b i)) ^ ((m:ℝ)⁻¹) := le_trans hmink hgeo
  have hlhs : (0:ℝ) ≤ (al + be) ^ m + (an + bn) ^ m := by positivity
  have hPab : 0 < ∏ i ∈ Finset.range m, (a i + b i) :=
    Finset.prod_pos (fun i hi => by linarith [ha i hi, hb i hi])
  have := pow_le_pow_left₀ (Real.rpow_nonneg hlhs _) hchain m
  rwa [Real.rpow_inv_natCast_pow hlhs hm',
    Real.rpow_inv_natCast_pow hPab.le hm'] at this

/-- **Generalized IMO 1969 Problem 6.**  For positive reals `a₀,…,a_{m-1}, aₙ` and
`b₀,…,b_{m-1}, bₙ` (so `n = m + 1` numbers in each family) with
`A = ∏ aᵢ - aₙ^m > 0` and `B = ∏ bᵢ - bₙ^m > 0` we have
`2^{m+1} / (∏ (aᵢ + bᵢ) - (aₙ + bₙ)^m) ≤ 1/A + 1/B`. -/
theorem generalized (m : ℕ) (hm : 0 < m) (a b : ℕ → ℝ) (an bn : ℝ)
    (ha : ∀ i ∈ Finset.range m, 0 < a i) (hb : ∀ i ∈ Finset.range m, 0 < b i)
    (han : 0 < an) (hbn : 0 < bn)
    (hA : 0 < (∏ i ∈ Finset.range m, a i) - an ^ m)
    (hB : 0 < (∏ i ∈ Finset.range m, b i) - bn ^ m) :
    (2:ℝ) ^ (m + 1) / ((∏ i ∈ Finset.range m, (a i + b i)) - (an + bn) ^ m)
      ≤ 1 / ((∏ i ∈ Finset.range m, a i) - an ^ m)
        + 1 / ((∏ i ∈ Finset.range m, b i) - bn ^ m) := by
  have hm' : m ≠ 0 := hm.ne'
  set A := (∏ i ∈ Finset.range m, a i) - an ^ m with hAdef
  set B := (∏ i ∈ Finset.range m, b i) - bn ^ m with hBdef
  set al := A ^ ((m:ℝ)⁻¹) with haldef
  set be := B ^ ((m:ℝ)⁻¹) with hbedef
  have hal : 0 < al := Real.rpow_pos_of_pos hA _
  have hbe : 0 < be := Real.rpow_pos_of_pos hB _
  have halm : al ^ m = A := Real.rpow_inv_natCast_pow hA.le hm'
  have hbem : be ^ m = B := Real.rpow_inv_natCast_pow hB.le hm'
  have hlb := denom_lower_bound hm a b an bn ha hb han.le hbn.le hA.le hB.le
  rw [← hAdef, ← hBdef, ← haldef, ← hbedef] at hlb
  set D := (∏ i ∈ Finset.range m, (a i + b i)) - (an + bn) ^ m with hDdef
  have hD : (al + be) ^ m ≤ D := by rw [hDdef]; linarith
  have hDpos : 0 < D := lt_of_lt_of_le (by positivity) hD
  have hstep1 : (2:ℝ) ^ (m+1) / D ≤ (2:ℝ) ^ (m+1) / (al + be) ^ m := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity) hD
  have hstep2 : (2:ℝ) ^ (m+1) / (al + be) ^ m ≤ 1 / A + 1 / B := by
    rw [div_add_div _ _ (ne_of_gt hA) (ne_of_gt hB), div_le_div_iff₀ (by positivity) (by positivity)]
    have hk := key_alg m hal hbe
    rw [halm, hbem] at hk
    nlinarith [hk, mul_pos hA hB]
  linarith

/-- **IMO 1969, Problem 6.**  For real numbers `x₁, x₂, y₁, y₂, z₁, z₂` with `x₁, x₂ > 0`,
`x₁y₁ - z₁² > 0` and `x₂y₂ - z₂² > 0`,
`8 / ((x₁+x₂)(y₁+y₂) - (z₁+z₂)²) ≤ 1/(x₁y₁ - z₁²) + 1/(x₂y₂ - z₂²)`. -/
theorem imo1969_p6 (x₁ x₂ y₁ y₂ z₁ z₂ : ℝ) (hx₁ : 0 < x₁) (hx₂ : 0 < x₂)
    (hA : 0 < x₁ * y₁ - z₁ ^ 2) (hB : 0 < x₂ * y₂ - z₂ ^ 2) :
    8 / ((x₁ + x₂) * (y₁ + y₂) - (z₁ + z₂) ^ 2)
      ≤ 1 / (x₁ * y₁ - z₁ ^ 2) + 1 / (x₂ * y₂ - z₂ ^ 2) := by
  set A := x₁ * y₁ - z₁ ^ 2 with hAdef
  set B := x₂ * y₂ - z₂ ^ 2 with hBdef
  have hy₁ : 0 < y₁ := by nlinarith [sq_nonneg z₁]
  have hy₂ : 0 < y₂ := by nlinarith [sq_nonneg z₂]
  set u := Real.sqrt A with hudef
  set v := Real.sqrt B with hvdef
  have hu : 0 < u := Real.sqrt_pos.mpr hA
  have hv : 0 < v := Real.sqrt_pos.mpr hB
  have hu2 : u ^ 2 = A := Real.sq_sqrt hA.le
  have hv2 : v ^ 2 = B := Real.sq_sqrt hB.le
  have hp : 0 < x₁ * y₂ := by positivity
  have hq : 0 < x₂ * y₁ := by positivity
  have hc : 0 ≤ u * v + |z₁ * z₂| := by positivity
  have hpq : (u * v + |z₁ * z₂|) ^ 2 ≤ (x₁ * y₂) * (x₂ * y₁) := by
    have hprod : (x₁ * y₂) * (x₂ * y₁) = (A + z₁ ^ 2) * (B + z₂ ^ 2) := by
      rw [hAdef, hBdef]; ring
    have habs : |z₁ * z₂| ^ 2 = z₁ ^ 2 * z₂ ^ 2 := by rw [sq_abs]; ring
    have hcross : 2 * (u * v) * |z₁ * z₂| ≤ B * z₁ ^ 2 + A * z₂ ^ 2 := by
      have h := sq_nonneg (v * |z₁| - u * |z₂|)
      have e1 : |z₁| ^ 2 = z₁ ^ 2 := sq_abs z₁
      have e2 : |z₂| ^ 2 = z₂ ^ 2 := sq_abs z₂
      have e3 : |z₁ * z₂| = |z₁| * |z₂| := abs_mul z₁ z₂
      nlinarith [h, hu2, hv2]
    rw [hprod]
    nlinarith [hcross, habs]
  have hsum_pq : 2 * (u * v + |z₁ * z₂|) ≤ x₁ * y₂ + x₂ * y₁ := by
    nlinarith [sq_nonneg (x₁ * y₂ - x₂ * y₁), hpq, hc, hp, hq]
  have hz : z₁ * z₂ ≤ |z₁ * z₂| := le_abs_self _
  have hD : (u + v) ^ 2 ≤ (x₁ + x₂) * (y₁ + y₂) - (z₁ + z₂) ^ 2 := by
    have expand : (x₁ + x₂) * (y₁ + y₂) - (z₁ + z₂) ^ 2
        = A + B + (x₁ * y₂ + x₂ * y₁) - 2 * (z₁ * z₂) := by rw [hAdef, hBdef]; ring
    rw [expand]
    nlinarith [hsum_pq, hz, hu2, hv2]
  have hDpos : 0 < (x₁ + x₂) * (y₁ + y₂) - (z₁ + z₂) ^ 2 :=
    lt_of_lt_of_le (by positivity) hD
  have hstep1 : 8 / ((x₁ + x₂) * (y₁ + y₂) - (z₁ + z₂) ^ 2) ≤ 8 / (u + v) ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) hD
  have hstep2 : 8 / (u + v) ^ 2 ≤ 1 / A + 1 / B := by
    rw [div_add_div _ _ (ne_of_gt hA) (ne_of_gt hB),
      div_le_div_iff₀ (by positivity) (by positivity)]
    have hk := key_alg 2 hu hv
    rw [hu2, hv2] at hk
    norm_num at hk
    nlinarith [hk, mul_pos hA hB]
  linarith

/-- The generalized inequality is sharp: equality holds when `aᵢ = bᵢ` for all `i` (and
`aₙ = bₙ`). -/
theorem generalized_eq_of_eq (m : ℕ) (a : ℕ → ℝ) (an : ℝ)
    (hA : 0 < (∏ i ∈ Finset.range m, a i) - an ^ m) :
    (2:ℝ) ^ (m + 1) / ((∏ i ∈ Finset.range m, (a i + a i)) - (an + an) ^ m)
      = 1 / ((∏ i ∈ Finset.range m, a i) - an ^ m)
        + 1 / ((∏ i ∈ Finset.range m, a i) - an ^ m) := by
  have h1 : (∏ i ∈ Finset.range m, (a i + a i)) = 2 ^ m * ∏ i ∈ Finset.range m, a i := by
    rw [show (2:ℝ)^m = ∏ _i ∈ Finset.range m, (2:ℝ) by
      rw [Finset.prod_const, Finset.card_range], ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun i _ => by ring)
  have h2 : (an + an) ^ m = 2 ^ m * an ^ m := by rw [← mul_pow]; ring_nf
  have hpow : (0:ℝ) < 2 ^ m := by positivity
  rw [h1, h2, ← mul_sub, pow_succ, mul_comm ((2:ℝ)^m) 2]
  field_simp
  ring

/-- IMO 1969 Problem 6 is sharp: equality holds when `x₁ = x₂`, `y₁ = y₂`, `z₁ = z₂`. -/
theorem imo1969_p6_eq_of_eq (x y z : ℝ) (hA : 0 < x * y - z ^ 2) :
    8 / ((x + x) * (y + y) - (z + z) ^ 2)
      = 1 / (x * y - z ^ 2) + 1 / (x * y - z ^ 2) := by
  have h : (x + x) * (y + y) - (z + z) ^ 2 = 4 * (x * y - z ^ 2) := by ring
  rw [h]
  field_simp
  ring

end IMO1969P6
