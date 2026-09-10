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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Imo1983P3

/-- Auxiliary: if `u` and `v` are coprime integers and `v > 0`, then for every integer `n`
there is a natural number `x < v` with `v ∣ n - x * u`. -/
lemma exists_small_nat_smul_congr {u v : ℤ} (hv : 0 < v) (h : IsCoprime u v) (n : ℤ) :
    ∃ x : ℕ, (x : ℤ) < v ∧ v ∣ n - x * u := by
  obtain ⟨s, t, hst⟩ := h
  refine ⟨((n * s) % v).toNat, ?_, ?_⟩
  · rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (ne_of_gt hv))]
    exact Int.emod_lt_of_pos _ hv
  · rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (ne_of_gt hv))]
    refine ⟨n * t + ((n * s) / v) * u, ?_⟩
    have hd : (n * s) % v = n * s - v * ((n * s) / v) := Int.emod_def _ _
    rw [hd]
    linear_combination (-n) * hst

/-- Chicken McNugget / Sylvester, integer form: if `b`, `c` are coprime positive naturals then
every integer `m` with `(b-1)*(c-1) ≤ m` can be written as `y*c + z*b` with `y z : ℕ`. -/
lemma exists_repr_of_ge {b c : ℕ} (hb : 0 < b) (hcop : Nat.Coprime b c) (m : ℤ)
    (hm : ((b : ℤ) - 1) * ((c : ℤ) - 1) ≤ m) :
    ∃ y z : ℕ, m = y * c + z * b := by
  have hb' : (0 : ℤ) < b := by exact_mod_cast hb
  have hcop' : IsCoprime (c : ℤ) (b : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop.symm
  obtain ⟨y, hylt, hdvd⟩ := exists_small_nat_smul_congr hb' hcop' m
  obtain ⟨z, hz⟩ := hdvd
  have hyle : (y : ℤ) ≤ (b : ℤ) - 1 := by omega
  have hzpos : 0 ≤ z := by
    by_contra hneg
    push_neg at hneg
    have hz1 : z ≤ -1 := by omega
    have : m - y * c ≤ -(b : ℤ) := by
      calc m - y * c = b * z := hz
        _ ≤ b * (-1) := by
            exact mul_le_mul_of_nonneg_left hz1 (le_of_lt hb')
        _ = -(b : ℤ) := by ring
    nlinarith [hm, hyle, hz]
  refine ⟨y, z.toNat, ?_⟩
  rw [Int.toNat_of_nonneg hzpos]
  linarith [hz]

/-- **IMO 1983, Problem 3.**  For positive integers `a`, `b`, `c` that are pairwise coprime,
`2abc - ab - bc - ca` is the largest integer that cannot be written as `x*bc + y*ca + z*ab`
with `x, y, z` non-negative integers. -/
theorem imo1983_p3 (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b) (hbc : Nat.Coprime b c) (hca : Nat.Coprime c a) :
    IsGreatest {n : ℤ | ¬ ∃ x y z : ℕ, n = x * (b * c) + y * (c * a) + z * (a * b)}
      (2 * a * b * c - a * b - b * c - c * a) := by
  have ha' : (0 : ℤ) < a := by exact_mod_cast ha
  have hb' : (0 : ℤ) < b := by exact_mod_cast hb
  have hc' : (0 : ℤ) < c := by exact_mod_cast hc
  constructor
  · -- `2abc - ab - bc - ca` is not representable
    rintro ⟨x, y, z, hxyz⟩
    -- `a ∣ x + 1`
    have hxa : (a : ℤ) ≤ (x : ℤ) + 1 := by
      have hdvd : (a : ℤ) ∣ ((x : ℤ) + 1) * ((b : ℤ) * c) := by
        refine ⟨2 * b * c - b - c - y * c - z * b, ?_⟩
        linarith [hxyz, (by ring : ((x : ℤ) + 1) * ((b : ℤ) * c)
          = (x : ℤ) * (b * c) + b * c)]
      have hcop : IsCoprime (a : ℤ) ((b : ℤ) * c) := by
        have : Nat.Coprime a (b * c) := Nat.Coprime.mul_right hab hca.symm
        exact_mod_cast Nat.isCoprime_iff_coprime.mpr this
      have := hcop.dvd_of_dvd_mul_right hdvd
      exact Int.le_of_dvd (by positivity) this
    have hyb : (b : ℤ) ≤ (y : ℤ) + 1 := by
      have hdvd : (b : ℤ) ∣ ((y : ℤ) + 1) * ((c : ℤ) * a) := by
        refine ⟨2 * a * c - a - c - x * c - z * a, ?_⟩
        linarith [hxyz, (by ring : ((y : ℤ) + 1) * ((c : ℤ) * a)
          = (y : ℤ) * (c * a) + c * a)]
      have hcop : IsCoprime (b : ℤ) ((c : ℤ) * a) := by
        have : Nat.Coprime b (c * a) := Nat.Coprime.mul_right hbc hab.symm
        exact_mod_cast Nat.isCoprime_iff_coprime.mpr this
      have := hcop.dvd_of_dvd_mul_right hdvd
      exact Int.le_of_dvd (by positivity) this
    have hzc : (c : ℤ) ≤ (z : ℤ) + 1 := by
      have hdvd : (c : ℤ) ∣ ((z : ℤ) + 1) * ((a : ℤ) * b) := by
        refine ⟨2 * a * b - a - b - x * b - y * a, ?_⟩
        linarith [hxyz, (by ring : ((z : ℤ) + 1) * ((a : ℤ) * b)
          = (z : ℤ) * (a * b) + a * b)]
      have hcop : IsCoprime (c : ℤ) ((a : ℤ) * b) := by
        have : Nat.Coprime c (a * b) := Nat.Coprime.mul_right hca hbc.symm
        exact_mod_cast Nat.isCoprime_iff_coprime.mpr this
      have := hcop.dvd_of_dvd_mul_right hdvd
      exact Int.le_of_dvd (by positivity) this
    nlinarith [hxyz, hxa, hyb, hzc, mul_pos (mul_pos ha' hb') hc',
      mul_pos hb' hc', mul_pos hc' ha', mul_pos ha' hb']
  · -- every larger integer is representable
    rintro n hn
    by_contra hlt
    push_neg at hlt
    apply hn
    -- choose `x < a` with `a ∣ n - x * (b*c)`
    have hcop : IsCoprime ((b : ℤ) * c) (a : ℤ) := by
      have : Nat.Coprime (b * c) a := Nat.Coprime.mul_left (hab.symm) hca
      exact_mod_cast Nat.isCoprime_iff_coprime.mpr this
    obtain ⟨x, hxlt, hdvd⟩ := exists_small_nat_smul_congr ha' hcop n
    obtain ⟨m, hm⟩ := hdvd
    have hxle : (x : ℤ) ≤ (a : ℤ) - 1 := by omega
    have hmge : ((b : ℤ) - 1) * ((c : ℤ) - 1) ≤ m := by
      have key : (a : ℤ) * (((b : ℤ) - 1) * ((c : ℤ) - 1) - 1) < a * m := by
        nlinarith [hm, hxle, hlt, mul_pos hb' hc']
      have := lt_of_mul_lt_mul_left key ha'.le
      linarith
    obtain ⟨y, z, hyz⟩ := exists_repr_of_ge hb hbc m hmge
    exact ⟨x, y, z, by rw [hyz] at hm; linarith [hm]⟩

end Imo1983P3
