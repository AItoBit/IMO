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

/-!
# IMO 1981 Problem 4

(a) For which values of `n > 2` is there a set of `n` consecutive positive integers such that the
largest number in the set is a divisor of the least common multiple of the remaining `n - 1`
numbers?  Answer: exactly the `n` with `n ≥ 4`.

(b) For which values of `n > 2` is there exactly one such set?  Answer: only `n = 4`
(the set `{3, 4, 5, 6}`).
-/

namespace IMO1981P4

/-- `ConsecLcmProp n m` says that the set of `n` consecutive positive integers
`{m, m+1, ..., m+n-1}` has the property that its largest element `m + n - 1` divides the least
common multiple of the other `n - 1` elements. -/
def ConsecLcmProp (n m : ℕ) : Prop :=
  0 < m ∧ (m + n - 1) ∣ (Finset.range (n - 1)).lcm (fun i => m + i)

/-- The lcm of `n` consecutive integers starting at `m` divides their product. -/
lemma lcm_range_dvd_prod (N m : ℕ) :
    (Finset.range N).lcm (fun i => m + i) ∣ ∏ i ∈ Finset.range N, (m + i) :=
  Finset.lcm_dvd (fun _ hi => Finset.dvd_prod_of_mem _ hi)

/-- Construction: if `a, b` are coprime, both at most `N`, and `m + N = a * b`, then the set
`{m, ..., m + N}` of `N + 1` consecutive positive integers has the required property. -/
lemma consecLcmProp_of_coprime {N a b m : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hab : Nat.Coprime a b) (haN : a ≤ N) (hbN : b ≤ N) (hm : m + N = a * b) (hm0 : 0 < m) :
    ConsecLcmProp (N + 1) m := by
  refine ⟨hm0, ?_⟩
  have hsimp : m + (N + 1) - 1 = a * b := by omega
  have hNa : N + 1 - 1 = N := by omega
  rw [hsimp, hNa]
  -- the element `m + (N - a)` equals `a * (b - 1)`, hence is divisible by `a`
  have hA : a ∣ (Finset.range N).lcm (fun i => m + i) := by
    refine dvd_trans ?_ (Finset.dvd_lcm (f := fun i => m + i) (Finset.mem_range.mpr
      (by omega : N - a < N)))
    show a ∣ m + (N - a)
    have hval : m + (N - a) = a * (b - 1) := by
      have : a * (b - 1) = a * b - a := by
        cases b with
        | zero => omega
        | succ c => simp [Nat.mul_succ]
      omega
    rw [hval]
    exact Dvd.intro _ rfl
  -- likewise `m + (N - b) = b * (a - 1)` is divisible by `b`
  have hB : b ∣ (Finset.range N).lcm (fun i => m + i) := by
    refine dvd_trans ?_ (Finset.dvd_lcm (f := fun i => m + i) (Finset.mem_range.mpr
      (by omega : N - b < N)))
    show b ∣ m + (N - b)
    have hval : m + (N - b) = b * (a - 1) := by
      have hba : b * a = a * b := Nat.mul_comm _ _
      have : b * (a - 1) = b * a - b := by
        cases a with
        | zero => omega
        | succ c => simp [Nat.mul_succ]
      omega
    rw [hval]
    exact Dvd.intro _ rfl
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hab hA hB

/-- No set of three consecutive positive integers has the property: the largest element `k`
divides `(k-1)(k-2) ≡ 2`, forcing `k ∣ 2`, impossible since `k ≥ 3`. -/
lemma not_consecLcmProp_three (m : ℕ) : ¬ ConsecLcmProp 3 m := by
  rintro ⟨hm, hdvd⟩
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  have hprod : (j + 1 + 3 - 1) ∣ ∏ i ∈ Finset.range (3 - 1), (j + 1 + i) :=
    hdvd.trans (lcm_range_dvd_prod _ _)
  norm_num [Finset.prod_range_succ] at hprod
  have hprod' : (j + 3) ∣ (j + 1) * (j + 2) := by
    have : (j + 1) * (j + 1 + 1) = (j + 1) * (j + 2) := by ring
    rwa [this] at hprod
  have key : (j + 3) ∣ 2 := by
    have h1 : (j + 1) * (j + 2) = (j + 3) * j + 2 := by ring
    have h2 : (j + 3) ∣ (j + 3) * j := Dvd.intro _ rfl
    exact (Nat.dvd_add_right h2).mp (h1 ▸ hprod')
  have := Nat.le_of_dvd (by norm_num) key
  omega

/-- For four consecutive positive integers, the only set with the property is `{3, 4, 5, 6}`:
the largest element `k` divides `(k-1)(k-2)(k-3) ≡ -6`, so `k ∣ 6` and `k ≥ 4` gives `k = 6`. -/
lemma consecLcmProp_four_iff (m : ℕ) : ConsecLcmProp 4 m ↔ m = 3 := by
  constructor
  · rintro ⟨hm, hdvd⟩
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    have hprod : (j + 1 + 4 - 1) ∣ ∏ i ∈ Finset.range (4 - 1), (j + 1 + i) :=
      hdvd.trans (lcm_range_dvd_prod _ _)
    norm_num [Finset.prod_range_succ] at hprod
    have hprod' : (j + 4) ∣ (j + 1) * (j + 2) * (j + 3) := by
      have : (j + 1) * (j + 1 + 1) * (j + 1 + 2) = (j + 1) * (j + 2) * (j + 3) := by ring
      rwa [this] at hprod
    have key : (j + 4) ∣ 6 := by
      have h1 : (j + 4) * (j * j + 2 * j + 3) = (j + 1) * (j + 2) * (j + 3) + 6 := by ring
      have h2 : (j + 4) ∣ (j + 4) * (j * j + 2 * j + 3) := Dvd.intro _ rfl
      have h3 : (j + 4) ∣ (j + 1) * (j + 2) * (j + 3) + 6 := h1 ▸ h2
      exact (Nat.dvd_add_right hprod').mp h3
    have hle : j ≤ 2 := by have := Nat.le_of_dvd (by norm_num) key; omega
    interval_cases j <;> revert key <;> decide
  · rintro rfl
    exact consecLcmProp_of_coprime (N := 3) (a := 3) (b := 2) (by norm_num) (by norm_num)
      (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **IMO 1981, Problem 4 (a).** For `n > 2`, a set of `n` consecutive positive integers whose
largest element divides the lcm of the others exists exactly when `n ≥ 4`. -/
theorem imo1981_p4a (n : ℕ) (hn : 2 < n) : (∃ m, ConsecLcmProp n m) ↔ 4 ≤ n := by
  constructor
  · rintro ⟨m, hmp⟩
    by_contra h
    rw [show n = 3 by omega] at hmp
    exact not_consecLcmProp_three m hmp
  · intro h
    obtain ⟨t, rfl⟩ : ∃ t, n = t + 4 := ⟨n - 4, by omega⟩
    refine ⟨(t + 3) * (t + 1), ?_⟩
    have hco : Nat.Coprime (t + 3) (t + 2) := by
      show Nat.Coprime (t + 2 + 1) (t + 2); simp [Nat.Coprime]
    have := consecLcmProp_of_coprime (N := t + 3) (a := t + 3) (b := t + 2)
      (m := (t + 3) * (t + 1)) (by omega) (by omega) hco (by omega) (by omega) (by ring)
      (by positivity)
    simpa using this

/-- **IMO 1981, Problem 4 (b).** For `n > 2`, there is exactly one set of `n` consecutive positive
integers with the stated property precisely when `n = 4`. -/
theorem imo1981_p4b (n : ℕ) (hn : 2 < n) : (∃! m, ConsecLcmProp n m) ↔ n = 4 := by
  constructor
  · rintro ⟨m, hm, huniq⟩
    rcases Nat.lt_or_ge n 4 with h | h
    · rw [show n = 3 by omega] at hm
      exact absurd hm (not_consecLcmProp_three m)
    rcases Nat.lt_or_ge n 5 with h5 | h5
    · omega
    · exfalso
      obtain ⟨t, rfl⟩ : ∃ t, n = t + 5 := ⟨n - 5, by omega⟩
      have hco1 : Nat.Coprime (t + 4) (t + 3) := by
        show Nat.Coprime (t + 3 + 1) (t + 3); simp [Nat.Coprime]
      have hco2 : Nat.Coprime (t + 3) (t + 2) := by
        show Nat.Coprime (t + 2 + 1) (t + 2); simp [Nat.Coprime]
      have h1 : ConsecLcmProp (t + 5) ((t + 4) * (t + 2)) := by
        have := consecLcmProp_of_coprime (N := t + 4) (a := t + 4) (b := t + 3)
          (m := (t + 4) * (t + 2)) (by omega) (by omega) hco1 (by omega) (by omega) (by ring)
          (by positivity)
        simpa using this
      have h2 : ConsecLcmProp (t + 5) (t * t + 4 * t + 2) := by
        have := consecLcmProp_of_coprime (N := t + 4) (a := t + 3) (b := t + 2)
          (m := t * t + 4 * t + 2) (by omega) (by omega) hco2 (by omega) (by omega) (by ring)
          (by positivity)
        simpa using this
      have e1 := huniq _ h1
      have e2 := huniq _ h2
      nlinarith [e1, e2]
  · rintro rfl
    exact ⟨3, (consecLcmProp_four_iff 3).mpr rfl, fun m hm => (consecLcmProp_four_iff m).mp hm⟩

end IMO1981P4
