/-
# IMO 1973, Problem 6

Let `a₁, …, aₙ` be positive reals and `0 < q < 1`.  Find `b₁, …, bₙ` with

* (a) `aₖ < bₖ` for all `k`;
* (b) `q < b_{k+1} / bₖ < 1/q` for `k = 1, …, n-1`;
* (c) `b₁ + ⋯ + bₙ < (1+q)/(1-q) · (a₁ + ⋯ + aₙ)`.

## Modelling

Indices run over `Finset.range n` with `a : ℕ → ℝ` positive.  Condition (b) is
stated multiplicatively as `q * bₖ < b_{k+1}` and `q * b_{k+1} < bₖ`; together
with `0 < bₖ` (also part of the conclusion, since the problem asks for positive
`bₖ`) this is exactly `q < b_{k+1}/bₖ < 1/q`.

## Proof

The AoPS construction is `cₖ = ∑ⱼ q^{|k-j|} aⱼ`.  Writing `dd k j = |k - j|`
(as truncated subtraction `(k-j) + (j-k)`):

* (a) `aₖ ≤ cₖ`, because the `j = k` term is `q⁰ aₖ = aₖ` and the rest is ≥ 0.
* (b) `q * cₖ < c_{k+1}`: term by term, `dd (k+1) j ≤ dd k j + 1`, so
  `q^{dd k j + 1} ≤ q^{dd (k+1) j}`, and at `j = k+1` the exponents are `2` and
  `0`, giving a strict inequality.  Symmetrically for `q * c_{k+1} < cₖ`.
  This replaces the `bₖ = X + Y`, `b_{k+1} = qX + Y/q` bookkeeping of the
  write-up by a single termwise comparison.
* (c) swapping the two sums, `∑ₖ cₖ = ∑ⱼ (∑ₖ q^{dd k j}) aⱼ`, and for each `j`
  the inner sum splits as `∑_{i<j+1} qⁱ + q ∑_{i<n-j-1} qⁱ < 1/(1-q) + q/(1-q)`.

The construction only gives `aₖ ≤ cₖ`, with equality when `n = 1`.  Since (c) is
*strict* for the `cₖ`, there is room to scale: with `A = ∑ aₖ`, `C = ∑ cₖ` and
`R = (1+q)/(1-q)`, put

  `μ = (R·A + C) / (2C) > 1`,   `bₖ = μ cₖ`.

Then (a) becomes strict, (b) is scale invariant, and `∑ bₖ = (R·A + C)/2 < R·A`.
-/

import Mathlib

namespace Imo1973P6

/-! ### Powers of `q` -/

private lemma pow_le_one_aux {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) : ∀ d : ℕ, q ^ d ≤ 1 := by
  intro d
  induction d with
  | zero => simp
  | succ m ih =>
    rw [pow_succ]
    nlinarith [pow_nonneg h0 m]

private lemma pow_lt_one_aux {q : ℝ} (h0 : 0 ≤ q) (h1 : q < 1) {d : ℕ} (hd : 0 < d) :
    q ^ d < 1 := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  rw [pow_succ]
  nlinarith [pow_le_one_aux h0 h1.le e, pow_nonneg h0 e]

private lemma qpow_le {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) {m m' : ℕ} (h : m ≤ m') :
    q ^ m' ≤ q ^ m := by
  obtain ⟨d, rfl⟩ : ∃ d, m' = m + d := ⟨m' - m, by omega⟩
  rw [pow_add]
  nlinarith [pow_le_one_aux h0 h1 d, pow_nonneg h0 m]

private lemma qpow_lt {q : ℝ} (h0 : 0 < q) (h1 : q < 1) {m m' : ℕ} (h : m < m') :
    q ^ m' < q ^ m := by
  obtain ⟨d, rfl⟩ : ∃ d, m' = m + d := ⟨m' - m, by omega⟩
  rw [pow_add]
  have hd : 0 < d := by omega
  nlinarith [pow_lt_one_aux h0.le h1 hd, pow_pos h0 m]

private lemma geom_id (q : ℝ) : ∀ m : ℕ,
    (1 - q) * ∑ i ∈ Finset.range m, q ^ i = 1 - q ^ m := by
  intro m
  induction m with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, mul_add, ih, pow_succ]
    ring

private lemma geom_lt {q : ℝ} (h0 : 0 < q) (m : ℕ) :
    (1 - q) * ∑ i ∈ Finset.range m, q ^ i < 1 := by
  rw [geom_id]
  have := pow_pos h0 m
  linarith

/-! ### The construction -/

/-- `dd k j = |k - j|`. -/
private def dd (k j : ℕ) : ℕ := (k - j) + (j - k)

private lemma dd_self (k : ℕ) : dd k k = 0 := by simp [dd]

private lemma dd_succ_le (k j : ℕ) : dd (k + 1) j ≤ dd k j + 1 := by simp only [dd]; omega

private lemma dd_le_succ (k j : ℕ) : dd k j ≤ dd (k + 1) j + 1 := by simp only [dd]; omega

/-- `cₖ = ∑ⱼ q^{|k-j|} aⱼ`. -/
private noncomputable def cc (n : ℕ) (q : ℝ) (a : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, q ^ dd k j * a j

private lemma cc_pos {n : ℕ} {q : ℝ} {a : ℕ → ℝ} (hn : 0 < n) (hq0 : 0 < q)
    (ha : ∀ j, 0 < a j) (k : ℕ) : 0 < cc n q a k := by
  refine Finset.sum_pos (fun j _ => mul_pos (pow_pos hq0 _) (ha j)) ?_
  exact Finset.nonempty_range_iff.mpr (by omega)

private lemma le_cc {n : ℕ} {q : ℝ} {a : ℕ → ℝ} (hq0 : 0 < q) (ha : ∀ j, 0 < a j)
    {k : ℕ} (hk : k < n) : a k ≤ cc n q a k := by
  have h := Finset.single_le_sum
    (f := fun j => q ^ dd k j * a j)
    (fun j _ => le_of_lt (mul_pos (pow_pos hq0 _) (ha j)))
    (Finset.mem_range.mpr hk)
  rw [dd_self, pow_zero, one_mul] at h
  exact h

private lemma cc_lower {n : ℕ} {q : ℝ} {a : ℕ → ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (ha : ∀ j, 0 < a j) {k : ℕ} (hk : k + 1 < n) :
    q * cc n q a k < cc n q a (k + 1) := by
  have hmul : q * cc n q a k = ∑ j ∈ Finset.range n, q ^ (dd k j + 1) * a j := by
    unfold cc
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pow_succ]
    ring
  rw [hmul]
  unfold cc
  refine Finset.sum_lt_sum (fun j _ => ?_) ⟨k + 1, Finset.mem_range.mpr hk, ?_⟩
  · exact mul_le_mul_of_nonneg_right
      (qpow_le hq0.le hq1.le (dd_succ_le k j)) (ha j).le
  · refine mul_lt_mul_of_pos_right (qpow_lt hq0 hq1 ?_) (ha (k + 1))
    simp only [dd]; omega

private lemma cc_upper {n : ℕ} {q : ℝ} {a : ℕ → ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (ha : ∀ j, 0 < a j) {k : ℕ} (hk : k + 1 < n) :
    q * cc n q a (k + 1) < cc n q a k := by
  have hmul : q * cc n q a (k + 1) = ∑ j ∈ Finset.range n, q ^ (dd (k + 1) j + 1) * a j := by
    unfold cc
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pow_succ]
    ring
  rw [hmul]
  unfold cc
  refine Finset.sum_lt_sum (fun j _ => ?_) ⟨k, Finset.mem_range.mpr (by omega), ?_⟩
  · exact mul_le_mul_of_nonneg_right
      (qpow_le hq0.le hq1.le (dd_le_succ k j)) (ha j).le
  · refine mul_lt_mul_of_pos_right (qpow_lt hq0 hq1 ?_) (ha k)
    simp only [dd]; omega

/-- The inner sum `∑ₖ q^{|k-j|}` is bounded by `(1+q)/(1-q)`. -/
private lemma inner_bound {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {n j : ℕ} (hj : j < n) :
    ∑ k ∈ Finset.range n, q ^ dd k j < (1 + q) / (1 - q) := by
  have hq' : (0:ℝ) < 1 - q := by linarith
  have hsplit : ∑ k ∈ Finset.range n, q ^ dd k j
      = (∑ k ∈ (Finset.range n).filter (fun k => k ≤ j), q ^ dd k j)
        + (∑ k ∈ (Finset.range n).filter (fun k => ¬ k ≤ j), q ^ dd k j) :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hAset : (Finset.range n).filter (fun k => k ≤ j) = Finset.range (j + 1) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  have hBset : (Finset.range n).filter (fun k => ¬ k ≤ j) = Finset.Ico (j + 1) n := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  have hA : ∑ k ∈ Finset.range (j + 1), q ^ dd k j
      = ∑ i ∈ Finset.range (j + 1), q ^ i := by
    rw [← Finset.sum_range_reflect (fun i => q ^ i) (j + 1)]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    rw [show dd k j = j + 1 - 1 - k from by simp only [dd]; omega]
  have hB : ∑ k ∈ Finset.Ico (j + 1) n, q ^ dd k j
      = q * ∑ i ∈ Finset.range (n - (j + 1)), q ^ i := by
    rw [Finset.sum_Ico_eq_sum_range, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show dd (j + 1 + i) j = i + 1 from by simp only [dd]; omega, pow_succ]
    ring
  have hgA := geom_lt hq0 (j + 1)
  have hgB := geom_lt hq0 (n - (j + 1))
  have hR : (1 + q) / (1 - q) * (1 - q) = 1 + q := by field_simp
  refine lt_of_mul_lt_mul_right ?_ hq'.le
  rw [hR, hsplit, hAset, hBset, hA, hB]
  nlinarith [hgA, hgB, hq0]

/-! ### The theorem -/

/-- **IMO 1973, Problem 6.** -/
theorem imo1973_p6 (n : ℕ) (hn : 0 < n) (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (a : ℕ → ℝ) (ha : ∀ j, 0 < a j) :
    ∃ b : ℕ → ℝ,
      (∀ k, k < n → 0 < b k) ∧
      (∀ k, k < n → a k < b k) ∧
      (∀ k, k + 1 < n → q * b k < b (k + 1) ∧ q * b (k + 1) < b k) ∧
      (∑ k ∈ Finset.range n, b k) < (1 + q) / (1 - q) * ∑ k ∈ Finset.range n, a k := by
  have hq' : (0:ℝ) < 1 - q := by linarith
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = ∑ k ∈ Finset.range n, a k := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = ∑ k ∈ Finset.range n, cc n q a k := ⟨_, rfl⟩
  have hApos : 0 < A := by
    rw [hA]
    exact Finset.sum_pos (fun j _ => ha j) (Finset.nonempty_range_iff.mpr (by omega))
  have hCpos : 0 < C := by
    rw [hC]
    exact Finset.sum_pos (fun j _ => cc_pos hn hq0 ha j)
      (Finset.nonempty_range_iff.mpr (by omega))
  -- condition (c) for the unscaled construction
  have hswap : ∑ k ∈ Finset.range n, cc n q a k
      = ∑ j ∈ Finset.range n, (∑ k ∈ Finset.range n, q ^ dd k j) * a j := by
    unfold cc
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => (Finset.sum_mul _ _ _).symm
  have hkey : C < (1 + q) / (1 - q) * A := by
    rw [hC, hA, hswap, Finset.mul_sum]
    refine Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.mpr (by omega)) ?_
    intro j hj
    exact mul_lt_mul_of_pos_right (inner_bound hq0 hq1 (Finset.mem_range.mp hj)) (ha j)
  -- the scaling factor
  obtain ⟨μ, hμ⟩ : ∃ μ : ℝ, μ = ((1 + q) / (1 - q) * A + C) / (2 * C) := ⟨_, rfl⟩
  have h2C : (0:ℝ) < 2 * C := by linarith
  have hμmul : μ * (2 * C) = (1 + q) / (1 - q) * A + C := by
    rw [hμ]; field_simp
  have hμ1 : 1 < μ := by
    refine lt_of_mul_lt_mul_right ?_ h2C.le
    rw [hμmul]
    linarith
  have hμpos : 0 < μ := by linarith
  refine ⟨fun k => μ * cc n q a k, ?_, ?_, ?_, ?_⟩
  · intro k _
    exact mul_pos hμpos (cc_pos hn hq0 ha k)
  · intro k hk
    have h1 := le_cc hq0 ha hk
    have h2 := cc_pos (n := n) hn hq0 ha k
    nlinarith
  · intro k hk
    constructor
    · have := cc_lower hq0 hq1 ha hk
      nlinarith
    · have := cc_upper hq0 hq1 ha hk
      nlinarith
  · have hsum : ∑ k ∈ Finset.range n, μ * cc n q a k = μ * C := by
      rw [hC, Finset.mul_sum]
    rw [hsum, ← hA]
    -- `μ * C = (R A + C)/2 < R A`
    have : μ * C * 2 = (1 + q) / (1 - q) * A + C := by
      rw [← hμmul]; ring
    linarith

end Imo1973P6
