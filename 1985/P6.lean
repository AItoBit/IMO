import Mathlib

/-!
# IMO 1985, Problem 6

For every real `x₁` build `x₁, x₂, …` by `x_{n+1} = x_n (x_n + 1/n)`, `n ≥ 1`.
Prove there is exactly one `x₁` with `0 < x_n < x_{n+1} < 1` for every `n`.

Internally we use `s t k = x_{k+1}` when `x₁ = t`.

* A parameter `t` is *good* iff `1 - 1/(k+1) < s t k < 1` for all `k`.
* Existence: the closed sets `K n = {t | ∀ m ≤ n, 1 - 1/(m+1) ≤ s t m ≤ 1}` are nested,
  nonempty (intermediate value theorem) and compact, so they share a point.
* Uniqueness: if `t < u` are both good, `s u k - s t k ≥ u - t` for all `k`,
  but it is also `< 1/(k+1)`.
-/

open Set

namespace Imo1985P6

/-- `s t k` is `x_{k+1}` when `x₁ = t`. -/
noncomputable def s (t : ℝ) : ℕ → ℝ
  | 0 => t
  | k + 1 => s t k * (s t k + 1 / ((k : ℝ) + 1))

@[simp] lemma s_zero (t : ℝ) : s t 0 = t := rfl

lemma s_succ (t : ℝ) (k : ℕ) : s t (k + 1) = s t k * (s t k + 1 / ((k : ℝ) + 1)) := rfl

lemma e_bounds (k : ℕ) : 0 < 1 / ((k : ℝ) + 1) ∧ 1 / ((k : ℝ) + 1) ≤ 1 := by
  constructor
  · positivity
  · exact div_le_one_of_le₀ (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]) (by positivity)

lemma s_continuous (k : ℕ) : Continuous fun t => s t k := by
  induction k with
  | zero =>
    simp only [s_zero]
    exact continuous_id
  | succ k ih =>
    simp only [s_succ]
    exact ih.mul (ih.add continuous_const)

lemma s_nonneg {t : ℝ} (ht : 0 ≤ t) (k : ℕ) : 0 ≤ s t k := by
  induction k with
  | zero => simpa using ht
  | succ k ih =>
    rw [s_succ]
    exact mul_nonneg ih (add_nonneg ih (e_bounds k).1.le)

lemma s_zero_param (k : ℕ) : s 0 k = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [s_succ, ih, zero_mul]

lemma one_le_s_one (k : ℕ) : 1 ≤ s 1 k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [s_succ]
    have he := (e_bounds k).1
    nlinarith [mul_nonneg (sub_nonneg.2 ih) (add_nonneg (by linarith : (0 : ℝ) ≤ s 1 k) he.le)]

/-- Once a term drops below its window, all later terms stay below theirs. -/
lemma small_persist {t : ℝ} (ht : 0 ≤ t) {m : ℕ} (hm : s t m < 1 - 1 / ((m : ℝ) + 1)) :
    ∀ k, m ≤ k → s t k < 1 - 1 / ((k : ℝ) + 1) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact hm
  | succ k hmk ih =>
    have h0 := s_nonneg ht k
    have hlt : 1 / ((k : ℝ) + 1 + 1) < 1 / ((k : ℝ) + 1) :=
      one_div_lt_one_div_of_lt (by positivity) (by linarith)
    rw [s_succ, Nat.cast_add_one]
    nlinarith [mul_nonneg h0 (sub_pos.2 ih).le]

/-- Once a term exceeds `1`, all later terms exceed `1`. -/
lemma big_persist {t : ℝ} {m : ℕ} (hm : 1 < s t m) : ∀ k, m ≤ k → 1 < s t k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact hm
  | succ k hmk ih =>
    rw [s_succ]
    have he := (e_bounds k).1
    nlinarith [mul_pos (sub_pos.2 ih) (by linarith : (0 : ℝ) < s t k + 1 / ((k : ℝ) + 1))]

/-- Good parameters: every term lies strictly inside its window. -/
abbrev Good (t : ℝ) : Prop := ∀ k : ℕ, 1 - 1 / ((k : ℝ) + 1) < s t k ∧ s t k < 1

lemma good_imp_cond {t : ℝ} (ht : Good t) (k : ℕ) :
    0 < s t k ∧ s t k < s t (k + 1) ∧ s t (k + 1) < 1 := by
  obtain ⟨h1, _⟩ := ht k
  have he := e_bounds k
  have hpos : 0 < s t k := by linarith [he.2]
  refine ⟨hpos, ?_, (ht (k + 1)).2⟩
  rw [s_succ]
  nlinarith [mul_pos hpos (by linarith : (0 : ℝ) < s t k + 1 / ((k : ℝ) + 1) - 1)]

lemma cond_imp_good {t : ℝ} (h : ∀ k, 0 < s t k ∧ s t k < s t (k + 1) ∧ s t (k + 1) < 1) :
    Good t := by
  intro k
  obtain ⟨hpos, hlt, hlt1⟩ := h k
  refine ⟨?_, hlt.trans hlt1⟩
  by_contra hc
  push_neg at hc
  rw [s_succ] at hlt
  nlinarith [mul_nonneg hpos.le (sub_nonneg.2 hc)]

/-! ### Existence -/

/-- Parameters whose first `n + 1` terms lie in the closed windows. -/
def K (n : ℕ) : Set ℝ :=
  ⋂ m, ⋂ (_ : m ≤ n), {t | 1 - 1 / ((m : ℝ) + 1) ≤ s t m ∧ s t m ≤ 1}

lemma K_closed (n : ℕ) : IsClosed (K n) := by
  unfold K
  apply isClosed_iInter
  intro m
  apply isClosed_iInter
  intro _
  have h1 : IsClosed {t : ℝ | 1 - 1 / ((m : ℝ) + 1) ≤ s t m} :=
    isClosed_le continuous_const (s_continuous m)
  have h2 : IsClosed {t : ℝ | s t m ≤ 1} := isClosed_le (s_continuous m) continuous_const
  exact h1.inter h2

lemma K_antitone (i : ℕ) : K (i + 1) ⊆ K i := by
  intro t ht
  simp only [K, mem_iInter, mem_setOf_eq] at ht ⊢
  intro m hm
  exact ht m (by omega)

lemma K_zero_compact : IsCompact (K 0) := by
  refine (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).of_isClosed_subset (K_closed 0) ?_
  intro t ht
  simp only [K, mem_iInter, mem_setOf_eq] at ht
  simpa using ht 0 le_rfl

lemma K_nonempty (n : ℕ) : (K n).Nonempty := by
  have he := e_bounds n
  have hc : ContinuousOn (fun t => s t n) (Icc 0 1) := (s_continuous n).continuousOn
  have hmem : 1 - 1 / ((n : ℝ) + 1) ∈ Icc (s 0 n) (s 1 n) := by
    rw [s_zero_param, mem_Icc]
    have := one_le_s_one n
    constructor <;> linarith [he.1, he.2]
  obtain ⟨t, htI, hteq⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hc hmem
  have hteq' : s t n = 1 - 1 / ((n : ℝ) + 1) := hteq
  refine ⟨t, ?_⟩
  simp only [K, mem_iInter, mem_setOf_eq]
  intro m hm
  constructor
  · by_contra h
    push_neg at h
    have := small_persist htI.1 h n hm
    linarith
  · by_contra h
    push_neg at h
    have := big_persist h n hm
    linarith

lemma exists_good : ∃ t, Good t := by
  obtain ⟨t, ht⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    K K_antitone K_nonempty K_zero_compact K_closed
  simp only [mem_iInter] at ht
  have hK : ∀ m : ℕ, 1 - 1 / ((m : ℝ) + 1) ≤ s t m ∧ s t m ≤ 1 := by
    intro m
    have hm := ht m
    simp only [K, mem_iInter, mem_setOf_eq] at hm
    exact hm m le_rfl
  refine ⟨t, fun k => ⟨?_, ?_⟩⟩
  · rcases (hK k).1.lt_or_eq with h | h
    · exact h
    · exfalso
      have h1 := (hK (k + 1)).1
      have hlt : 1 / ((k : ℝ) + 1 + 1) < 1 / ((k : ℝ) + 1) :=
        one_div_lt_one_div_of_lt (by positivity) (by linarith)
      rw [s_succ, ← h, Nat.cast_add_one] at h1
      nlinarith
  · rcases (hK k).2.lt_or_eq with h | h
    · exact h
    · exfalso
      have h1 := (hK (k + 1)).2
      rw [s_succ, h] at h1
      have := (e_bounds k).1
      linarith

/-! ### Uniqueness -/

lemma good_unique_aux {t u : ℝ} (ht : Good t) (hu : Good u) (htu : t < u) : False := by
  have key : ∀ k, u - t ≤ s u k - s t k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      simp only [s_succ]
      have h1 := (ht k).1
      have h2 := (hu k).1
      have he := e_bounds k
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ s u k - s t k)
        (by linarith : (0 : ℝ) ≤ s u k + s t k + 1 / ((k : ℝ) + 1) - 1)]
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.2 htu)
  have := key k
  have := (ht k).1
  have := (hu k).2
  linarith

lemma good_unique {t u : ℝ} (ht : Good t) (hu : Good u) : t = u := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact good_unique_aux ht hu h
  · exact good_unique_aux hu ht h

/-! ### Link with the sequence of the problem -/

lemma x_eq_s {a : ℝ} {x : ℕ → ℝ} (h1 : x 1 = a)
    (hx : ∀ n : ℕ, 1 ≤ n → x (n + 1) = x n * (x n + 1 / n)) (k : ℕ) :
    x (k + 1) = s a k := by
  induction k with
  | zero => simpa using h1
  | succ k ih => rw [hx (k + 1) (by omega), ih, s_succ, Nat.cast_add_one]

/-- **IMO 1985 P6.** -/
theorem imo1985_p6 :
    ∃! a : ℝ, ∀ x : ℕ → ℝ, x 1 = a → (∀ n : ℕ, 1 ≤ n → x (n + 1) = x n * (x n + 1 / n)) →
      ∀ n : ℕ, 1 ≤ n → 0 < x n ∧ x n < x (n + 1) ∧ x (n + 1) < 1 := by
  obtain ⟨a, ha⟩ := exists_good
  refine ⟨a, ?_, ?_⟩
  · intro x h1 hx n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [x_eq_s h1 hx k, x_eq_s h1 hx (k + 1)]
    exact good_imp_cond ha k
  · intro b hb
    have hrec : ∀ n : ℕ, 1 ≤ n → (fun n => s b (n - 1)) (n + 1) =
        (fun n => s b (n - 1)) n * ((fun n => s b (n - 1)) n + 1 / (n : ℝ)) := by
      intro n hn
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      simp [s_succ]
    have hgood : Good b := by
      apply cond_imp_good
      intro k
      have h := hb (fun n => s b (n - 1)) (by simp) hrec (k + 1) (by omega)
      simpa using h
    exact good_unique hgood ha

end Imo1985P6
