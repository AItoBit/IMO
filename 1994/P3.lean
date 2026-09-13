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
# IMO 1994 Problem 3

For any positive integer `k`, let `f k` be the number of elements in the set
`{k+1, k+2, ..., 2k}` whose base 2 representation has precisely three `1`s.

(a) For each positive integer `m` there is at least one `k` with `f k = m`.
(b) The positive integers `m` for which there is exactly one such `k` are exactly
    the numbers `n(n-1)/2 + 1` with `n ≥ 2`.
-/

namespace IMO1994P3

/-- The number of `1`s in the base 2 representation of `n`. -/
def onesCount (n : ℕ) : ℕ := (Nat.digits 2 n).sum

/-- `f k` is the number of elements of `{k+1, …, 2k}` whose base 2 representation
has precisely three `1`s. -/
def f (k : ℕ) : ℕ :=
  ((Finset.Ico (k + 1) (2 * k + 1)).filter (fun x => onesCount x = 3)).card

/-! ### Basic facts about `onesCount` -/

lemma onesCount_zero : onesCount 0 = 0 := rfl

lemma onesCount_bit (n r : ℕ) (hr : r < 2) : onesCount (2 * n + r) = onesCount n + r := by
  rcases Nat.eq_zero_or_pos (2 * n + r) with h | h
  · have hn : n = 0 := by omega
    have hr0 : r = 0 := by omega
    subst hn; subst hr0; simp [onesCount]
  · unfold onesCount
    rw [Nat.digits_def' (by norm_num : 1 < 2) h]
    have h1 : (2 * n + r) % 2 = r := by omega
    have h2 : (2 * n + r) / 2 = n := by omega
    rw [h1, h2]
    simp [List.sum_cons]
    omega

lemma onesCount_eq_zero_iff (n : ℕ) : onesCount n = 0 ↔ n = 0 := by
  constructor
  · induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro h
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · exact h0
      · have hd : n = 2 * (n / 2) + n % 2 := by omega
        rw [hd, onesCount_bit _ _ (by omega)] at h
        have h2 : onesCount (n / 2) = 0 := by omega
        have := ih (n / 2) (by omega) h2
        omega
  · rintro rfl; simp [onesCount]

lemma onesCount_eq_one_iff (n : ℕ) : onesCount n = 1 ↔ ∃ b : ℕ, n = 2 ^ b := by
  constructor
  · induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro h
      have h0 : 0 < n := by
        rcases Nat.eq_zero_or_pos n with rfl | h0
        · simp [onesCount] at h
        · exact h0
      have hd : n = 2 * (n / 2) + n % 2 := by omega
      rw [hd, onesCount_bit _ _ (by omega)] at h
      rcases (by omega : n % 2 = 0 ∨ n % 2 = 1) with hr | hr
      · have h2 : onesCount (n / 2) = 1 := by omega
        obtain ⟨b, hb⟩ := ih (n / 2) (by omega) h2
        exact ⟨b + 1, by rw [hd, hr, hb]; ring⟩
      · have h2 : onesCount (n / 2) = 0 := by omega
        have hz := (onesCount_eq_zero_iff _).mp h2
        exact ⟨0, by rw [hd, hr, hz]; ring⟩
  · rintro ⟨b, rfl⟩
    induction b with
    | zero => simp [onesCount]
    | succ b ih =>
      have h : (2:ℕ) ^ (b + 1) = 2 * 2 ^ b + 0 := by ring
      rw [h, onesCount_bit _ _ (by omega)]
      omega

lemma onesCount_pow_add (N i : ℕ) (hi : i < 2 ^ N) :
    onesCount (2 ^ N + i) = onesCount i + 1 := by
  induction N generalizing i with
  | zero =>
    have hi0 : i = 0 := by simpa using hi
    subst hi0
    simp [onesCount]
  | succ N ih =>
    have hi2 : i / 2 < 2 ^ N := by
      have h : (2:ℕ) ^ (N + 1) = 2 * 2 ^ N := by ring
      omega
    have hsplit : (2:ℕ) ^ (N + 1) + i = 2 * (2 ^ N + i / 2) + i % 2 := by
      have h : (2:ℕ) ^ (N + 1) = 2 * 2 ^ N := by ring
      omega
    have hi' : i = 2 * (i / 2) + i % 2 := by omega
    rw [hsplit, onesCount_bit _ _ (by omega), ih _ hi2]
    conv_rhs => rw [hi', onesCount_bit _ _ (by omega)]
    omega

lemma onesCount_pow (N : ℕ) : onesCount (2 ^ N) = 1 := by
  have h := onesCount_pow_add N 0 (by positivity)
  simpa [onesCount] using h

lemma onesCount_pow_add_one (N : ℕ) (hN : 1 ≤ N) : onesCount (2 ^ N + 1) = 2 := by
  have h1 : (1:ℕ) < 2 ^ N := by
    calc (1:ℕ) < 2 ^ 1 := by norm_num
    _ ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) hN
  have h := onesCount_pow_add N 1 h1
  simpa [onesCount] using h

/-! ### A closed formula for `f` -/

private def gg (x : ℕ) : ℕ := if onesCount x = 3 then 1 else 0

private lemma f_eq_sum (k : ℕ) : f k = ∑ x ∈ Finset.Ico (k + 1) (2 * k + 1), gg x := by
  rw [f, Finset.card_filter]; simp [gg]

/-- The recurrence `f (k+1) = f k + [2k+1 has three ones]`, for `k ≥ 1`. -/
lemma f_succ (k : ℕ) (hk : 1 ≤ k) :
    f (k + 1) = f k + (if onesCount k = 2 then 1 else 0) := by
  have h1 : (∑ x ∈ Finset.Ico (k+1) (2*k+1), gg x) + ∑ x ∈ Finset.Ico (2*k+1) (2*k+3), gg x
      = ∑ x ∈ Finset.Ico (k+1) (2*k+3), gg x :=
    Finset.sum_Ico_consecutive gg (by omega) (by omega)
  have h2 : (∑ x ∈ Finset.Ico (k+1) (k+2), gg x) + ∑ x ∈ Finset.Ico (k+2) (2*k+3), gg x
      = ∑ x ∈ Finset.Ico (k+1) (2*k+3), gg x :=
    Finset.sum_Ico_consecutive gg (by omega) (by omega)
  have hfk1 : f (k+1) = ∑ x ∈ Finset.Ico (k+2) (2*k+3), gg x := by
    rw [f_eq_sum]; congr 1
  have hmid : ∑ x ∈ Finset.Ico (2*k+1) (2*k+3), gg x = gg (2*k+1) + gg (2*k+2) := by
    have h : Finset.Ico (2*k+1) (2*k+3) = {2*k+1, 2*k+2} := by
      ext x; simp [Finset.mem_Ico]; omega
    rw [h, Finset.sum_pair (by omega)]
  have hsingle : ∑ x ∈ Finset.Ico (k+1) (k+2), gg x = gg (k+1) := by simp
  have hg : gg (2*k+2) = gg (k+1) := by
    have h : 2*k+2 = 2*(k+1) + 0 := by ring
    rw [gg, gg, h, onesCount_bit _ _ (by omega)]
    simp
  have hg1 : gg (2*k+1) = if onesCount k = 2 then 1 else 0 := by
    rw [gg, onesCount_bit k 1 (by omega)]
    by_cases h : onesCount k = 2 <;> simp [h]
  rw [f_eq_sum k] at *
  omega

/-- `f K` counts the numbers below `K` having exactly two binary ones. -/
lemma f_eq_card (K : ℕ) :
    f K = ((Finset.range K).filter (fun j => onesCount j = 2)).card := by
  induction K with
  | zero => decide
  | succ K ih =>
    rcases Nat.eq_zero_or_pos K with rfl | hK
    · decide
    · rw [f_succ K hK, ih, Finset.range_add_one, Finset.filter_insert]
      by_cases h : onesCount K = 2
      · rw [if_pos h, if_pos h, Finset.card_insert_of_notMem (by simp)]
      · rw [if_neg h, if_neg h]; simp

/-- The number of `j < 2 ^ N` with exactly `s` binary ones is `N.choose s`. -/
lemma card_ones_lt_pow (N s : ℕ) :
    ((Finset.range (2 ^ N)).filter (fun j => onesCount j = s)).card = N.choose s := by
  induction N generalizing s with
  | zero =>
    simp only [pow_zero, Finset.range_one, Finset.filter_singleton]
    rcases Nat.eq_zero_or_pos s with rfl | hs
    · simp [onesCount]
    · rw [if_neg (by simp [onesCount]; omega)]
      simp [Nat.choose_eq_zero_of_lt hs]
  | succ N ih =>
    have hsplit : Finset.range (2 ^ (N + 1))
        = Finset.range (2 ^ N) ∪ (Finset.range (2 ^ N)).image (fun i => 2 ^ N + i) := by
      ext x
      simp only [Finset.mem_range, Finset.mem_union, Finset.mem_image]
      constructor
      · intro hx
        rcases lt_or_ge x (2 ^ N) with h | h
        · exact Or.inl h
        · refine Or.inr ⟨x - 2 ^ N, ?_, by omega⟩
          have h2 : (2:ℕ) ^ (N + 1) = 2 * 2 ^ N := by ring
          omega
      · rintro (h | ⟨i, hi, rfl⟩)
        · have : (2:ℕ) ^ N ≤ 2 ^ (N + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        · have : (2:ℕ) ^ (N + 1) = 2 * 2 ^ N := by ring
          omega
    have hdisj : Disjoint (Finset.range (2 ^ N))
        ((Finset.range (2 ^ N)).image (fun i => 2 ^ N + i)) := by
      rw [Finset.disjoint_left]
      intro a ha hb
      simp only [Finset.mem_range] at ha
      simp only [Finset.mem_image, Finset.mem_range] at hb
      obtain ⟨i, hi, rfl⟩ := hb
      omega
    rw [hsplit, Finset.filter_union,
      Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hdisj), ih]
    have himg : ((Finset.range (2 ^ N)).image (fun i => 2 ^ N + i)).filter
          (fun j => onesCount j = s)
        = ((Finset.range (2 ^ N)).filter (fun i => onesCount i + 1 = s)).image
          (fun i => 2 ^ N + i) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range]
      constructor
      · rintro ⟨⟨i, hi, rfl⟩, hx⟩
        exact ⟨i, ⟨hi, by rw [onesCount_pow_add N i hi] at hx; exact hx⟩, rfl⟩
      · rintro ⟨i, ⟨hi, hx⟩, rfl⟩
        exact ⟨⟨i, hi, rfl⟩, by rw [onesCount_pow_add N i hi]; exact hx⟩
    rw [himg, Finset.card_image_of_injective _ (fun a b h => by omega)]
    cases s with
    | zero =>
      have hempty : ((Finset.range (2 ^ N)).filter (fun i => onesCount i + 1 = 0)) = ∅ := by simp
      rw [hempty]
      simp
    | succ t =>
      have heq : ((Finset.range (2 ^ N)).filter (fun i => onesCount i + 1 = t + 1))
          = ((Finset.range (2 ^ N)).filter (fun i => onesCount i = t)) := by
        apply Finset.filter_congr
        intro x _
        constructor <;> intro h <;> omega
      rw [heq, ih, Nat.choose_succ_succ' N t]
      omega

lemma f_mono : Monotone f := by
  intro a b hab
  rw [f_eq_card, f_eq_card]
  exact Finset.card_le_card (Finset.filter_subset_filter _ (by
    intro x hx; simp only [Finset.mem_range] at *; omega))

lemma f_succ_le (K : ℕ) : f (K + 1) ≤ f K + 1 := by
  rw [f_eq_card, f_eq_card, Finset.range_add_one, Finset.filter_insert]
  by_cases h : onesCount K = 2
  · rw [if_pos h]
    exact (Finset.card_insert_le _ _).trans (by omega)
  · rw [if_neg h]; omega

lemma f_pow_add_two (a : ℕ) (ha : 2 ≤ a) : f (2 ^ a + 2) = a * (a - 1) / 2 + 1 := by
  rw [f_eq_card]
  have h1 : Finset.range (2 ^ a + 2)
      = insert (2 ^ a + 1) (insert (2 ^ a) (Finset.range (2 ^ a))) := by
    ext x; simp only [Finset.mem_range, Finset.mem_insert]; omega
  rw [h1, Finset.filter_insert, if_pos (onesCount_pow_add_one a (by omega)),
    Finset.filter_insert, if_neg (by rw [onesCount_pow]; omega),
    Finset.card_insert_of_notMem (by simp), card_ones_lt_pow, Nat.choose_two_right]

lemma f_unbounded (m : ℕ) : ∃ K, m ≤ f K := by
  refine ⟨2 ^ (2 * m + 2) + 2, ?_⟩
  rw [f_pow_add_two _ (by omega)]
  have h : (2 * m + 2) * (2 * m + 2 - 1) / 2 ≥ (2 * m + 2) * 1 / 2 := by
    exact Nat.div_le_div_right (Nat.mul_le_mul_left _ (by omega))
  omega

/-! ### Part (a) -/

/-- **Part (a)**: every positive integer `m` is a value of `f`. -/
theorem exists_f_eq (m : ℕ) (hm : 0 < m) : ∃ k : ℕ, 0 < k ∧ f k = m := by
  have hex : ∃ K, m ≤ f K := f_unbounded m
  have hK : m ≤ f (Nat.find hex) := Nat.find_spec hex
  have hf0 : f 0 = 0 := by decide
  have hK0 : Nat.find hex ≠ 0 := by
    intro h
    rw [h, hf0] at hK
    omega
  obtain ⟨j, hj⟩ : ∃ j, Nat.find hex = j + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hlt : ¬ (m ≤ f j) := Nat.find_min hex (by omega)
  have hstep := f_succ_le j
  rw [hj] at hK
  exact ⟨j + 1, by omega, by omega⟩

/-! ### Part (b) -/

lemma onesCount_two : onesCount 2 = 1 := by
  have h := onesCount_pow 1
  norm_num at h
  exact h

lemma onesCount_pow_add_two (a : ℕ) (ha : 2 ≤ a) : onesCount (2 ^ a + 2) = 2 := by
  have h2 : (2:ℕ) < 2 ^ a := by
    calc (2:ℕ) = 2 ^ 1 := by norm_num
    _ < 2 ^ a := Nat.pow_lt_pow_right (by norm_num) (by omega)
  rw [onesCount_pow_add a 2 h2, onesCount_two]

/-- Two consecutive integers both having exactly two binary ones occurs exactly for the
pair `2 ^ a + 1`, `2 ^ a + 2` with `a ≥ 2`. -/
lemma consecutive_two_ones (k : ℕ) (hk : 2 ≤ k) :
    (onesCount k = 2 ∧ onesCount (k - 1) = 2) ↔ ∃ a : ℕ, 2 ≤ a ∧ k = 2 ^ a + 2 := by
  constructor
  · rintro ⟨h1, h2⟩
    rcases (by omega : k % 2 = 0 ∨ k % 2 = 1) with hr | hr
    · have hkq : k = 2 * (k / 2) + 0 := by omega
      have honeq : onesCount (k / 2) = 2 := by
        rw [hkq, onesCount_bit _ _ (by omega)] at h1; omega
      have hkm : k - 1 = 2 * (k / 2 - 1) + 1 := by omega
      rw [hkm, onesCount_bit _ _ (by omega)] at h2
      obtain ⟨b, hb⟩ := (onesCount_eq_one_iff _).mp (by omega : onesCount (k / 2 - 1) = 1)
      have hqv : k / 2 = 2 ^ b + 1 := by omega
      have hb1 : 1 ≤ b := by
        by_contra hb0
        have hb00 : b = 0 := by omega
        rw [hb00, pow_zero] at hqv
        rw [hqv] at honeq
        rw [onesCount_two] at honeq
        omega
      exact ⟨b + 1, by omega, by rw [hkq, hqv]; ring⟩
    · exfalso
      have hkq : k = 2 * (k / 2) + 1 := by omega
      have h1' : onesCount (k / 2) = 1 := by
        rw [hkq, onesCount_bit _ _ (by omega)] at h1; omega
      have hkm : k - 1 = 2 * (k / 2) + 0 := by omega
      rw [hkm, onesCount_bit _ _ (by omega)] at h2
      omega
  · rintro ⟨a, ha, rfl⟩
    refine ⟨onesCount_pow_add_two a ha, ?_⟩
    have h : 2 ^ a + 2 - 1 = 2 ^ a + 1 := by omega
    rw [h, onesCount_pow_add_one a (by omega)]

/-- **Part (b)**: the positive integers `m` attained by exactly one `k` are precisely the
numbers `n (n-1) / 2 + 1` for `n ≥ 2`. -/
theorem unique_f_eq_iff (m : ℕ) (hm : 0 < m) :
    (∃! k : ℕ, 0 < k ∧ f k = m) ↔ ∃ n : ℕ, 2 ≤ n ∧ m = n * (n - 1) / 2 + 1 := by
  constructor
  · rintro ⟨k, ⟨hk0, hfk⟩, huniq⟩
    have hf1 : f 1 = 0 := by decide
    have hk2 : 2 ≤ k := by
      rcases (by omega : k = 1 ∨ 2 ≤ k) with rfl | h
      · omega
      · exact h
    have hones_k : onesCount k = 2 := by
      by_contra h
      have hs := f_succ k (by omega)
      rw [if_neg h] at hs
      have := huniq (k + 1) ⟨by omega, by omega⟩
      omega
    have hones_km : onesCount (k - 1) = 2 := by
      by_contra h
      have hs := f_succ (k - 1) (by omega)
      rw [if_neg h, show k - 1 + 1 = k by omega] at hs
      have := huniq (k - 1) ⟨by omega, by omega⟩
      omega
    obtain ⟨a, ha, hka⟩ := (consecutive_two_ones k hk2).mp ⟨hones_k, hones_km⟩
    exact ⟨a, ha, by rw [← hfk, hka, f_pow_add_two a ha]⟩
  · rintro ⟨n, hn, rfl⟩
    refine ⟨2 ^ n + 2, ⟨by positivity, f_pow_add_two n hn⟩, ?_⟩
    rintro j ⟨hj0, hfj⟩
    by_contra hne
    have hfval := f_pow_add_two n hn
    rcases (by omega : j < 2 ^ n + 2 ∨ 2 ^ n + 2 < j) with h | h
    · have hs := f_succ (2 ^ n + 1) (Nat.le_add_left 1 _)
      rw [show 2 ^ n + 1 + 1 = 2 ^ n + 2 by omega,
        if_pos (onesCount_pow_add_one n (by omega))] at hs
      have hmono : f j ≤ f (2 ^ n + 1) := f_mono (by omega)
      omega
    · have hs := f_succ (2 ^ n + 2) (Nat.le_add_left 1 _)
      rw [if_pos (onesCount_pow_add_two n hn)] at hs
      have hmono : f (2 ^ n + 2 + 1) ≤ f j := f_mono (by omega)
      omega

end IMO1994P3
