/-
IMO 2024 Problem 1.

Determine all real numbers `α` such that, for every positive integer `n`,
the integer `⌊α⌋ + ⌊2α⌋ + ⋯ + ⌊nα⌋` is a multiple of `n`.

Answer: exactly the even integers.

Proof strategy (a uniform version of the two-case argument):

Write `⌊α⌋ = 2a + c` with `c = ⌊α⌋ % 2 ∈ {0,1}`, and `α = (2a+c) + ε`, `0 ≤ ε < 1`.
Then `⌊iα⌋ = i(2a+c) + ⌊iε⌋`.

Main claim (induction on `n`):  `⌊nα⌋ = n(2a+c) + c(n-1)` for all `n ≥ 1`.

Assuming it for all `i ≤ m`, the closed form

  `∑_{i=1}^{m} (i(2a+c) + c(i-1)) = a·m(m+1) + c·m²`

together with `(m+1) ∣ S_{m+1}` gives `(m+1) ∣ c + ⌊(m+1)ε⌋`
(because `a·m(m+1) ≡ 0` and `c·m² = c(m+1)(m-1) + c ≡ c`).
Since `0 ≤ ⌊(m+1)ε⌋ ≤ m` and `c ∈ {0,1}`, the quantity `c + ⌊(m+1)ε⌋` lies in
`[0, m+1]`, so it is `0` or `m+1`; either way `⌊(m+1)ε⌋ = c·m`.

Finally:
* `c = 1` forces `⌊nε⌋ = n-1`, i.e. `n(1-ε) ≤ 1` for all `n` — impossible (Archimedes).
* `c = 0` forces `⌊nε⌋ = 0`, i.e. `nε < 1` for all `n`, hence `ε = 0` and `α = 2a`.
-/

import Mathlib

open Finset

/-! ### Floor wrappers

These two facts are `@[simp]` in Mathlib, but their names have moved around
(`Int.floor_add_int` → `Int.floor_add_intCast`, etc.).  Proving them by `simp`
here makes the file insensitive to that. -/

private lemma floor_add_intCast' (x : ℝ) (z : ℤ) : ⌊x + (z : ℝ)⌋ = ⌊x⌋ + z := by
  simp

private lemma floor_intCast' (z : ℤ) : ⌊((z : ℝ))⌋ = z := by
  simp

/-- The Gauss-type closed form used throughout. -/
private lemma sum_aux (a c : ℤ) (m : ℕ) :
    ∑ i ∈ Finset.Icc 1 m, ((i : ℤ) * (2 * a + c) + c * ((i : ℤ) - 1))
      = a * (m : ℤ) * ((m : ℤ) + 1) + c * (m : ℤ) ^ 2 := by
  induction m with
  | zero =>
      rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
      simp
  | succ m ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih]
      push_cast
      ring

theorem imo2024_p1 (α : ℝ) :
    (∀ n : ℕ, 0 < n → (n : ℤ) ∣ ∑ i ∈ Finset.Icc 1 n, ⌊(i : ℝ) * α⌋) ↔
      ∃ m : ℤ, Even m ∧ α = (m : ℝ) := by
  constructor
  · intro h
    -- `⌊α⌋ = 2a + c` with `c ∈ {0,1}`
    obtain ⟨a, c, hc01, hkk⟩ : ∃ a c : ℤ, (c = 0 ∨ c = 1) ∧ ⌊α⌋ = 2 * a + c :=
      ⟨⌊α⌋ / 2, ⌊α⌋ % 2, by omega, by omega⟩
    -- `α = (2a+c) + ε` with `0 ≤ ε < 1`
    obtain ⟨ε, hε0, hε1, hαε⟩ :
        ∃ ε : ℝ, 0 ≤ ε ∧ ε < 1 ∧ α = ((2 * a + c : ℤ) : ℝ) + ε := by
      refine ⟨α - (⌊α⌋ : ℝ), by linarith [Int.floor_le α],
        by linarith [Int.lt_floor_add_one α], ?_⟩
      rw [← hkk]
      ring
    have hfloor : ∀ i : ℕ, ⌊(i : ℝ) * α⌋ = (i : ℤ) * (2 * a + c) + ⌊(i : ℝ) * ε⌋ := by
      intro i
      have h1 : (i : ℝ) * α = (i : ℝ) * ε + (((i : ℤ) * (2 * a + c) : ℤ) : ℝ) := by
        rw [hαε]; push_cast; ring
      rw [h1, floor_add_intCast']
      ring
    -- Main claim, packaged as `∀ n, ∀ i ≤ n, …` to get a strong hypothesis.
    have key : ∀ n i : ℕ, i ≤ n → 0 < i →
        ⌊(i : ℝ) * α⌋ = (i : ℤ) * (2 * a + c) + c * ((i : ℤ) - 1) := by
      intro n
      induction n with
      | zero =>
          intro i hi hi0
          exact absurd hi (by omega)
      | succ m ihm =>
          intro i hi hi0
          rcases eq_or_lt_of_le hi with heq | hlt
          · subst heq
            have hpos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by
              have hm : (0 : ℕ) < m + 1 := by omega
              exact_mod_cast hm
            have hcongr : ∑ j ∈ Finset.Icc 1 m, ⌊(j : ℝ) * α⌋
                = ∑ j ∈ Finset.Icc 1 m, ((j : ℤ) * (2 * a + c) + c * ((j : ℤ) - 1)) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              rw [Finset.mem_Icc] at hj
              exact ihm j hj.2 (by omega)
            have hS : ∑ j ∈ Finset.Icc 1 (m + 1), ⌊(j : ℝ) * α⌋
                = a * (m : ℤ) * ((m : ℤ) + 1) + c * (m : ℤ) ^ 2
                    + ⌊((m + 1 : ℕ) : ℝ) * α⌋ := by
              rw [Finset.sum_Icc_succ_top (by omega), hcongr, sum_aux]
            obtain ⟨d, hd⟩ := h (m + 1) (by omega)
            rw [hS, hfloor (m + 1)] at hd
            -- `(m+1) ∣ c + ⌊(m+1)ε⌋`
            have hdvd : ((m : ℤ) + 1) ∣ (c + ⌊((m + 1 : ℕ) : ℝ) * ε⌋) := by
              refine ⟨d - a * (m : ℤ) - c * ((m : ℤ) - 1) - (2 * a + c), ?_⟩
              push_cast at hd ⊢
              linear_combination hd
            have hL0 : 0 ≤ ⌊((m + 1 : ℕ) : ℝ) * ε⌋ :=
              Int.floor_nonneg.2 (mul_nonneg hpos.le hε0)
            have hLlt : ⌊((m + 1 : ℕ) : ℝ) * ε⌋ < (m : ℤ) + 1 := by
              refine Int.floor_lt.2 ?_
              have h3 := mul_lt_mul_of_pos_left hε1 hpos
              push_cast at h3 ⊢
              linarith
            have hLm : ⌊((m + 1 : ℕ) : ℝ) * ε⌋ = c * (m : ℤ) := by
              rcases hc01 with rfl | rfl
              · rw [zero_add] at hdvd
                rw [zero_mul]
                rcases eq_or_lt_of_le hL0 with h0 | h0
                · omega
                · have h4 := Int.le_of_dvd h0 hdvd
                  omega
              · rw [one_mul]
                have h1 : (0 : ℤ) < 1 + ⌊((m + 1 : ℕ) : ℝ) * ε⌋ := by omega
                have h4 := Int.le_of_dvd h1 hdvd
                omega
            rw [hfloor (m + 1)]
            push_cast
            push_cast at hLm
            linear_combination hLm
          · exact ihm i (by omega) hi0
    have hkey : ∀ n : ℕ, 0 < n → ⌊(n : ℝ) * ε⌋ = c * ((n : ℤ) - 1) := by
      intro n hn
      have h1 := key n n le_rfl hn
      have h2 := hfloor n
      linear_combination h1 - h2
    rcases hc01 with rfl | rfl
    · -- `c = 0`: every `⌊nε⌋ = 0`, hence `ε = 0`
      have hz : ε = 0 := by
        by_contra hne
        have hpos : 0 < ε := lt_of_le_of_ne hε0 (Ne.symm hne)
        obtain ⟨n, hn⟩ := Archimedean.arch (1 : ℝ) hpos
        rw [nsmul_eq_mul] at hn
        have hn0 : 0 < n := by
          rcases Nat.eq_zero_or_pos n with rfl | hp
          · norm_num at hn
          · exact hp
        have h5 := hkey n hn0
        rw [zero_mul] at h5
        have h6 : (1 : ℤ) ≤ ⌊(n : ℝ) * ε⌋ := by
          refine Int.le_floor.2 ?_
          push_cast
          linarith
        omega
      exact ⟨2 * a, ⟨a, by ring⟩, by rw [hαε, hz]; push_cast; ring⟩
    · -- `c = 1`: every `⌊nε⌋ = n - 1`, i.e. `n(1-ε) ≤ 1` — impossible
      exfalso
      have hpos : (0 : ℝ) < 1 - ε := by linarith
      obtain ⟨n, hn⟩ := Archimedean.arch (2 : ℝ) hpos
      rw [nsmul_eq_mul] at hn
      have hn0 : 0 < n := by
        rcases Nat.eq_zero_or_pos n with rfl | hp
        · norm_num at hn
        · exact hp
      have h5 := hkey n hn0
      rw [one_mul] at h5
      have h6 : ((n : ℤ) - 1 : ℤ) ≤ ⌊(n : ℝ) * ε⌋ := by omega
      have h7 := Int.le_floor.mp h6
      push_cast at h7
      nlinarith [h7, hn]
  · -- Even integers do work: `∑_{i=1}^n 2ti = t·n(n+1)`.
    rintro ⟨m, ⟨t, rfl⟩, rfl⟩
    intro n hn
    have hfl : ∀ i : ℕ, ⌊(i : ℝ) * ((t + t : ℤ) : ℝ)⌋
        = (i : ℤ) * (2 * t + 0) + 0 * ((i : ℤ) - 1) := by
      intro i
      have h1 : (i : ℝ) * ((t + t : ℤ) : ℝ) = (((i : ℤ) * (2 * t + 0) : ℤ) : ℝ) := by
        push_cast; ring
      rw [h1, floor_intCast']
      ring
    rw [Finset.sum_congr rfl (fun i _ => hfl i), sum_aux]
    exact ⟨t * ((n : ℤ) + 1), by ring⟩
