/-
# IMO 1978, Problem 3

The positive integers are the disjoint union of the ranges of two strictly
increasing sequences `f` and `g`, with `g n = f (f n) + 1` for all `n ≥ 1`.
Determine `f 240`.

The answer is `f 240 = 388`.

## Modelling

`f g : ℕ → ℕ`, with every hypothesis restricted to indices `≥ 1`:
strict monotonicity on `[1, ∞)`, positivity, disjointness of the two ranges,
covering of every `m ≥ 1`, and `g n = f (f n) + 1`.  Values at `0` are
unconstrained.

## Proof

`f` is the lower Wythoff sequence `⌊nφ⌋`, but neither `φ` nor Beatty sequences
are needed: three identities suffice, and they give `f 240` in eleven steps.

* **Counting invariant.**  For every `m` there are `a, b` with `a + b = m`,
  `f k ≤ m ↔ k ≤ a` and `g k ≤ m ↔ k ≤ b` (for `k ≥ 1`).  Induction on `m`:
  each `m + 1` is either an `f`-value or a `g`-value, and it is then forced to
  be `f (a+1)` resp. `g (b+1)`, so exactly one of the two counters advances.

* **(I)** `f (f n) + 1 = f n + n`, i.e. `g n = f n + n`.  Apply the invariant at
  `m = f (f n)`: there the `f`-counter is `f n`, so the `g`-counter is
  `f (f n) - f n`; and the `g`-values `≤ f (f n)` are exactly `g 1, …, g (n-1)`,
  because `g n = f (f n) + 1`.

* **(II)** `f (f n + n) = 2 * f n + n`.  Apply (I) twice to get
  `f (f n + n - 1) = 2 f n + n - 2`, note `g (f n) = 2 f n + n - 1` is a
  `g`-value (so not an `f`-value), and use the invariant at `m = 2 f n + n` to
  see that `f (f n + n) ≤ m`.

Then

  `f 1 = 1`, `f 2 = 3`, `f 3 = 4`, `f 4 = 6`, `f 6 = 9`, `f 9 = 14`,
  `f 14 = 22`, `f 22 = 35`, `f 57 = 92`, `f 92 = 148`, `f 240 = 388`,

alternating (I) and (II).  The two uses of (II) are the shortcuts that avoid
computing `f` at all 240 indices.
-/

import Mathlib

namespace Imo1978P3

/-- **IMO 1978, Problem 3.** -/
theorem imo1978_p3 (f g : ℕ → ℕ)
    (hfmono : ∀ a b, 1 ≤ a → a < b → f a < f b)
    (hgmono : ∀ a b, 1 ≤ a → a < b → g a < g b)
    (hfpos : ∀ n, 1 ≤ n → 1 ≤ f n)
    (hgpos : ∀ n, 1 ≤ n → 1 ≤ g n)
    (hdisj : ∀ a b, 1 ≤ a → 1 ≤ b → f a ≠ g b)
    (hcover : ∀ m, 1 ≤ m → (∃ k, 1 ≤ k ∧ f k = m) ∨ (∃ k, 1 ≤ k ∧ g k = m))
    (hgf : ∀ n, 1 ≤ n → g n = f (f n) + 1) :
    f 240 = 388 := by
  -- the counting invariant
  have count : ∀ m : ℕ, ∃ a b : ℕ, a + b = m ∧
      (∀ k, 1 ≤ k → (f k ≤ m ↔ k ≤ a)) ∧ (∀ k, 1 ≤ k → (g k ≤ m ↔ k ≤ b)) := by
    intro m
    induction m with
    | zero =>
      refine ⟨0, 0, rfl, ?_, ?_⟩
      · intro k hk
        constructor
        · intro h; have := hfpos k hk; omega
        · intro h; omega
      · intro k hk
        constructor
        · intro h; have := hgpos k hk; omega
        · intro h; omega
    | succ m ih =>
      obtain ⟨a, b, hab, hA, hB⟩ := ih
      rcases hcover (m + 1) (by omega) with ⟨j, hj, hfj⟩ | ⟨j, hj, hgj⟩
      · -- `m + 1` is an `f`-value, so it must be `f (a+1)`
        have hja : a + 1 ≤ j := by
          by_contra hc
          have hj' : j ≤ a := by omega
          have := (hA j hj).mpr hj'
          omega
        have h1 : f (a + 1) ≤ m + 1 := by
          rcases Nat.eq_or_lt_of_le hja with h | h
          · rw [← h] at hfj; omega
          · have := hfmono (a + 1) j (by omega) h; omega
        have h2 : m + 1 ≤ f (a + 1) := by
          by_contra hc
          have hle : f (a + 1) ≤ m := by omega
          have := (hA (a + 1) (by omega)).mp hle
          omega
        have hfa1 : f (a + 1) = m + 1 := by omega
        refine ⟨a + 1, b, by omega, ?_, ?_⟩
        · intro k hk
          constructor
          · intro h
            by_contra hc
            have hk2 : a + 1 < k := by omega
            have := hfmono (a + 1) k (by omega) hk2
            omega
          · intro h
            rcases Nat.eq_or_lt_of_le h with h' | h'
            · rw [h']; omega
            · have := hfmono k (a + 1) hk (by omega)
              omega
        · intro k hk
          have hne : g k ≠ m + 1 := by
            rw [← hfa1]
            exact fun hh => hdisj (a + 1) k (by omega) hk hh.symm
          constructor
          · intro h
            have hle : g k ≤ m := by omega
            exact (hB k hk).mp hle
          · intro h
            have := (hB k hk).mpr h
            omega
      · -- `m + 1` is a `g`-value, so it must be `g (b+1)`
        have hjb : b + 1 ≤ j := by
          by_contra hc
          have hj' : j ≤ b := by omega
          have := (hB j hj).mpr hj'
          omega
        have h1 : g (b + 1) ≤ m + 1 := by
          rcases Nat.eq_or_lt_of_le hjb with h | h
          · rw [← h] at hgj; omega
          · have := hgmono (b + 1) j (by omega) h; omega
        have h2 : m + 1 ≤ g (b + 1) := by
          by_contra hc
          have hle : g (b + 1) ≤ m := by omega
          have := (hB (b + 1) (by omega)).mp hle
          omega
        have hgb1 : g (b + 1) = m + 1 := by omega
        refine ⟨a, b + 1, by omega, ?_, ?_⟩
        · intro k hk
          have hne : f k ≠ m + 1 := by
            rw [← hgb1]
            exact hdisj k (b + 1) hk (by omega)
          constructor
          · intro h
            have hle : f k ≤ m := by omega
            exact (hA k hk).mp hle
          · intro h
            have := (hA k hk).mpr h
            omega
        · intro k hk
          constructor
          · intro h
            by_contra hc
            have hk2 : b + 1 < k := by omega
            have := hgmono (b + 1) k (by omega) hk2
            omega
          · intro h
            rcases Nat.eq_or_lt_of_le h with h' | h'
            · rw [h']; omega
            · have := hgmono k (b + 1) hk (by omega)
              omega
  -- `n ≤ f n`
  have hge : ∀ n, 1 ≤ n → n ≤ f n := by
    intro n
    induction n with
    | zero => intro h; omega
    | succ m ih =>
      intro _
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm; exact hfpos 1 (by omega)
      · have h1 := ih hm
        have h2 := hfmono m (m + 1) hm (by omega)
        omega
  -- the `g`-counter below an `f`-value
  have hcf : ∀ n, 1 ≤ n → ∀ k, 1 ≤ k → (g k ≤ f n ↔ k + n ≤ f n) := by
    intro n hn
    obtain ⟨a, b, hab, hA, hB⟩ := count (f n)
    have han : a = n := by
      have h1 : n ≤ a := (hA n hn).mp (le_refl _)
      have h2 : a ≤ n := by
        by_contra hc
        have hna : n < a := by omega
        have ha1 : 1 ≤ a := by omega
        have h3 := (hA a ha1).mpr (le_refl a)
        have h4 := hfmono n a hn hna
        omega
      omega
    intro k hk
    rw [hB k hk]
    omega
  -- (I)
  have hI : ∀ n, 1 ≤ n → f (f n) + 1 = f n + n := by
    intro n hn
    have hfn1 : 1 ≤ f n := hfpos n hn
    have key := hcf (f n) hfn1
    have hup : f (f n) + 1 ≤ f n + n := by
      by_contra hc
      have h3 : n + f n ≤ f (f n) := by omega
      have h4 := (key n hn).mpr h3
      rw [hgf n hn] at h4
      omega
    have hlow : f n + n ≤ f (f n) + 1 := by
      rcases Nat.lt_or_ge n 2 with h2 | h2
      · have hn1 : n = 1 := by omega
        subst hn1
        have := hge (f 1) hfn1
        omega
      · have hn1 : 1 ≤ n - 1 := by omega
        have hgle : g (n - 1) ≤ f (f n) := by
          have h5 := hgmono (n - 1) n hn1 (by omega)
          rw [hgf n hn] at h5
          omega
        have := (key (n - 1) hn1).mp hgle
        omega
    omega
  have hgeq : ∀ n, 1 ≤ n → g n = f n + n := by
    intro n hn
    rw [hgf n hn]
    have := hI n hn
    omega
  -- `f 1 = 1`
  have e1 : f 1 = 1 := by
    rcases hcover 1 (by omega) with ⟨k, hk, hfk⟩ | ⟨k, hk, hgk⟩
    · have h0 := hge 1 (by omega)
      have h1 : f 1 ≤ f k := by
        rcases Nat.eq_or_lt_of_le hk with h | h
        · exact le_of_eq (congrArg f h)
        · exact le_of_lt (hfmono 1 k (by omega) h)
      omega
    · have h1 := hgeq k hk
      have h2 := hfpos k hk
      omega
  -- (II)
  have hII : ∀ n, 1 ≤ n → f (f n + n) = 2 * f n + n := by
    intro n hn
    have hfn1 : 1 ≤ f n := hfpos n hn
    have hffn := hI n hn
    have hfffn := hI (f n) hfn1
    obtain ⟨a, b, hab, hA, hB⟩ := count (2 * f n + n)
    have hgF : g (f n) = f (f n) + f n := hgeq (f n) hfn1
    have hb1 : f n ≤ b := (hB (f n) hfn1).mp (by omega)
    have hgF1 : g (f n + 1) = f (f n + 1) + (f n + 1) := hgeq (f n + 1) (by omega)
    have hmono1 : f (f n) < f (f n + 1) := hfmono (f n) (f n + 1) hfn1 (by omega)
    have hb2 : ¬ (f n + 1 ≤ b) := by
      intro hc
      have := (hB (f n + 1) (by omega)).mpr hc
      omega
    have hbeq : b = f n := by omega
    have hle : f (f n + n) ≤ 2 * f n + n := (hA (f n + n) (by omega)).mpr (by omega)
    have hlt : f (f (f n)) < f (f n + n) :=
      hfmono (f (f n)) (f n + n) (hfpos (f n) hfn1) (by omega)
    have hne : f (f n + n) ≠ g (f n) := hdisj (f n + n) (f n) (by omega) hfn1
    omega
  -- the eleven-step chain
  have e2 : f 2 = 3 := by
    have h := hII 1 (by norm_num)
    rw [e1] at h
    norm_num at h
    exact h
  have e3 : f 3 = 4 := by
    have h := hI 2 (by norm_num)
    rw [e2] at h
    omega
  have e4 : f 4 = 6 := by
    have h := hI 3 (by norm_num)
    rw [e3] at h
    omega
  have e6 : f 6 = 9 := by
    have h := hI 4 (by norm_num)
    rw [e4] at h
    omega
  have e9 : f 9 = 14 := by
    have h := hI 6 (by norm_num)
    rw [e6] at h
    omega
  have e14 : f 14 = 22 := by
    have h := hI 9 (by norm_num)
    rw [e9] at h
    omega
  have e22 : f 22 = 35 := by
    have h := hI 14 (by norm_num)
    rw [e14] at h
    omega
  have e57 : f 57 = 92 := by
    have h := hII 22 (by norm_num)
    rw [e22] at h
    norm_num at h
    exact h
  have e92 : f 92 = 148 := by
    have h := hI 57 (by norm_num)
    rw [e57] at h
    omega
  have h := hII 92 (by norm_num)
  rw [e92] at h
  norm_num at h
  exact h

end Imo1978P3
