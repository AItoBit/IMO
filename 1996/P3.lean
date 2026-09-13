import Mathlib

/-!
# IMO 1996, Problem 3

Find all `f : ℕ → ℕ` with `f (m + f n) = f (f m) + f n` for all `m, n`.

## Answer

Either `f = 0`, or there are `d > 0` and `a : ℕ → ℕ` with `a 0 = 0` such that

  `f n = d * (a (n % d) + n / d)`.

(Only the values `a r` for `r < d` matter.)

## Proof of the forward direction

* `m = n = 0` gives `f 0 = 0`, and then `m = 0` gives `f (f n) = f n`.
* So the equation reads `f (m + f n) = f m + f n`; in particular for any fixed point `t` of `f`,
  `f (m + t) = f m + t`.
* If `f` has no positive fixed point then every `f n`, being a fixed point, is `0`.
* Otherwise let `d` be the least positive fixed point. Iterating the previous step,
  `f (m + q*d) = f m + q*d`, so `f n = f (n % d) + (n / d) * d`.
* A fixed point `t` then satisfies `f (t % d) = t % d` with `t % d < d`, so `d ∣ t` by
  minimality. Since every `f r` is a fixed point, `d ∣ f r`, and `a r := f r / d` works.
-/

namespace Imo1996P3

theorem imo1996_p3 (f : ℕ → ℕ) :
    (∀ m n, f (m + f n) = f (f m) + f n) ↔
      (∀ n, f n = 0) ∨
        ∃ d : ℕ, 0 < d ∧ ∃ a : ℕ → ℕ, a 0 = 0 ∧ ∀ n, f n = d * (a (n % d) + n / d) := by
  classical
  constructor
  · intro P
    -- `f 0 = 0`
    have h0 : f 0 = 0 := by
      have h := P 0 0
      rw [Nat.zero_add] at h
      omega
    -- `f` is idempotent
    have hff : ∀ n, f (f n) = f n := by
      intro n
      have h := P 0 n
      simp only [Nat.zero_add, h0] at h
      simpa using h
    -- translation by a fixed point
    have key : ∀ t m, f t = t → f (m + t) = f m + t := by
      intro t m ht
      have h := P m t
      rw [ht, hff m] at h
      exact h
    by_cases hex : ∃ n, 0 < n ∧ f n = n
    · right
      obtain ⟨d, ⟨hd0, hdfix⟩, hmin⟩ :
          ∃ d, (0 < d ∧ f d = d) ∧ ∀ k, k < d → ¬ (0 < k ∧ f k = k) :=
        ⟨Nat.find hex, Nat.find_spec hex, fun k hk => Nat.find_min hex hk⟩
      -- translation by multiples of `d`
      have hstep : ∀ q m, f (m + q * d) = f m + q * d := by
        intro q
        induction q with
        | zero => intro m; simp
        | succ q ih =>
          intro m
          have hre : m + (q + 1) * d = (m + q * d) + d := by ring
          rw [hre, key d _ hdfix, ih m]
          ring
      -- decomposition of `f` along division by `d`
      have hdecomp : ∀ n, f n = f (n % d) + (n / d) * d := by
        intro n
        conv_lhs => rw [← Nat.mod_add_div' n d]
        exact hstep (n / d) (n % d)
      -- fixed points are multiples of `d`
      have hfix_dvd : ∀ t, f t = t → d ∣ t := by
        intro t ht
        have h1 := hdecomp t
        rw [ht] at h1
        have h2 : t % d + t / d * d = t := Nat.mod_add_div' t d
        have h3 : f (t % d) = t % d := by omega
        have h4 : t % d < d := Nat.mod_lt _ hd0
        by_contra hcon
        have h5 : 0 < t % d := by
          rcases Nat.eq_zero_or_pos (t % d) with h | h
          · exact absurd (Nat.dvd_of_mod_eq_zero h) hcon
          · exact h
        exact hmin (t % d) h4 ⟨h5, h3⟩
      refine ⟨d, hd0, fun r => f r / d, by simp [h0], ?_⟩
      intro n
      obtain ⟨k, hk⟩ := hfix_dvd (f (n % d)) (hff (n % d))
      have hdiv : f (n % d) / d = k := by
        rw [hk]
        exact Nat.mul_div_cancel_left k hd0
      show f n = d * (f (n % d) / d + n / d)
      rw [hdecomp n, hdiv, hk]
      ring
    · left
      intro n
      by_contra hn
      exact hex ⟨f n, Nat.pos_of_ne_zero hn, hff n⟩
  · rintro (h | ⟨d, hd, a, ha0, hf⟩) m n
    · simp [h]
    · have hmod : (m + f n) % d = m % d := by
        rw [hf n]
        exact Nat.add_mul_mod_self_left m d _
      have hdivv : (m + f n) / d = m / d + (a (n % d) + n / d) := by
        rw [hf n]
        exact Nat.add_mul_div_left m _ hd
      have hJ : f m = d * (a (m % d) + m / d) := hf m
      have hfm : f (f m) = f m := by
        rw [hf (f m), hJ, Nat.mul_mod_right, Nat.mul_div_cancel_left _ hd, ha0, Nat.zero_add]
      rw [hf (m + f n), hmod, hdivv, hfm, hf m, hf n]
      ring

end Imo1996P3
