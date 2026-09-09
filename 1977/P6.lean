/-
# IMO 1977, Problem 6

Let `f : ℕ⁺ → ℕ⁺` satisfy `f (n+1) > f (f n)` for every positive integer `n`.
Prove that `f n = n` for all `n`.

## Modelling

`f : ℕ → ℕ` with the hypotheses restricted to positive arguments:
`0 < f n` for `0 < n`, and `f (n+1) > f (f n)` for `0 < n`.  The conclusion is
`f n = n` for every `0 < n`.  The value `f 0` is left unconstrained, as it
should be.

## Proof

Both write-ups (the AoPS one by infinite descent, and Peter Schor's auxiliary
function `g n = f (n+1) - 1` in the official solution) are more involved than
necessary.  The direct route is a single induction:

* **Key.**  For all `k` and all `n ≥ k` with `n > 0`, `f n ≥ k`.
  Induction on `k`.  For the step, write `n = m + 1` with `m ≥ k`.  If `m = 0`
  then `k = 0` and `f n ≥ 1` by positivity.  Otherwise `f m ≥ k` by the
  induction hypothesis, hence also `f (f m) ≥ k` (applying it to `f m ≥ k`),
  and `f (m+1) > f (f m) ≥ k`.

* Taking `k = n` gives `f n ≥ n`.
* Hence `f (f n) ≥ f n`, so `f (n+1) > f (f n) ≥ f n`: `f` is strictly
  increasing on the positives, and therefore monotone there.
* If `f n ≥ n + 1` then monotonicity gives `f (f n) ≥ f (n+1)`, contradicting
  `f (n+1) > f (f n)`.  So `f n ≤ n`, and with `f n ≥ n` we are done.
-/

import Mathlib

namespace Imo1977P6

/-- **IMO 1977, Problem 6.** -/
theorem imo1977_p6 (f : ℕ → ℕ) (hpos : ∀ n, 0 < n → 0 < f n)
    (h : ∀ n, 0 < n → f (n + 1) > f (f n)) :
    ∀ n, 0 < n → f n = n := by
  -- Key: `f n ≥ k` whenever `n ≥ k` and `n > 0`.
  have key : ∀ k n : ℕ, k ≤ n → 0 < n → k ≤ f n := by
    intro k
    induction k with
    | zero => intro n _ _; exact Nat.zero_le _
    | succ k ih =>
      intro n hkn hn
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      rcases Nat.eq_zero_or_pos m with hm | hm
      · have hk0 : k = 0 := by omega
        have hp := hpos (m + 1) (by omega)
        omega
      · have h1 : k ≤ f m := ih m (by omega) hm
        have h2 : 0 < f m := hpos m hm
        have h3 : k ≤ f (f m) := ih (f m) h1 h2
        have h4 := h m hm
        omega
  -- `n ≤ f n`
  have hge : ∀ n, 0 < n → n ≤ f n := fun n hn => key n n (le_refl n) hn
  -- `f` is strictly increasing on the positives
  have hstep : ∀ n, 0 < n → f n < f (n + 1) := by
    intro n hn
    have h1 := h n hn
    have h2 : f n ≤ f (f n) := hge (f n) (hpos n hn)
    omega
  have hmono : ∀ a b : ℕ, 0 < a → a ≤ b → f a ≤ f b := by
    intro a b ha hab
    induction b, hab using Nat.le_induction with
    | base => exact le_refl _
    | succ m hm ih =>
      have hs := hstep m (by omega)
      omega
  -- `f n ≤ n`
  intro n hn
  have hle : f n ≤ n := by
    by_contra hcon
    have h1 : n + 1 ≤ f n := by omega
    have h2 : f (n + 1) ≤ f (f n) := hmono (n + 1) (f n) (by omega) h1
    have h3 := h n hn
    omega
  have h4 := hge n hn
  omega

end Imo1977P6
