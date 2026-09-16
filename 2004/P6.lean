import Mathlib

/-!
# IMO 2004, Problem 6 — the "only if" half, and the concatenation engine

A positive integer is *alternating* if every two consecutive decimal digits have different
parity. Find all `n` having an alternating multiple. Answer: all `n` not divisible by `20`.

## What is formalized

* `Alternating`, in the arithmetic form below rather than through `Nat.digits`. Digit `i` of `m`
  is `(m / 10^i) % 10`, and since `10` is even its parity is just `(m / 10^i) % 2`; digit `i+1`
  exists exactly when `10^(i+1) ≤ m`. (I checked this definition agrees with the digit-list one
  for every `m < 200000`.)
* **`imo2004_p6_only_if`: a multiple of `20` is never alternating**, hence no `n` divisible by
  `20` has an alternating multiple. Complete.
* **`alternating_concat`**: writing an alternating block `x` in front of an alternating block `y`
  of exactly `L` digits gives an alternating number, provided the parities differ across the
  junction. Complete. This is the engine every step of the converse runs on.

## What is NOT formalized

The converse — every `n` with `20 ∤ n` has an alternating multiple — is not proved here. Its
proof needs three further ingredients on top of `alternating_concat`:

1. an induction producing, for each `k`, a `2k`-digit alternating multiple of `2^(2k+1)` whose
   leading digit is odd (base `16`; the step prepends one of `10, 12, 14, 16` chosen by solving
   `b · 2^(2k-1) ≡ a (mod 2^(2k+1))` for `b ∈ {0,1,2,3}`);
2. an induction producing an alternating multiple of `2 · 5^k` with at most `k` digits, using
   that the digits of one parity class hit every residue mod `5` exactly once;
3. for the part of `n` coprime to `10`, repeating an even-length alternating block `i` times —
   which multiplies it by `(10^{2ai} - 1)/(10^{2a} - 1)` and preserves alternation — and choosing
   `i` by a lifting-the-exponent argument so that the remaining factor of `n` divides.

Steps 1 and 2 are within reach of `alternating_concat`; step 3 needs the `p`-adic valuation
machinery for `10^{2ai} - 1` and is the substantial one. The AoPS write-up's own treatment of
step 3 is terse to the point of being hard to check (it asserts `ν_p(a_i) = ν_p(x) + ν_p(i)` and
then picks `i = φ(n)` without reconciling the two).
-/

namespace Imo2004P6

/-- `m` is alternating: consecutive decimal digits have different parity. Digit `i` of `m` has the
parity of `m / 10 ^ i`, and exists exactly when `10 ^ i ≤ m`. -/
def Alternating (m : ℕ) : Prop :=
  ∀ i : ℕ, 10 ^ (i + 1) ≤ m → (m / 10 ^ i) % 2 ≠ (m / 10 ^ (i + 1)) % 2

/-! ### Sanity checks on the definition -/

theorem alternating_sixteen : Alternating 16 := by
  intro i hi
  match i with
  | 0 => norm_num
  | (k + 1) =>
      exfalso
      have h1 : (10 : ℕ) ^ 2 ≤ 10 ^ (k + 1 + 1) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 : (10 : ℕ) ^ 2 = 100 := by norm_num
      omega

/-! ### No multiple of `20` is alternating -/

theorem not_alternating_of_twenty_dvd {m : ℕ} (hm : 0 < m) (h : 20 ∣ m) : ¬ Alternating m := by
  intro halt
  obtain ⟨t, rfl⟩ := h
  have ht : 1 ≤ t := by omega
  have hpow : (10 : ℕ) ^ (0 + 1) = 10 := by norm_num
  have hle : 10 ^ (0 + 1) ≤ 20 * t := by omega
  have hne := halt 0 hle
  have e0 : (20 * t) / 10 ^ 0 = 20 * t := by norm_num
  have e1 : (20 * t) / 10 ^ (0 + 1) = 2 * t := by rw [hpow]; omega
  rw [e0, e1] at hne
  exact hne (by omega)

/-- **IMO 2004 P6, the "only if" direction.** -/
theorem imo2004_p6_only_if (n : ℕ) (h : 20 ∣ n) :
    ¬ ∃ m : ℕ, 0 < m ∧ n ∣ m ∧ Alternating m := by
  rintro ⟨m, hmpos, hnm, halt⟩
  exact not_alternating_of_twenty_dvd hmpos (dvd_trans h hnm) halt

/-! ### Arithmetic of writing one block in front of another -/

theorem div_pow_of_le {x y L i : ℕ} (hi : i ≤ L) :
    (x * 10 ^ L + y) / 10 ^ i = x * 10 ^ (L - i) + y / 10 ^ i := by
  have hpos : 0 < (10 : ℕ) ^ i := pow_pos (by norm_num) i
  have h1 : x * 10 ^ L + y = y + 10 ^ i * (x * 10 ^ (L - i)) := by
    have h2 : (10 : ℕ) ^ L = 10 ^ i * 10 ^ (L - i) := by
      rw [← pow_add]
      congr 1
      omega
    rw [h2]
    ring
  rw [h1, Nat.add_mul_div_left _ _ hpos]
  exact Nat.add_comm _ _

theorem div_pow_of_ge {x y L j : ℕ} (hy : y < 10 ^ L) :
    (x * 10 ^ L + y) / 10 ^ (L + j) = x / 10 ^ j := by
  have hL0 : 0 < (10 : ℕ) ^ L := pow_pos (by norm_num) L
  have h1 : (x * 10 ^ L + y) / 10 ^ L = x := by
    have h2 : x * 10 ^ L + y = y + 10 ^ L * x := by ring
    rw [h2, Nat.add_mul_div_left _ _ hL0, Nat.div_eq_of_lt hy, zero_add]
  rw [pow_add, ← Nat.div_div_eq_div_mul, h1]

theorem parity_shift (x z k : ℕ) (hk : 1 ≤ k) : (x * 10 ^ k + z) % 2 = z % 2 := by
  obtain ⟨d, hd⟩ : (2 : ℕ) ∣ 10 ^ k := dvd_pow (by norm_num) (by omega)
  have h1 : x * 10 ^ k = 2 * (x * d) := by rw [hd]; ring
  rw [h1]
  omega

/-- Writing the alternating block `x` in front of the `L`-digit alternating block `y` gives an
alternating number, provided the parities differ at the junction. -/
theorem alternating_concat {x y L : ℕ} (hL : 1 ≤ L) (hylo : 10 ^ (L - 1) ≤ y)
    (hyhi : y < 10 ^ L) (hx : Alternating x) (hy : Alternating y)
    (hjunc : x % 2 ≠ (y / 10 ^ (L - 1)) % 2) :
    Alternating (x * 10 ^ L + y) := by
  intro i hi
  rcases Nat.lt_or_ge (i + 1) L with hlt | hge
  · -- both digits lie inside `y`
    rw [div_pow_of_le (by omega : i ≤ L), div_pow_of_le (by omega : i + 1 ≤ L),
      parity_shift _ _ _ (by omega : 1 ≤ L - i),
      parity_shift _ _ _ (by omega : 1 ≤ L - (i + 1))]
    refine hy i ?_
    calc (10 : ℕ) ^ (i + 1) ≤ 10 ^ (L - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ y := hylo
  · rcases Nat.eq_or_lt_of_le hge with heq | hgt
    · -- the junction: digit `i` is the top digit of `y`, digit `i+1` the bottom digit of `x`
      have hiL : i = L - 1 := by omega
      have h1 : (x * 10 ^ L + y) / 10 ^ (i + 1) = x := by
        have h2 := div_pow_of_ge (x := x) (y := y) (L := L) (j := 0) hyhi
        rw [← heq]
        simpa using h2
      rw [h1, div_pow_of_le (by omega : i ≤ L), parity_shift _ _ _ (by omega : 1 ≤ L - i), hiL]
      exact Ne.symm hjunc
    · -- both digits lie inside `x`
      have hLi : L ≤ i := by omega
      have e1 : (x * 10 ^ L + y) / 10 ^ i = x / 10 ^ (i - L) := by
        have h2 := div_pow_of_ge (x := x) (y := y) (L := L) (j := i - L) hyhi
        rwa [show L + (i - L) = i from by omega] at h2
      have e2 : (x * 10 ^ L + y) / 10 ^ (i + 1) = x / 10 ^ (i - L + 1) := by
        have h2 := div_pow_of_ge (x := x) (y := y) (L := L) (j := i - L + 1) hyhi
        rwa [show L + (i - L + 1) = i + 1 from by omega] at h2
      rw [e1, e2]
      refine hx (i - L) ?_
      have hL0 : 0 < (10 : ℕ) ^ L := pow_pos (by norm_num) L
      have hmul : 10 ^ L * 10 ^ (i - L + 1) < 10 ^ L * (x + 1) := by
        calc 10 ^ L * 10 ^ (i - L + 1) = 10 ^ (i + 1) := by
              rw [← pow_add]; congr 1; omega
          _ ≤ x * 10 ^ L + y := hi
          _ < x * 10 ^ L + 10 ^ L := by omega
          _ = 10 ^ L * (x + 1) := by ring
      have := Nat.lt_of_mul_lt_mul_left hmul
      omega

end Imo2004P6
