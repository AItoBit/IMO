import Mathlib

open scoped BigOperators
open scoped Nat

set_option maxHeartbeats 1000000

/-!
# IMO 1974, Problem 3

Prove that the number `∑_{k=0}^{n} C(2n+1, 2k+1) * 2^(3k)` is not divisible by `5`
for any integer `n ≥ 0`.

The proof works in the ring `ℤ√2`.  Writing `(1 + √2)^(2n+1) = A n + B n √2` one has
`A n = ∑_{k=0}^n C(2n+1,2k) 2^k`, `B n = ∑_{k=0}^n C(2n+1,2k+1) 2^k`, and taking norms
gives the Pell identity `A n ^ 2 - 2 * B n ^ 2 = -1`.

Modulo `5` we have `8 = 2^3 ≡ 2⁻¹`, and reversing the order of summation (together with the
symmetry `C(2n+1, 2(n-k)+1) = C(2n+1, 2k)`) shows `2^n * S n ≡ A n [ZMOD 5]`, where `S n`
is the sum from the problem.  Hence `5 ∣ S n` would force `A n ≡ 0`, so `2 * B n ^ 2 ≡ 1`
modulo `5`, which is impossible since `3` is not a square modulo `5`.
-/

namespace IMO1974P3

/-- The "rational part" of `(1 + √2) ^ (2n+1)`: `A n = ∑_{k=0}^{n} C(2n+1, 2k) 2^k`. -/
def A (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n + 1), ((2 * n + 1).choose (2 * k) : ℤ) * 2 ^ k

/-- The "irrational part" of `(1 + √2) ^ (2n+1)`: `B n = ∑_{k=0}^{n} C(2n+1, 2k+1) 2^k`. -/
def B (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n + 1), ((2 * n + 1).choose (2 * k + 1) : ℤ) * 2 ^ k

/-- The sum appearing in the problem: `S n = ∑_{k=0}^{n} C(2n+1, 2k+1) * 2^(3k)`. -/
def S (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), (2 * n + 1).choose (2 * k + 1) * 2 ^ (3 * k)

/-- Splitting a sum over `range (2 * N)` into its even- and odd-indexed parts. -/
lemma sum_range_two_mul {M : Type*} [AddCommMonoid M] (f : ℕ → M) (N : ℕ) :
    ∑ m ∈ Finset.range (2 * N), f m = ∑ k ∈ Finset.range N, (f (2 * k) + f (2 * k + 1)) := by
  induction N with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ← ih, Nat.mul_succ, Finset.sum_range_succ, Finset.sum_range_succ]
      rw [add_assoc]

/-- A finite sum in `ℤ√2` is computed componentwise. -/
lemma sum_mk (f g : ℕ → ℤ) (N : ℕ) :
    ∑ k ∈ Finset.range N, (⟨f k, g k⟩ : Zsqrtd 2)
      = ⟨∑ k ∈ Finset.range N, f k, ∑ k ∈ Finset.range N, g k⟩ := by
  induction N with
  | zero => simp; rfl
  | succ n ih => simp [Finset.sum_range_succ, ih]

lemma sqrtd_two_mul (k : ℕ) : (Zsqrtd.sqrtd (d := 2)) ^ (2 * k) = ⟨2 ^ k, 0⟩ := by
  rw [pow_mul]
  have h : (Zsqrtd.sqrtd (d := 2)) ^ 2 = ⟨2, 0⟩ := by ext <;> simp [pow_two]
  rw [h]
  induction k with
  | zero => rfl
  | succ m ih => rw [pow_succ, pow_succ, ih]; ext <;> simp

/-- `(1 + √2) ^ (2n+1) = A n + B n * √2` inside `ℤ√2`. -/
lemma pow_eq (n : ℕ) : (⟨1, 1⟩ : Zsqrtd 2) ^ (2 * n + 1) = ⟨A n, B n⟩ := by
  have hbase : (⟨1, 1⟩ : Zsqrtd 2) = Zsqrtd.sqrtd + 1 := by ext <;> simp
  rw [hbase, add_pow]
  have h2 : 2 * n + 1 + 1 = 2 * (n + 1) := by ring
  rw [h2, sum_range_two_mul]
  have hterm : ∀ k ∈ Finset.range (n + 1),
      (Zsqrtd.sqrtd (d := 2)) ^ (2 * k) * 1 ^ (2 * n + 1 - 2 * k)
          * ((2 * n + 1).choose (2 * k) : ℤ√2)
        + (Zsqrtd.sqrtd (d := 2)) ^ (2 * k + 1) * 1 ^ (2 * n + 1 - (2 * k + 1))
          * ((2 * n + 1).choose (2 * k + 1) : ℤ√2)
      = (⟨((2 * n + 1).choose (2 * k) : ℤ) * 2 ^ k,
          ((2 * n + 1).choose (2 * k + 1) : ℤ) * 2 ^ k⟩ : Zsqrtd 2) := by
    intro k _
    rw [sqrtd_two_mul, pow_succ, sqrtd_two_mul]
    ext <;> simp <;> ring
  rw [Finset.sum_congr rfl hterm, sum_mk]
  rfl

/-- The Pell identity `A n ^ 2 - 2 * B n ^ 2 = -1`. -/
lemma pell (n : ℕ) : A n ^ 2 - 2 * B n ^ 2 = -1 := by
  have hn : ((⟨1, 1⟩ : Zsqrtd 2) ^ (2 * n + 1)).norm
      = (Zsqrtd.norm (⟨1, 1⟩ : Zsqrtd 2)) ^ (2 * n + 1) :=
    map_pow (Zsqrtd.normMonoidHom (d := 2)) _ _
  rw [pow_eq n] at hn
  have h1 : (Zsqrtd.norm (⟨1, 1⟩ : Zsqrtd 2)) = -1 := by simp [Zsqrtd.norm_def]
  rw [h1, Odd.neg_one_pow ⟨n, by ring⟩, Zsqrtd.norm_def] at hn
  simp only at hn
  linear_combination hn

/-- Modulo `5` we have `2 ^ n * S n = A n`. -/
lemma key (n : ℕ) : (2 : ZMod 5) ^ n * (S n : ZMod 5) = ((A n : ℤ) : ZMod 5) := by
  rw [S, A]
  push_cast
  rw [Finset.mul_sum]
  rw [← Finset.sum_range_reflect
    (fun k => (2 : ZMod 5) ^ n * ((((2 * n + 1).choose (2 * k + 1) : ℕ) : ZMod 5) * 2 ^ (3 * k)))]
  refine Finset.sum_congr rfl ?_
  intro k hk
  simp only [Finset.mem_range] at hk
  have hidx : n + 1 - 1 - k = n - k := by omega
  simp only [hidx]
  have hch : (2 * n + 1).choose (2 * (n - k) + 1) = (2 * n + 1).choose (2 * k) := by
    have h : 2 * (n - k) + 1 = (2 * n + 1) - 2 * k := by omega
    rw [h, Nat.choose_symm (by omega)]
  rw [hch]
  have hexp : (2 : ZMod 5) ^ n * 2 ^ (3 * (n - k)) = 2 ^ k := by
    rw [← pow_add]
    have h4 : n + 3 * (n - k) = 4 * (n - k) + k := by omega
    rw [h4, pow_add, pow_mul]
    have h16 : ((2 : ZMod 5) ^ 4) = 1 := by decide
    rw [h16, one_pow, one_mul]
  calc (2 : ZMod 5) ^ n * ((((2 * n + 1).choose (2 * k) : ℕ) : ZMod 5) * 2 ^ (3 * (n - k)))
      = (((2 * n + 1).choose (2 * k) : ℕ) : ZMod 5) * ((2 : ZMod 5) ^ n * 2 ^ (3 * (n - k))) := by
        ring
    _ = _ := by rw [hexp]

/-- **IMO 1974, Problem 3.** For every `n ≥ 0` the number
`∑_{k=0}^{n} C(2n+1, 2k+1) * 2^(3k)` is not divisible by `5`. -/
theorem imo1974_p3 (n : ℕ) :
    ¬ (5 ∣ ∑ k ∈ Finset.range (n + 1), (2 * n + 1).choose (2 * k + 1) * 2 ^ (3 * k)) := by
  intro hdvd
  have hS : ((S n : ℕ) : ZMod 5) = 0 := (ZMod.natCast_eq_zero_iff (S n) 5).2 hdvd
  have hA : ((A n : ℤ) : ZMod 5) = 0 := by rw [← key n, hS, mul_zero]
  have hpell : ((A n : ℤ) : ZMod 5) ^ 2 - 2 * ((B n : ℤ) : ZMod 5) ^ 2 = -1 := by
    have h := congrArg (fun x : ℤ => ((x : ZMod 5))) (pell n)
    push_cast at h
    simpa using h
  rw [hA] at hpell
  have hno : ∀ b : ZMod 5, (0 : ZMod 5) ^ 2 - 2 * b ^ 2 ≠ -1 := by decide
  exact hno _ hpell

end IMO1974P3
