import Mathlib

/-!
# IMO 1998 (functional equation): least possible value of `f 1998`

We consider functions `f` from the positive integers to the positive integers
satisfying
`f (t ^ 2 * f s) = s * (f t) ^ 2` for all positive integers `s, t`,
and show that the least possible value of `f 1998` is `120`.

Positive integers are modelled as natural numbers together with explicit
positivity hypotheses.
-/

namespace IMO1998

/-- The functional equation, for functions of the positive integers into
themselves (modelled as `ℕ → ℕ` together with positivity hypotheses). -/
def Good (f : ℕ → ℕ) : Prop :=
  (∀ n, 0 < n → 0 < f n) ∧ ∀ s t, 0 < s → 0 < t → f (t ^ 2 * f s) = s * f t ^ 2

/-! ## The construction attaining the value `120` -/

/-- The involution of the primes swapping `2 ↔ 3` and `5 ↔ 37`. -/
def swapPrime (p : ℕ) : ℕ :=
  if p = 2 then 3 else if p = 3 then 2 else if p = 5 then 37 else if p = 37 then 5 else p

lemma swapPrime_swapPrime (p : ℕ) : swapPrime (swapPrime p) = p := by
  unfold swapPrime; split_ifs <;> omega

lemma swapPrime_pos {p : ℕ} (hp : 0 < p) : 0 < swapPrime p := by
  unfold swapPrime; split_ifs <;> omega

lemma swapPrime_prime {p : ℕ} (hp : p.Prime) : (swapPrime p).Prime := by
  unfold swapPrime
  split_ifs with h1 h2 h3 h4 <;> first | assumption | norm_num

/-- The completely multiplicative extension of `swapPrime`. -/
def F (n : ℕ) : ℕ := n.factorization.prod fun p k => swapPrime p ^ k

lemma F_one : F 1 = 1 := by simp [F]

lemma F_pos (n : ℕ) : 0 < F n := by
  rw [F, Finsupp.prod]
  refine Finset.prod_pos fun p hp => pow_pos ?_ _
  exact swapPrime_pos (Nat.pos_of_mem_primeFactors (by simpa using hp))

lemma F_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) : F (m * n) = F m * F n := by
  unfold F
  rw [Nat.factorization_mul hm hn]
  exact Finsupp.prod_add_index' (by intro p; simp) (by intro p a b; rw [pow_add])

lemma F_prime {p : ℕ} (hp : p.Prime) : F p = swapPrime p := by
  unfold F
  rw [hp.factorization]
  rw [Finsupp.prod_single_index (by simp)]
  simp

lemma F_F (n : ℕ) (hn : n ≠ 0) : F (F n) = n := by
  induction n using Nat.recOnMul with
  | zero => exact absurd rfl hn
  | one => simp [F_one]
  | prime p hp =>
      rw [F_prime hp, F_prime (swapPrime_prime hp), swapPrime_swapPrime]
  | mul a b iha ihb =>
      have ha : a ≠ 0 := by rintro rfl; simp at hn
      have hb : b ≠ 0 := by rintro rfl; simp at hn
      rw [F_mul ha hb, F_mul (F_pos a).ne' (F_pos b).ne', iha ha, ihb hb]

lemma good_F : Good F := by
  refine ⟨fun n _ => F_pos n, ?_⟩
  intro s t hs ht
  have h1 : F (t ^ 2 * F s) = F (t ^ 2) * F (F s) := F_mul (by positivity) (F_pos s).ne'
  rw [h1, F_F s hs.ne', sq, F_mul ht.ne' ht.ne', sq]
  ring

lemma F_1998 : F 1998 = 120 := by
  have h2 : F 2 = 3 := by rw [F_prime (by norm_num)]; rfl
  have h3 : F 3 = 2 := by rw [F_prime (by norm_num)]; rfl
  have h37 : F 37 = 5 := by rw [F_prime (by norm_num)]; rfl
  have : (1998 : ℕ) = 2 * (3 * (3 * (3 * 37))) := by norm_num
  rw [this, F_mul (by norm_num) (by norm_num), F_mul (by norm_num) (by norm_num),
    F_mul (by norm_num) (by norm_num), F_mul (by norm_num) (by norm_num), h2, h3, h37]

/-! ## The lower bound -/

lemma prime_ge_five {x : ℕ} (hx : x.Prime) (h2 : x ≠ 2) (h3 : x ≠ 3) : 5 ≤ x := by
  by_contra h
  have h2le := hx.two_le
  interval_cases x
  · exact h2 rfl
  · exact h3 rfl
  · norm_num at hx

lemma prime_ge_three {x : ℕ} (hx : x.Prime) (h2 : x ≠ 2) : 3 ≤ x := by
  have := hx.two_le
  omega

/-- If `p, q, r` are pairwise distinct primes then `p * q ^ 3 * r ≥ 120`. -/
lemma distinct_primes_bound {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) : 120 ≤ p * q ^ 3 * r := by
  have hp2 := hp.two_le
  have hq2 := hq.two_le
  have hr2 := hr.two_le
  rcases eq_or_ne q 2 with rfl | hq2'
  · -- p, r are odd distinct primes, so p * r ≥ 15
    have hp3 : 3 ≤ p := prime_ge_three hp hpq
    have hr3 : 3 ≤ r := prime_ge_three hr (Ne.symm hqr)
    have hpr15 : 15 ≤ p * r := by
      rcases eq_or_ne p 3 with rfl | hp3' 
      · have : 5 ≤ r := prime_ge_five hr (Ne.symm hqr) (Ne.symm hpr)
        nlinarith
      · have hp5 : 5 ≤ p := prime_ge_five hp hpq hp3'
        nlinarith
    nlinarith
  · rcases eq_or_ne q 3 with rfl | hq3'
    · have hpr10 : 10 ≤ p * r := by
        rcases eq_or_ne p 2 with rfl | hp2' 
        · have : 5 ≤ r := prime_ge_five hr (Ne.symm hpr) (Ne.symm hqr)
          nlinarith
        · have hp5 : 5 ≤ p := prime_ge_five hp hp2' hpq
          nlinarith
      nlinarith
    · have hq5 : 5 ≤ q := prime_ge_five hq hq2' hq3'
      have hq125 : 125 ≤ q ^ 3 := by simpa using Nat.pow_le_pow_left hq5 3
      calc (120 : ℕ) ≤ 2 * 125 * 2 := by norm_num
        _ ≤ p * q ^ 3 * r := Nat.mul_le_mul (Nat.mul_le_mul hp2 hq125) hr2

section Lower

variable {f : ℕ → ℕ}

/-- `f (f s) = s * f 1 ^ 2`. -/
lemma ff (hf : Good f) {s : ℕ} (hs : 0 < s) : f (f s) = s * f 1 ^ 2 := by
  simpa using hf.2 s 1 hs one_pos

lemma f_one_pos (hf : Good f) : 0 < f 1 := hf.1 1 one_pos

/-- `f (f 1 ^ 2 * x) = f 1 ^ 2 * f x`. -/
lemma f_ksq_mul (hf : Good f) {x : ℕ} (hx : 0 < x) : f (f 1 ^ 2 * x) = f 1 ^ 2 * f x := by
  have h1 : f (f x) = x * f 1 ^ 2 := ff hf hx
  have h2 : f (f (f x)) = f x * f 1 ^ 2 := ff hf (hf.1 x hx)
  rw [h1] at h2
  rw [mul_comm (f 1 ^ 2) x, h2, mul_comm]

/-- `f (t ^ 2 * f 1) = f t ^ 2`. -/
lemma f_sq_mul_k (hf : Good f) {t : ℕ} (ht : 0 < t) : f (t ^ 2 * f 1) = f t ^ 2 := by
  simpa using hf.2 1 t one_pos ht

/-- `f (f 1 * t) = f 1 * f t`. -/
lemma f_k_mul (hf : Good f) {t : ℕ} (ht : 0 < t) : f (f 1 * t) = f 1 * f t := by
  have hk : 0 < f 1 := f_one_pos hf
  have key : f (f 1 * t) ^ 2 = (f 1 * f t) ^ 2 := by
    have e1 : f ((f 1 * t) ^ 2 * f 1) = f (f 1 * t) ^ 2 :=
      f_sq_mul_k hf (by positivity)
    have e2 : (f 1 * t) ^ 2 * f 1 = f 1 ^ 2 * (f 1 * t ^ 2) := by ring
    have e3 : f (f 1 ^ 2 * (f 1 * t ^ 2)) = f 1 ^ 2 * f (f 1 * t ^ 2) :=
      f_ksq_mul hf (by positivity)
    have e4 : f (f 1 * t ^ 2) = f t ^ 2 := by
      rw [mul_comm]; exact f_sq_mul_k hf ht
    rw [← e1, e2, e3, e4]; ring
  exact Nat.pow_left_injective (n := 2) (by norm_num) key

/-- `f 1 * f (t ^ 2) = f t ^ 2`. -/
lemma k_mul_f_sq (hf : Good f) {t : ℕ} (ht : 0 < t) : f 1 * f (t ^ 2) = f t ^ 2 := by
  rw [← f_k_mul hf (by positivity : (0:ℕ) < t ^ 2), mul_comm (f 1) (t ^ 2)]
  exact f_sq_mul_k hf ht

/-- `f 1 * f (a * b) = f a * f b`. -/
lemma k_mul_f_mul (hf : Good f) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    f 1 * f (a * b) = f a * f b := by
  have hk : 0 < f 1 := f_one_pos hf
  have hb2 : 0 < b ^ 2 := by positivity
  -- the functional equation with `s = f (b ^ 2)`, `t = a`
  have h1 : f (a ^ 2 * f (f (b ^ 2))) = f (b ^ 2) * f a ^ 2 :=
    hf.2 (f (b ^ 2)) a (hf.1 _ hb2) ha
  have h2 : f (f (b ^ 2)) = b ^ 2 * f 1 ^ 2 := ff hf hb2
  rw [h2] at h1
  have h3 : a ^ 2 * (b ^ 2 * f 1 ^ 2) = f 1 ^ 2 * (a * b) ^ 2 := by ring
  rw [h3, f_ksq_mul hf (by positivity)] at h1
  -- now `f 1 ^ 2 * f ((a * b) ^ 2) = f (b ^ 2) * f a ^ 2`
  have h4 : f 1 * f ((a * b) ^ 2) = f (a * b) ^ 2 := k_mul_f_sq hf (by positivity)
  have h5 : f 1 * f (b ^ 2) = f b ^ 2 := k_mul_f_sq hf hb
  have key : (f 1 * f (a * b)) ^ 2 = (f a * f b) ^ 2 := by
    have : f 1 * (f 1 ^ 2 * f ((a * b) ^ 2)) = f 1 * (f (b ^ 2) * f a ^ 2) := by rw [h1]
    calc (f 1 * f (a * b)) ^ 2 = f 1 ^ 2 * (f 1 * f ((a * b) ^ 2)) := by rw [h4]; ring
      _ = f 1 * (f 1 ^ 2 * f ((a * b) ^ 2)) := by ring
      _ = f 1 * (f (b ^ 2) * f a ^ 2) := this
      _ = (f 1 * f (b ^ 2)) * f a ^ 2 := by ring
      _ = f b ^ 2 * f a ^ 2 := by rw [h5]
      _ = (f a * f b) ^ 2 := by ring
  exact Nat.pow_left_injective (n := 2) (by norm_num) key

lemma k_pow_mul (hf : Good f) {t : ℕ} (ht : 0 < t) (n : ℕ) :
    f 1 ^ n * f (t ^ (n + 1)) = f t ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hpow : 0 < t ^ (n + 1) := by positivity
      have h := k_mul_f_mul hf ht hpow
      calc f 1 ^ (n + 1) * f (t ^ (n + 2))
          = f 1 ^ n * (f 1 * f (t * t ^ (n + 1))) := by
            rw [show t ^ (n + 2) = t * t ^ (n + 1) by ring]; ring
        _ = f 1 ^ n * (f t * f (t ^ (n + 1))) := by rw [h]
        _ = f t * (f 1 ^ n * f (t ^ (n + 1))) := by ring
        _ = f t * f t ^ (n + 1) := by rw [ih]
        _ = f t ^ (n + 2) := by ring

lemma k_dvd (hf : Good f) {t : ℕ} (ht : 0 < t) : f 1 ∣ f t := by
  have hk : 0 < f 1 := f_one_pos hf
  have hft : 0 < f t := hf.1 t ht
  rw [← Nat.factorization_le_iff_dvd hk.ne' hft.ne']
  rw [Finsupp.le_def]
  intro p
  set a := (f 1).factorization p with ha
  set b := (f t).factorization p with hb
  by_contra hcon
  push_neg at hcon
  -- `f 1 ^ n ∣ f t ^ (n + 1)` for every `n`
  set n := b + 1 with hn
  have hdvd : f 1 ^ n ∣ f t ^ (n + 1) := ⟨f (t ^ (n + 1)), (k_pow_mul hf ht n).symm⟩
  have hle : (f 1 ^ n).factorization ≤ (f t ^ (n + 1)).factorization :=
    (Nat.factorization_le_iff_dvd (by positivity) (by positivity)).mpr hdvd
  rw [Finsupp.le_def] at hle
  have := hle p
  rw [Nat.factorization_pow, Nat.factorization_pow] at this
  simp only [Finsupp.smul_apply, smul_eq_mul, ← ha, ← hb] at this
  nlinarith

end Lower

section Normalized

variable {g : ℕ → ℕ}

/-- A completely multiplicative involution of the positive integers maps primes to primes. -/
lemma normalized_prime (hpos : ∀ n, 0 < n → 0 < g n)
    (hmul : ∀ a b, 0 < a → 0 < b → g (a * b) = g a * g b)
    (hinv : ∀ a, 0 < a → g (g a) = a) (hg1 : g 1 = 1) {p : ℕ} (hp : p.Prime) :
    (g p).Prime := by
  have hp0 : 0 < p := hp.pos
  have hgp : 0 < g p := hpos p hp0
  have hone : ∀ m, 0 < m → g m = 1 → m = 1 := by
    intro m hm h
    have := hinv m hm
    rw [h, hg1] at this
    omega
  refine Nat.prime_def.mpr ⟨?_, ?_⟩
  · rcases Nat.lt_or_ge (g p) 2 with h | h
    · have hgp1 : g p = 1 := by omega
      exact absurd (hone p hp0 hgp1) hp.one_lt.ne'
    · exact h
  · intro m hm
    obtain ⟨n, hn⟩ := hm
    have hm0 : 0 < m := by
      rcases Nat.eq_zero_or_pos m with rfl | h
      · simp at hn; omega
      · exact h
    have hn0 : 0 < n := by
      rcases Nat.eq_zero_or_pos n with rfl | h
      · simp at hn; omega
      · exact h
    have hsplit : p = g m * g n := by
      have := hinv p hp0
      rw [hn, hmul m n hm0 hn0] at this
      omega
    rcases (Nat.Prime.eq_one_or_self_of_dvd hp (g m) ⟨g n, hsplit⟩) with h | h
    · exact Or.inl (hone m hm0 h)
    · right
      have hgn : g n = 1 := by
        rw [h] at hsplit
        have : p * 1 = p * g n := by simpa using hsplit
        exact (Nat.eq_of_mul_eq_mul_left hp0 this).symm
      have : n = 1 := hone n hn0 hgn
      rw [hn, this, mul_one]

/-- For a completely multiplicative involution `g` of the positive integers, `g 1998 ≥ 120`. -/
lemma normalized_bound (hpos : ∀ n, 0 < n → 0 < g n)
    (hmul : ∀ a b, 0 < a → 0 < b → g (a * b) = g a * g b)
    (hinv : ∀ a, 0 < a → g (g a) = a) (hg1 : g 1 = 1) : 120 ≤ g 1998 := by
  have hinj : ∀ a b, 0 < a → 0 < b → g a = g b → a = b := by
    intro a b ha hb h
    rw [← hinv a ha, ← hinv b hb, h]
  have h2 : (g 2).Prime := normalized_prime hpos hmul hinv hg1 (by norm_num)
  have h3 : (g 3).Prime := normalized_prime hpos hmul hinv hg1 (by norm_num)
  have h37 : (g 37).Prime := normalized_prime hpos hmul hinv hg1 (by norm_num)
  have e : g 1998 = g 2 * g 3 ^ 3 * g 37 := by
    have : (1998 : ℕ) = 2 * (3 * (3 * (3 * 37))) := by norm_num
    rw [this, hmul 2 _ (by norm_num) (by norm_num), hmul 3 _ (by norm_num) (by norm_num),
      hmul 3 _ (by norm_num) (by norm_num), hmul 3 37 (by norm_num) (by norm_num)]
    ring
  rw [e]
  refine distinct_primes_bound h2 h3 h37 ?_ ?_ ?_
  · intro h; have := hinj 2 3 (by norm_num) (by norm_num) h; omega
  · intro h; have := hinj 2 37 (by norm_num) (by norm_num) h; omega
  · intro h; have := hinj 3 37 (by norm_num) (by norm_num) h; omega

end Normalized

/-- The least possible value of `f 1998` is `120`. -/
theorem least_f_1998 : IsLeast {v : ℕ | ∃ f : ℕ → ℕ, Good f ∧ f 1998 = v} 120 := by
  constructor
  · exact ⟨F, good_F, F_1998⟩
  · rintro v ⟨f, hf, rfl⟩
    have hk : 0 < f 1 := f_one_pos hf
    set g : ℕ → ℕ := fun t => f t / f 1 with hgdef
    have hfg : ∀ t, 0 < t → f t = f 1 * g t := fun t ht =>
      (Nat.mul_div_cancel' (k_dvd hf ht)).symm
    have hpos : ∀ n, 0 < n → 0 < g n := by
      intro n hn
      have h := hf.1 n hn
      rw [hfg n hn] at h
      exact Nat.pos_of_ne_zero fun h0 => by simp [h0] at h
    have hmul : ∀ a b, 0 < a → 0 < b → g (a * b) = g a * g b := by
      intro a b ha hb
      have h := k_mul_f_mul hf ha hb
      rw [hfg (a * b) (by positivity), hfg a ha, hfg b hb, ← mul_assoc] at h
      refine Nat.eq_of_mul_eq_mul_left (show 0 < f 1 * f 1 by positivity) ?_
      rw [h]; ring
    have hinv : ∀ a, 0 < a → g (g a) = a := by
      intro a ha
      have ha' : 0 < g a := hpos a ha
      have h1 : f (f a) = a * f 1 ^ 2 := ff hf ha
      rw [hfg a ha, f_k_mul hf ha', hfg (g a) ha', ← mul_assoc] at h1
      refine Nat.eq_of_mul_eq_mul_left (show 0 < f 1 * f 1 by positivity) ?_
      rw [h1]; ring
    have hg1 : g 1 = 1 := by
      refine Nat.eq_of_mul_eq_mul_left hk ?_
      rw [← hfg 1 one_pos, mul_one]
    calc (120 : ℕ) ≤ g 1998 := normalized_bound hpos hmul hinv hg1
      _ ≤ f 1 * g 1998 := Nat.le_mul_of_pos_left _ hk
      _ = f 1998 := (hfg 1998 (by norm_num)).symm

end IMO1998
