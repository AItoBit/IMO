import Mathlib

open scoped BigOperators
open scoped Nat

set_option maxHeartbeats 1000000

/-!
# IMO 1995 Problem 6

Let `p` be an odd prime.  The number of `p`-element subsets `A` of `{1, 2, …, 2p}`
whose element sum is divisible by `p` is `(C(2p, p) - 2)/p + 2`.

The proof uses the model `G p = ZMod p × Fin 2` for the ground set `{1, …, 2p}`
(an element `n` corresponds to its residue together with the information of which
half of the interval it lies in), and a free shift action of `ZMod p` on the first
half of the ground set.
-/

namespace IMO1995P6

open Finset

/-- The model of the ground set `{1, 2, …, 2p}`: a residue mod `p` together with a
half-indicator. -/
abbrev G (p : ℕ) : Type := ZMod p × Fin 2

variable {p : ℕ} [NeZero p]

/-- The `i`-th half of the ground set. -/
def half (p : ℕ) [NeZero p] (i : Fin 2) : Finset (G p) :=
  {b : G p | b.2 = i}

/-- The number of elements of `B` lying in the first half. -/
def mlen (B : Finset (G p)) : ℕ := (B.filter (fun b => b.2 = 0)).card

/-- Shift by `k` on the first half, identity on the second half. -/
def sh (k : ZMod p) (b : G p) : G p := (b.1 + (if b.2 = 0 then k else 0), b.2)

/-- All `p`-element subsets of the ground set. -/
def S (p : ℕ) [NeZero p] : Finset (Finset (G p)) := powersetCard p univ

/-- The `p`-element subsets that meet both halves. -/
def X (p : ℕ) [NeZero p] : Finset (Finset (G p)) :=
  (S p).filter (fun B => 0 < mlen B ∧ mlen B < p)

/-- The residue-sum of a subset of the model. -/
def rsum (B : Finset (G p)) : ZMod p := ∑ b ∈ B, b.1

lemma card_half (i : Fin 2) : (half p i).card = p := by
  have h : half p i = (univ : Finset (ZMod p)) ×ˢ ({i} : Finset (Fin 2)) := by
    ext ⟨r, j⟩; simp [half, eq_comm]
  rw [h, card_product]
  simp [ZMod.card]

omit [NeZero p] in
lemma sh_injective (k : ZMod p) : Function.Injective (sh (p := p) k) := by
  rintro ⟨r, i⟩ ⟨r', i'⟩ h
  simp only [sh, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  subst h2
  simp_all

omit [NeZero p] in
lemma mlen_le_card (B : Finset (G p)) : mlen B ≤ B.card :=
  card_filter_le _ _

omit [NeZero p] in
lemma card_sh_image (k : ZMod p) (B : Finset (G p)) :
    (B.image (sh k)).card = B.card :=
  card_image_of_injective _ (sh_injective k)

omit [NeZero p] in
lemma mlen_sh_image (k : ZMod p) (B : Finset (G p)) :
    mlen (B.image (sh k)) = mlen B := by
  classical
  unfold mlen
  rw [Finset.filter_image, card_image_of_injective _ (sh_injective k)]
  rfl

omit [NeZero p] in
lemma rsum_sh_image (k : ZMod p) (B : Finset (G p)) :
    rsum (B.image (sh k)) = rsum B + (mlen B : ZMod p) * k := by
  classical
  unfold rsum
  rw [Finset.sum_image (fun a _ b _ h => sh_injective k h)]
  have : ∀ b ∈ B, (sh k b).1 = b.1 + (if b.2 = 0 then k else 0) := by
    intro b _; rfl
  rw [Finset.sum_congr rfl this, Finset.sum_add_distrib]
  congr 1
  rw [← Finset.sum_filter]
  simp [mlen, mul_comm]

lemma eq_half_zero_of_mlen (B : Finset (G p)) (hB : B.card = p) (h : mlen B = p) :
    B = half p 0 := by
  have hfe : B.filter (fun b => b.2 = 0) = B :=
    Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by rw [hB]; exact h.ge)
  have hsub : B ⊆ half p 0 := by
    intro b hb
    have hb' : b ∈ B.filter (fun b => b.2 = 0) := by rw [hfe]; exact hb
    simp [half, (Finset.mem_filter.mp hb').2]
  exact Finset.eq_of_subset_of_card_le hsub (by rw [card_half, hB])

lemma eq_half_one_of_mlen (B : Finset (G p)) (hB : B.card = p) (h : mlen B = 0) :
    B = half p 1 := by
  have hsub : B ⊆ half p 1 := by
    intro b hb
    have hnot : b ∉ B.filter (fun b => b.2 = 0) := by
      rw [Finset.card_eq_zero.mp h]; simp
    simp only [Finset.mem_filter, not_and] at hnot
    have hb2 : b.2 ≠ 0 := hnot hb
    have hb1 : b.2 = 1 := by omega
    simp [half, hb1]
  exact Finset.eq_of_subset_of_card_le hsub (by rw [card_half, hB])

lemma sum_univ_zmod_eq_zero (hodd : Odd p) : ∑ r : ZMod p, r = 0 := by
  have h : ∑ r : ZMod p, r = ∑ r : ZMod p, (-r) :=
    Fintype.sum_equiv (Equiv.neg (ZMod p)) _ _ (fun x => by simp)
  rw [Finset.sum_neg_distrib] at h
  refine (ZMod.add_self_eq_zero_iff_eq_zero hodd).mp ?_
  nth_rewrite 1 [h]
  ring

lemma rsum_half (hodd : Odd p) (i : Fin 2) : rsum (half p i) = 0 := by
  have h : half p i = (univ : Finset (ZMod p)) ×ˢ ({i} : Finset (Fin 2)) := by
    ext ⟨r, j⟩; simp [half, eq_comm]
  rw [rsum, h, Finset.sum_product]
  simpa using sum_univ_zmod_eq_zero hodd

lemma half_mem_S (i : Fin 2) : half p i ∈ S p := by
  simp [S, mem_powersetCard, card_half]

lemma mlen_half_zero : mlen (half p 0) = p := by
  unfold mlen
  rw [Finset.filter_true_of_mem (by intro b hb; simpa [half] using hb)]
  exact card_half 0

lemma mlen_half_one : mlen (half p 1) = 0 := by
  unfold mlen
  rw [Finset.filter_false_of_mem (by intro b hb; simp [half] at hb; simp [hb])]
  rfl

lemma half_ne : half p 0 ≠ half p 1 := by
  intro h
  have h0 : ((0 : ZMod p), (0 : Fin 2)) ∈ half p 0 := by simp [half]
  rw [h] at h0
  simp [half] at h0

lemma card_univ_G : (univ : Finset (G p)).card = 2 * p := by
  simp [Finset.card_univ, ZMod.card, Nat.mul_comm]

lemma card_S : (S p).card = (2 * p).choose p := by
  rw [S, Finset.card_powersetCard, card_univ_G]

/-- `S` is `X` together with the two halves. -/
lemma S_eq : S p = insert (half p 0) (insert (half p 1) (X p)) := by
  ext B
  constructor
  · intro hB
    have hcard : B.card = p := by
      simpa [S, Finset.mem_powersetCard] using hB
    rcases Nat.lt_or_ge 0 (mlen B) with h0 | h0
    · rcases Nat.lt_or_ge (mlen B) p with h1 | h1
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_filter.mpr ⟨hB, h0, h1⟩))
      · have hm : mlen B = p := le_antisymm (le_trans (mlen_le_card B) (le_of_eq hcard)) h1
        exact Finset.mem_insert.mpr (Or.inl (eq_half_zero_of_mlen B hcard hm))
    · have hm : mlen B = 0 := Nat.le_zero.mp h0
      exact Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl
        (eq_half_one_of_mlen B hcard hm)))
  · intro hB
    rcases Finset.mem_insert.mp hB with h | h
    · exact h ▸ half_mem_S 0
    · rcases Finset.mem_insert.mp h with h | h
      · exact h ▸ half_mem_S 1
      · exact (Finset.mem_filter.mp h).1

lemma half_zero_notMem_X : half p 0 ∉ X p := by
  intro h
  have h2 := (Finset.mem_filter.mp h).2.2
  rw [mlen_half_zero] at h2
  exact lt_irrefl _ h2

lemma half_one_notMem_X : half p 1 ∉ X p := by
  intro h
  have h2 := (Finset.mem_filter.mp h).2.1
  rw [mlen_half_one] at h2
  exact lt_irrefl _ h2

lemma card_X : (X p).card = (2 * p).choose p - 2 := by
  have h0 : half p 0 ∉ insert (half p 1) (X p) := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨half_ne, half_zero_notMem_X⟩
  have hS := card_S (p := p)
  rw [S_eq, Finset.card_insert_of_notMem h0,
    Finset.card_insert_of_notMem half_one_notMem_X] at hS
  omega

lemma sh_mem_X {B : Finset (G p)} (hB : B ∈ X p) (k : ZMod p) : B.image (sh k) ∈ X p := by
  obtain ⟨hS, h0, h1⟩ := Finset.mem_filter.mp hB
  have hc : B.card = p := by simpa [S, Finset.mem_powersetCard] using hS
  refine Finset.mem_filter.mpr ⟨?_, ?_, ?_⟩
  · simp [S, Finset.mem_powersetCard, card_sh_image, hc]
  · rwa [mlen_sh_image]
  · rwa [mlen_sh_image]

omit [NeZero p] in
lemma sh_comp (a b : ZMod p) (x : G p) : sh a (sh b x) = sh (a + b) x := by
  simp only [sh]
  split <;> simp [add_comm, add_left_comm]

omit [NeZero p] in
lemma sh_zero_apply (x : G p) : sh (0 : ZMod p) x = x := by
  simp only [sh]
  split <;> simp

omit [NeZero p] in
lemma image_sh_add (a b : ZMod p) (B : Finset (G p)) :
    (B.image (sh b)).image (sh a) = B.image (sh (a + b)) := by
  rw [Finset.image_image]
  congr 1
  funext x
  exact sh_comp a b x

omit [NeZero p] in
lemma image_sh_zero (B : Finset (G p)) : B.image (sh (0 : ZMod p)) = B := by
  have h : sh (0 : ZMod p) = id := funext sh_zero_apply
  rw [h, Finset.image_id]

lemma mlen_cast_ne_zero {B : Finset (G p)} (hB : B ∈ X p) :
    ((mlen B : ℕ) : ZMod p) ≠ 0 := by
  obtain ⟨-, h0, h1⟩ := Finset.mem_filter.mp hB
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro hdvd
  have := Nat.le_of_dvd h0 hdvd
  omega

/-- All residue-sum fibers of `X` have the same cardinality. -/
lemma card_fiber_eq (hp : p.Prime) (j : ZMod p) :
    ((X p).filter (fun B => rsum B = j)).card = ((X p).filter (fun B => rsum B = 0)).card := by
  haveI := Fact.mk hp
  refine Finset.card_bij'
    (fun B _ => B.image (sh (-j * ((mlen B : ℕ) : ZMod p)⁻¹)))
    (fun C _ => C.image (sh (j * ((mlen C : ℕ) : ZMod p)⁻¹)))
    ?_ ?_ ?_ ?_
  · intro B hB
    obtain ⟨hBX, hBj⟩ := Finset.mem_filter.mp hB
    have hm := mlen_cast_ne_zero hBX
    refine Finset.mem_filter.mpr ⟨sh_mem_X hBX _, ?_⟩
    rw [rsum_sh_image, hBj]
    field_simp
    ring
  · intro C hC
    obtain ⟨hCX, hC0⟩ := Finset.mem_filter.mp hC
    have hm := mlen_cast_ne_zero hCX
    refine Finset.mem_filter.mpr ⟨sh_mem_X hCX _, ?_⟩
    rw [rsum_sh_image, hC0]
    field_simp
    ring
  · intro B hB
    simp only
    rw [mlen_sh_image, image_sh_add]
    have : j * ((mlen B : ℕ) : ZMod p)⁻¹ + -j * ((mlen B : ℕ) : ZMod p)⁻¹ = 0 := by ring
    rw [this, image_sh_zero]
  · intro C hC
    simp only
    rw [mlen_sh_image, image_sh_add]
    have : -j * ((mlen C : ℕ) : ZMod p)⁻¹ + j * ((mlen C : ℕ) : ZMod p)⁻¹ = 0 := by ring
    rw [this, image_sh_zero]

lemma card_X_eq_mul (hp : p.Prime) :
    (X p).card = p * ((X p).filter (fun B => rsum B = 0)).card := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise (f := fun B => rsum B)
    (s := X p) (t := (univ : Finset (ZMod p))) (fun B _ => Finset.mem_univ _)
  rw [h, Finset.sum_congr rfl (fun j _ => card_fiber_eq hp j), Finset.sum_const,
    Finset.card_univ, ZMod.card, smul_eq_mul]

/-- The answer in the model. -/
theorem card_model (hp : p.Prime) (hodd : Odd p) :
    ((S p).filter (fun B => rsum B = 0)).card = ((2 * p).choose p - 2) / p + 2 := by
  have hsplit : (S p).filter (fun B => rsum B = 0)
      = insert (half p 0) (insert (half p 1) ((X p).filter (fun B => rsum B = 0))) := by
    rw [S_eq, Finset.filter_insert, Finset.filter_insert]
    simp [rsum_half hodd]
  have h0 : half p 0 ∉ insert (half p 1) ((X p).filter (fun B => rsum B = 0)) := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨half_ne, fun h => half_zero_notMem_X (Finset.mem_filter.mp h).1⟩
  have h1 : half p 1 ∉ (X p).filter (fun B => rsum B = 0) :=
    fun h => half_one_notMem_X (Finset.mem_filter.mp h).1
  rw [hsplit, Finset.card_insert_of_notMem h0, Finset.card_insert_of_notMem h1]
  have hX := card_X_eq_mul (p := p) hp
  rw [card_X] at hX
  have hdiv : ((2 * p).choose p - 2) / p = ((X p).filter (fun B => rsum B = 0)).card := by
    rw [hX]
    exact Nat.mul_div_cancel_left _ hp.pos
  omega

/-! ### Transfer to the interval `{1, …, 2p}` -/

/-- Encoding of the model into `{1, 2, …, 2p}`. -/
def enc (b : G p) : ℕ := b.1.val + 1 + p * b.2.val

/-- Decoding of `{1, 2, …, 2p}` into the model. -/
def dec (p : ℕ) [NeZero p] (n : ℕ) : G p := (((n - 1 : ℕ) : ZMod p), if n ≤ p then 0 else 1)

lemma enc_mem_Icc (b : G p) : enc b ∈ Finset.Icc 1 (2 * p) := by
  have h1 : b.1.val < p := ZMod.val_lt b.1
  have h2 : b.2.val ≤ 1 := Nat.lt_succ_iff.mp b.2.isLt
  simp only [Finset.mem_Icc, enc]
  constructor
  · omega
  · calc b.1.val + 1 + p * b.2.val ≤ (p - 1) + 1 + p * 1 := by
          have := Nat.mul_le_mul_left p h2
          omega
      _ ≤ 2 * p := by omega

lemma enc_injective : Function.Injective (enc (p := p)) := by
  rintro ⟨r, i⟩ ⟨r', i'⟩ h
  have h1 : r.val < p := ZMod.val_lt r
  have h1' : r'.val < p := ZMod.val_lt r'
  have h2 : i.val ≤ 1 := Nat.lt_succ_iff.mp i.isLt
  have h2' : i'.val ≤ 1 := Nat.lt_succ_iff.mp i'.isLt
  simp only [enc] at h
  have hi : i.val = i'.val := by
    rcases Nat.lt_trichotomy i.val i'.val with hlt | heq | hgt
    · have : p * i.val + p ≤ p * i'.val := by
        have : i.val + 1 ≤ i'.val := hlt
        calc p * i.val + p = p * (i.val + 1) := by ring
          _ ≤ p * i'.val := Nat.mul_le_mul_left p this
      omega
    · exact heq
    · have : p * i'.val + p ≤ p * i.val := by
        have : i'.val + 1 ≤ i.val := hgt
        calc p * i'.val + p = p * (i'.val + 1) := by ring
          _ ≤ p * i.val := Nat.mul_le_mul_left p this
      omega
  have hr : r.val = r'.val := by rw [hi] at h; omega
  have : r = r' := ZMod.val_injective p hr
  simp [this, Fin.ext_iff, hi]

lemma enc_dec {n : ℕ} (hn : n ∈ Finset.Icc 1 (2 * p)) : enc (dec p n) = n := by
  simp only [Finset.mem_Icc] at hn
  simp only [enc, dec, ZMod.val_natCast]
  by_cases h : n ≤ p
  · have : (n - 1) % p = n - 1 := Nat.mod_eq_of_lt (by omega)
    simp [h, this]
    omega
  · have hlt : n - 1 - p < p := by omega
    have : (n - 1) % p = n - 1 - p := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hlt]
    simp [h, this]
    omega

lemma enc_cast (b : G p) : ((enc b : ℕ) : ZMod p) = b.1 + 1 := by
  simp [enc, ZMod.natCast_val, ZMod.cast_id]

lemma cast_sum_image_enc (B : Finset (G p)) (hcard : B.card = p) :
    ((∑ n ∈ B.image enc, n : ℕ) : ZMod p) = rsum B := by
  rw [Finset.sum_image (fun a _ b _ h => enc_injective h), Nat.cast_sum,
    Finset.sum_congr rfl (fun b (_ : b ∈ B) => enc_cast b), Finset.sum_add_distrib,
    Finset.sum_const, hcard]
  simp [rsum]

end IMO1995P6

open Finset IMO1995P6 in
/-- **IMO 1995, Problem 6.**  For an odd prime `p`, the number of `p`-element subsets
of `{1, 2, …, 2p}` whose elements sum to a multiple of `p` equals
`(binom(2p, p) - 2)/p + 2`. -/
theorem imo1995_p6 (p : ℕ) (hp : p.Prime) (hodd : Odd p) :
    (((Finset.Icc 1 (2 * p)).powerset.filter
        (fun A => A.card = p ∧ p ∣ ∑ x ∈ A, x)).card)
      = ((2 * p).choose p - 2) / p + 2 := by
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  classical
  have key : ((S p).filter (fun B => rsum B = 0)).card
      = (((Finset.Icc 1 (2 * p)).powerset.filter
          (fun A => A.card = p ∧ p ∣ ∑ x ∈ A, x)).card) := by
    refine Finset.card_bij (fun B _ => B.image enc) ?_ ?_ ?_
    · intro B hB
      obtain ⟨hBS, hB0⟩ := Finset.mem_filter.mp hB
      have hcard : B.card = p := by simpa [S, Finset.mem_powersetCard] using hBS
      refine Finset.mem_filter.mpr ⟨?_, ?_, ?_⟩
      · rw [Finset.mem_powerset]
        intro n hn
        obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hn
        exact enc_mem_Icc b
      · rw [Finset.card_image_of_injective _ enc_injective, hcard]
      · exact (ZMod.natCast_eq_zero_iff _ p).mp (by rw [cast_sum_image_enc B hcard, hB0])
    · exact fun B _ B' _ h => Finset.image_injective enc_injective h
    · intro A hA
      rw [Finset.mem_filter, Finset.mem_powerset] at hA
      obtain ⟨hAsub, hAcard, hAdvd⟩ := hA
      have hdec : ∀ n ∈ A, enc (dec p n) = n := fun n hn => enc_dec (hAsub hn)
      have himg : (A.image (dec p)).image enc = A := by
        rw [Finset.image_image]
        rw [show (enc ∘ dec p) = fun n => enc (dec p n) from rfl]
        rw [Finset.image_congr (g := id) (fun n hn => hdec n hn), Finset.image_id]
      have hinj : Set.InjOn (dec p) A := by
        intro a ha b hb hab
        rw [← hdec a ha, ← hdec b hb, hab]
      have hcardB : (A.image (dec p)).card = p := by
        rw [Finset.card_image_of_injOn hinj, hAcard]
      refine ⟨A.image (dec p), ?_, himg⟩
      refine Finset.mem_filter.mpr ⟨by simp [S, Finset.mem_powersetCard, hcardB], ?_⟩
      have hsum := cast_sum_image_enc (A.image (dec p)) hcardB
      rw [himg] at hsum
      rw [← hsum, ZMod.natCast_eq_zero_iff]
      exact hAdvd
  rw [← key, card_model hp hodd]

