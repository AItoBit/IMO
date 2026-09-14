import Mathlib

/-!
# IMO 1997, Problem 4 — silver matrices

An `n × n` matrix with entries in `S = {1, …, 2n-1}` is *silver* if for every `i` the `i`-th row
and the `i`-th column together contain all of `S`.

* (a) there is no silver matrix for `n = 1997`;
* (b) silver matrices exist for infinitely many `n`.

Both are proved, with no `sorry`.

## (a)

Let `n ≥ 2`. Since `|S| = 2n-1 > n`, some `m ∈ S` is not on the diagonal. The `i`-th cross has
exactly `2n-1` cells and its values exhaust `S`, so the value map is injective on it: each cross
holds exactly one `m`. Sending `i` to that cell is a map from `n` indices onto the set of
`m`-cells, and each `m`-cell `(r,c)` — necessarily off-diagonal — has exactly the two preimages
`r` and `c`. Hence `n = 2 · #(m-cells)` and `n` is even. `1997` is not.

## (b)

Instead of the doubling construction of the write-up, take `n = 2ᵏ` and use `xor` directly:

  `M i j = 2n-1` if `i = j`,  `i ^^^ j` if `i < j`,  `(i ^^^ j) + (n-1)` if `j < i`.

For `j ≠ i` the pair `M i j`, `M j i` is `{i ^^^ j, (i ^^^ j) + (n-1)}`, and `j ↦ i ^^^ j` is a
bijection from `{j ≠ i}` onto `{1, …, n-1}`. So the `i`-th cross carries `{1,…,n-1}`,
`{n,…,2n-2}` and `2n-1`, i.e. all of `S`.
-/

open Finset

namespace Imo1997P4

/-- The `i`-th row and column together exhaust `{1, …, 2n-1}`. -/
def Silver (n : ℕ) (M : Fin n → Fin n → ℕ) : Prop :=
  ∀ i : Fin n,
    (univ.image fun j => M i j) ∪ (univ.image fun j => M j i) = Finset.Icc 1 (2 * n - 1)

/-! ### Part (a) -/

/-- The cells of the `i`-th cross. -/
def cross (n : ℕ) (i : Fin n) : Finset (Fin n × Fin n) :=
  (univ.image fun j : Fin n => (i, j)) ∪ (univ.image fun j : Fin n => (j, i))

theorem mem_cross {n : ℕ} (i : Fin n) (p : Fin n × Fin n) :
    p ∈ cross n i ↔ (p.1 = i ∨ p.2 = i) := by
  simp only [cross, mem_union, mem_image, mem_univ, true_and, Prod.ext_iff]
  constructor
  · rintro (⟨j, hj1, -⟩ | ⟨j, -, hj2⟩)
    · exact Or.inl hj1.symm
    · exact Or.inr hj2.symm
  · rintro (h | h)
    · exact Or.inl ⟨p.2, h.symm, rfl⟩
    · exact Or.inr ⟨p.1, rfl, h.symm⟩

theorem card_cross {n : ℕ} (i : Fin n) : (cross n i).card = 2 * n - 1 := by
  classical
  have h1 : (univ.image fun j : Fin n => (i, j)).card = n := by
    rw [Finset.card_image_of_injective _ (fun a b hab => by simpa using hab), Finset.card_univ,
      Fintype.card_fin]
  have h2 : (univ.image fun j : Fin n => (j, i)).card = n := by
    rw [Finset.card_image_of_injective _ (fun a b hab => by simpa using hab), Finset.card_univ,
      Fintype.card_fin]
  have h3 : (univ.image fun j : Fin n => (i, j)) ∩ (univ.image fun j : Fin n => (j, i))
      = {(i, i)} := by
    ext p
    simp only [mem_inter, mem_image, mem_univ, true_and, mem_singleton, Prod.ext_iff]
    constructor
    · rintro ⟨⟨a, ha1, -⟩, ⟨b, -, hb2⟩⟩
      exact ⟨ha1.symm, hb2.symm⟩
    · rintro ⟨h1', h2'⟩
      exact ⟨⟨p.2, h1'.symm, rfl⟩, ⟨p.1, rfl, h2'.symm⟩⟩
  have h4 := Finset.card_union_add_card_inter
    (univ.image fun j : Fin n => (i, j)) (univ.image fun j : Fin n => (j, i))
  rw [h3, Finset.card_singleton, h1, h2] at h4
  unfold cross
  omega

theorem no_silver_of_odd (n : ℕ) (hn : 2 ≤ n) (hodd : ¬ 2 ∣ n)
    (M : Fin n → Fin n → ℕ) : ¬ Silver n M := by
  classical
  intro hS
  have himg : ∀ i : Fin n,
      (cross n i).image (fun p => M p.1 p.2) = Finset.Icc 1 (2 * n - 1) := by
    intro i
    rw [← hS i]
    ext x
    simp only [mem_image, mem_union, mem_cross, mem_univ, true_and]
    constructor
    · rintro ⟨p, hp, rfl⟩
      rcases hp with h | h
      · exact Or.inl ⟨p.2, by rw [← h]⟩
      · exact Or.inr ⟨p.1, by rw [← h]⟩
    · rintro (⟨j, rfl⟩ | ⟨j, rfl⟩)
      · exact ⟨(i, j), Or.inl rfl, rfl⟩
      · exact ⟨(j, i), Or.inr rfl, rfl⟩
  have hinj : ∀ i : Fin n, Set.InjOn (fun p : Fin n × Fin n => M p.1 p.2) (cross n i) := by
    intro i
    rw [← Finset.card_image_iff, himg i, Nat.card_Icc, card_cross i]
    omega
  obtain ⟨m, hm1, hm2⟩ : ∃ m, m ∈ Finset.Icc 1 (2 * n - 1) ∧ ∀ i : Fin n, M i i ≠ m := by
    by_contra hcon
    have hsub : Finset.Icc 1 (2 * n - 1) ⊆ univ.image fun i : Fin n => M i i := by
      intro v hv
      by_contra hnv
      exact hcon ⟨v, hv, fun i hi => hnv (mem_image.2 ⟨i, mem_univ i, hi⟩)⟩
    have hle := Finset.card_le_card hsub
    have hle2 : (univ.image fun i : Fin n => M i i).card ≤ n := by
      calc (univ.image fun i : Fin n => M i i).card ≤ (univ : Finset (Fin n)).card :=
            Finset.card_image_le
        _ = n := by simp
    rw [Nat.card_Icc] at hle
    omega
  have hF : ∀ i : Fin n, ∃ p : Fin n × Fin n,
      (cross n i).filter (fun q => M q.1 q.2 = m) = {p} := by
    intro i
    obtain ⟨p, hp, hpm⟩ : ∃ p ∈ cross n i, M p.1 p.2 = m := by
      have hmem : m ∈ (cross n i).image (fun p => M p.1 p.2) := by rw [himg i]; exact hm1
      rw [mem_image] at hmem
      obtain ⟨p, hp, hpm⟩ := hmem
      exact ⟨p, hp, hpm⟩
    refine ⟨p, ?_⟩
    ext q
    simp only [mem_filter, mem_singleton]
    constructor
    · rintro ⟨hq, hqm⟩
      exact hinj i (mem_coe.2 hq) (mem_coe.2 hp) (by simp only []; rw [hqm, hpm])
    · rintro rfl
      exact ⟨hp, hpm⟩
  choose φ hφ using hF
  have hφmem : ∀ i, φ i ∈ cross n i ∧ M (φ i).1 (φ i).2 = m := by
    intro i
    have hm : φ i ∈ (cross n i).filter (fun q => M q.1 q.2 = m) := by
      rw [hφ i]; exact mem_singleton_self _
    rw [mem_filter] at hm
    exact hm
  have hφuniq : ∀ (i : Fin n) (q : Fin n × Fin n), q ∈ cross n i → M q.1 q.2 = m → q = φ i := by
    intro i q hq hqm
    have hm : q ∈ (cross n i).filter (fun r => M r.1 r.2 = m) := mem_filter.2 ⟨hq, hqm⟩
    rw [hφ i] at hm
    exact mem_singleton.1 hm
  have hmaps : Set.MapsTo φ (univ : Finset (Fin n))
      ((univ.filter (fun p : Fin n × Fin n => M p.1 p.2 = m) : Finset (Fin n × Fin n)) :
        Set (Fin n × Fin n)) := by
    intro i _
    rw [mem_coe, mem_filter]
    exact ⟨mem_univ _, (hφmem i).2⟩
  have hcount : (univ : Finset (Fin n)).card
      = ∑ p ∈ univ.filter (fun p : Fin n × Fin n => M p.1 p.2 = m),
          (univ.filter (fun i => φ i = p)).card :=
    Finset.card_eq_sum_card_fiberwise hmaps
  have hfib : ∀ p ∈ univ.filter (fun p : Fin n × Fin n => M p.1 p.2 = m),
      (univ.filter (fun i => φ i = p)).card = 2 := by
    intro p hp
    have hpm : M p.1 p.2 = m := (mem_filter.1 hp).2
    have hne : p.1 ≠ p.2 := by
      intro h
      refine hm2 p.1 ?_
      rw [← hpm, h]
    have hset : univ.filter (fun i => φ i = p) = {p.1, p.2} := by
      ext i
      simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
      constructor
      · intro h
        have hpc : p ∈ cross n i := h ▸ (hφmem i).1
        rcases (mem_cross i p).1 hpc with h1 | h1
        · exact Or.inl h1.symm
        · exact Or.inr h1.symm
      · rintro (rfl | rfl)
        · exact (hφuniq p.1 p ((mem_cross _ _).2 (Or.inl rfl)) hpm).symm
        · exact (hφuniq p.2 p ((mem_cross _ _).2 (Or.inr rfl)) hpm).symm
    rw [hset, Finset.card_pair hne]
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul, Finset.card_univ,
    Fintype.card_fin] at hcount
  exact hodd ⟨(univ.filter (fun p : Fin n × Fin n => M p.1 p.2 = m)).card, by omega⟩

/-- **Part (a).** -/
theorem imo1997_p4_a (M : Fin 1997 → Fin 1997 → ℕ) : ¬ Silver 1997 M :=
  no_silver_of_odd 1997 (by norm_num) (by decide) M

/-! ### Part (b) -/

theorem xor_cancel (a w : ℕ) : a ^^^ (a ^^^ w) = w := by
  rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

theorem eq_of_xor_eq_zero {a b : ℕ} (h : a ^^^ b = 0) : a = b := by
  have h2 : (a ^^^ b) ^^^ b = 0 ^^^ b := by rw [h]
  rwa [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero, Nat.zero_xor] at h2

/-- The `xor` construction, silver whenever `n` is a power of two. -/
def SM (n : ℕ) (i j : Fin n) : ℕ :=
  if i.val = j.val then 2 * n - 1
  else if i.val < j.val then i.val ^^^ j.val
  else (i.val ^^^ j.val) + (n - 1)

theorem SM_diag {n : ℕ} (i : Fin n) : SM n i i = 2 * n - 1 := by simp [SM]

theorem SM_lt {n : ℕ} {i j : Fin n} (h : i.val < j.val) : SM n i j = i.val ^^^ j.val := by
  have h1 : ¬ (i.val = j.val) := by omega
  simp [SM, h1, h]

theorem SM_gt {n : ℕ} {i j : Fin n} (h : j.val < i.val) :
    SM n i j = (i.val ^^^ j.val) + (n - 1) := by
  have h1 : ¬ (i.val = j.val) := by omega
  have h2 : ¬ (i.val < j.val) := by omega
  simp [SM, h1, h2]

theorem silver_pow (k : ℕ) : Silver (2 ^ k) (SM (2 ^ k)) := by
  classical
  have hn : 0 < 2 ^ k := by positivity
  have hxlt : ∀ a b : Fin (2 ^ k), a.val ^^^ b.val < 2 ^ k := fun a b =>
    Nat.xor_lt_two_pow a.isLt b.isLt
  intro i
  ext x
  simp only [mem_union, mem_image, mem_univ, true_and, Finset.mem_Icc]
  constructor
  · have hval : ∀ a b : Fin (2 ^ k), 1 ≤ SM (2 ^ k) a b ∧ SM (2 ^ k) a b ≤ 2 * 2 ^ k - 1 := by
      intro a b
      by_cases hab : a.val = b.val
      · have : SM (2 ^ k) a b = 2 * 2 ^ k - 1 := by simp [SM, hab]
        omega
      · have h0 : a.val ^^^ b.val ≠ 0 := fun h => hab (eq_of_xor_eq_zero h)
        have h1 := hxlt a b
        rcases Nat.lt_or_ge a.val b.val with hlt | hge
        · rw [SM_lt hlt]; omega
        · have hgt : b.val < a.val := by omega
          rw [SM_gt hgt]; omega
    rintro (⟨j, rfl⟩ | ⟨j, rfl⟩)
    · exact hval i j
    · exact hval j i
  · rintro ⟨hx1, hx2⟩
    by_cases hbig : x = 2 * 2 ^ k - 1
    · exact Or.inl ⟨i, by rw [SM_diag, hbig]⟩
    obtain ⟨w, hw1, hw2, hwx⟩ :
        ∃ w, 1 ≤ w ∧ w < 2 ^ k ∧ (x = w ∨ x = w + (2 ^ k - 1)) := by
      by_cases hsmall : x ≤ 2 ^ k - 1
      · exact ⟨x, hx1, by omega, Or.inl rfl⟩
      · exact ⟨x - (2 ^ k - 1), by omega, by omega, Or.inr (by omega)⟩
    refine ?_
    have hjlt : i.val ^^^ w < 2 ^ k := Nat.xor_lt_two_pow i.isLt hw2
    set j : Fin (2 ^ k) := ⟨i.val ^^^ w, hjlt⟩ with hjdef
    have hjval : j.val = i.val ^^^ w := rfl
    have hxorj : i.val ^^^ j.val = w := by rw [hjval]; exact xor_cancel i.val w
    have hxorji : j.val ^^^ i.val = w := by rw [Nat.xor_comm]; exact hxorj
    have hij : i.val ≠ j.val := by
      intro h
      rw [← h, Nat.xor_self] at hxorj
      omega
    rcases hwx with hxw | hxw
    · rw [hxw]
      rcases Nat.lt_or_ge i.val j.val with hlt | hge
      · exact Or.inl ⟨j, by rw [SM_lt hlt, hxorj]⟩
      · have hgt : j.val < i.val := by omega
        exact Or.inr ⟨j, by rw [SM_lt hgt, hxorji]⟩
    · rw [hxw]
      rcases Nat.lt_or_ge i.val j.val with hlt | hge
      · exact Or.inr ⟨j, by rw [SM_gt hlt, hxorji]⟩
      · have hgt : j.val < i.val := by omega
        exact Or.inl ⟨j, by rw [SM_gt hgt, hxorj]⟩

/-- **Part (b).** Silver matrices exist for arbitrarily large `n`. -/
theorem imo1997_p4_b : ∀ N : ℕ, ∃ n : ℕ, N < n ∧ ∃ M : Fin n → Fin n → ℕ, Silver n M := by
  intro N
  refine ⟨2 ^ (N + 1), ?_, SM (2 ^ (N + 1)), silver_pow (N + 1)⟩
  have h1 : N < 2 ^ N := Nat.lt_two_pow_self
  have h2 : 2 ^ N ≤ 2 ^ (N + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

end Imo1997P4
