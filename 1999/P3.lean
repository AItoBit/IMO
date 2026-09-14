import Mathlib

/-!
# IMO 1999 Problem 3

Let `n` be an even positive integer.  We say that two different cells of an `n × n` board are
*neighbouring* if they have a common side.  Find the minimal number of cells that must be marked
so that every cell of the board (marked or not) has a marked neighbouring cell.

The answer is `n * (n + 2) / 4`.
-/

namespace Imo1999P3

open Finset

/-- The cells of the `n × n` board, as pairs `(row, column)` with entries `< n`. -/
def board (n : ℕ) : Finset (ℕ × ℕ) := Finset.range n ×ˢ Finset.range n

/-- Two cells are neighbouring when they have a common side. -/
def Adj (c d : ℕ × ℕ) : Prop :=
  (c.1 = d.1 ∧ (c.2 + 1 = d.2 ∨ d.2 + 1 = c.2)) ∨ (c.2 = d.2 ∧ (c.1 + 1 = d.1 ∨ d.1 + 1 = c.1))

instance (c d : ℕ × ℕ) : Decidable (Adj c d) := by unfold Adj; infer_instance

/-- A set of marked cells is *good* when every cell of the board has a marked neighbour. -/
def Good (n : ℕ) (S : Finset (ℕ × ℕ)) : Prop := ∀ c ∈ board n, ∃ s ∈ S, Adj c s

lemma mem_board {n : ℕ} {c : ℕ × ℕ} : c ∈ board n ↔ c.1 < n ∧ c.2 < n := by
  simp [board, Finset.mem_product]

/-- The marked black cells: on the diagonals `i + j ≡ 0 [MOD 4]`, every other cell counted
from the border. -/
def Pset (n : ℕ) : Finset (ℕ × ℕ) :=
  (board n).filter fun c =>
    (c.1 + c.2) % 4 = 0 ∧ ((c.1 + c.2 < n ∧ c.1 % 2 = 0) ∨ (n ≤ c.1 + c.2 ∧ c.1 % 2 = 1))

lemma mem_Pset {n : ℕ} {c : ℕ × ℕ} :
    c ∈ Pset n ↔ c.1 < n ∧ c.2 < n ∧ (c.1 + c.2) % 4 = 0 ∧
      ((c.1 + c.2 < n ∧ c.1 % 2 = 0) ∨ (n ≤ c.1 + c.2 ∧ c.1 % 2 = 1)) := by
  simp [Pset, mem_board, and_assoc]

/-- Reflection of the board in a vertical axis; it exchanges the two colours. -/
def refl (n : ℕ) (c : ℕ × ℕ) : ℕ × ℕ := (c.1, n - 1 - c.2)

/-- The marked cells. -/
def Qset (n : ℕ) : Finset (ℕ × ℕ) := Pset n ∪ (Pset n).image (refl n)

/-! ### The set `Pset` dominates the white cells exactly once -/

lemma exists_nbr_P {n i j : ℕ} (hn : n % 2 = 0) (hi : i < n) (hj : j < n)
    (hodd : (i + j) % 2 = 1) : ∃ d ∈ Pset n, Adj (i, j) d := by
  by_cases h1 : (i + j + 1) % 4 = 0
  · by_cases hpar : (i % 2 = 0) ↔ (i + j + 1 < n)
    · refine ⟨(i, j + 1), ?_, ?_⟩
      · rw [mem_Pset]; dsimp only; omega
      · simp [Adj]
    · refine ⟨(i + 1, j), ?_, ?_⟩
      · rw [mem_Pset]; dsimp only; omega
      · simp [Adj]
  · by_cases hpar : (i % 2 = 0) ↔ (i + j - 1 < n)
    · refine ⟨(i, j - 1), ?_, ?_⟩
      · rw [mem_Pset]; dsimp only; omega
      · exact Or.inl ⟨rfl, Or.inr (by dsimp only; omega)⟩
    · refine ⟨(i - 1, j), ?_, ?_⟩
      · rw [mem_Pset]; dsimp only; omega
      · exact Or.inr ⟨rfl, Or.inr (by dsimp only; omega)⟩

lemma nbr_P_unique {n i j : ℕ} {d e : ℕ × ℕ} (hd : d ∈ Pset n) (he : e ∈ Pset n)
    (had : Adj (i, j) d) (hae : Adj (i, j) e) : d = e := by
  obtain ⟨d1, d2⟩ := d
  obtain ⟨e1, e2⟩ := e
  rw [mem_Pset] at hd he
  simp only [Adj] at had hae
  dsimp only at hd he had hae
  rw [Prod.mk.injEq]
  omega

/-! ### Reflection -/

lemma refl_mem_board {n : ℕ} {c : ℕ × ℕ} (h : c ∈ board n) : refl n c ∈ board n := by
  rw [mem_board] at h ⊢
  exact ⟨h.1, by show n - 1 - c.2 < n; omega⟩

lemma refl_involutive {n : ℕ} {c : ℕ × ℕ} (h : c.2 < n) : refl n (refl n c) = c := by
  obtain ⟨a, b⟩ := c
  have hb : n - 1 - (n - 1 - b) = b := by dsimp only at h; omega
  simp [refl, hb]

lemma adj_parity {c d : ℕ × ℕ} (h : Adj c d) : (c.1 + c.2) % 2 ≠ (d.1 + d.2) % 2 := by
  obtain ⟨a, b⟩ := c
  obtain ⟨x, y⟩ := d
  simp only [Adj] at h
  dsimp only at h ⊢
  omega

lemma adj_refl {n : ℕ} {c d : ℕ × ℕ} (hc : c.2 < n) (hd : d.2 < n) :
    Adj c d ↔ Adj (refl n c) (refl n d) := by
  obtain ⟨a, b⟩ := c
  obtain ⟨x, y⟩ := d
  simp only [Adj, refl]
  dsimp only at hc hd ⊢
  omega

lemma Pset_subset_board {n : ℕ} : Pset n ⊆ board n := Finset.filter_subset _ _

lemma mem_image_refl {n : ℕ} {d : ℕ × ℕ} (hd : d.2 < n) :
    d ∈ (Pset n).image (refl n) ↔ refl n d ∈ Pset n := by
  constructor
  · intro h
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 h
    have : e.2 < n := (mem_board.1 (Pset_subset_board he)).2
    rwa [refl_involutive this]
  · intro h
    exact Finset.mem_image.2 ⟨refl n d, h, refl_involutive hd⟩

lemma Qset_subset_board {n : ℕ} : Qset n ⊆ board n := by
  intro c hc
  rcases Finset.mem_union.1 hc with h | h
  · exact Pset_subset_board h
  · obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 h
    exact refl_mem_board (Pset_subset_board he)

lemma mem_Qset_refl {n : ℕ} {d : ℕ × ℕ} (hd : d.2 < n) : d ∈ Qset n ↔ refl n d ∈ Qset n := by
  have h1 : refl n d ∈ (Pset n).image (refl n) ↔ d ∈ Pset n := by
    rw [mem_image_refl (show n - 1 - d.2 < n by omega), refl_involutive hd]
  have h2 : d ∈ (Pset n).image (refl n) ↔ refl n d ∈ Pset n := mem_image_refl hd
  simp only [Qset, Finset.mem_union, h1, h2]
  tauto

/-! ### Every cell has exactly one neighbour in `Qset` -/

lemma key_white {n i j : ℕ} (hn : n % 2 = 0) (hi : i < n) (hj : j < n) (hodd : (i + j) % 2 = 1) :
    ∃! d, d ∈ Qset n ∧ Adj (i, j) d := by
  obtain ⟨d, hdP, hadj⟩ := exists_nbr_P hn hi hj hodd
  refine ⟨d, ⟨Finset.mem_union_left _ hdP, hadj⟩, ?_⟩
  rintro e ⟨heQ, hae⟩
  rcases Finset.mem_union.1 heQ with heP | heI
  · exact nbr_P_unique heP hdP hae hadj
  · exfalso
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 heI
    rw [mem_Pset] at hf
    have hpar := adj_parity hae
    simp only [refl] at hpar
    omega

lemma key_black {n i j : ℕ} (hn : n % 2 = 0) (hi : i < n) (hj : j < n) (heven : (i + j) % 2 = 0) :
    ∃! d, d ∈ Qset n ∧ Adj (i, j) d := by
  have hj' : n - 1 - j < n := by omega
  have hodd : (i + (n - 1 - j)) % 2 = 1 := by omega
  obtain ⟨e, ⟨heQ, hae⟩, huniq⟩ := key_white hn hi hj' hodd
  have he2 : e.2 < n := (mem_board.1 (Qset_subset_board heQ)).2
  have hrc : refl n (i, n - 1 - j) = (i, j) := by
    have : n - 1 - (n - 1 - j) = j := by omega
    simp [refl, this]
  refine ⟨refl n e, ⟨(mem_Qset_refl he2).1 heQ, ?_⟩, ?_⟩
  · have := (adj_refl (n := n) (c := (i, n - 1 - j)) (d := e) (by dsimp only; omega) he2).1 hae
    rwa [hrc] at this
  · rintro d ⟨hdQ, had⟩
    have hd2 : d.2 < n := (mem_board.1 (Qset_subset_board hdQ)).2
    have : Adj (i, n - 1 - j) (refl n d) := by
      have := (adj_refl (n := n) (c := (i, j)) (d := d) (by dsimp only; omega) hd2).1 had
      simpa [refl] using this
    have hed : refl n d = e := huniq _ ⟨(mem_Qset_refl hd2).1 hdQ, this⟩
    rw [← hed, refl_involutive hd2]

lemma key {n : ℕ} (hn : n % 2 = 0) {c : ℕ × ℕ} (hc : c ∈ board n) :
    ∃! d, d ∈ Qset n ∧ Adj c d := by
  obtain ⟨i, j⟩ := c
  obtain ⟨hi, hj⟩ := mem_board.1 hc
  rcases Nat.even_or_odd (i + j) with h | h
  · exact key_black hn hi hj (Nat.even_iff.1 h)
  · exact key_white hn hi hj (Nat.odd_iff.1 h)

/-! ### The cardinality of `Qset` -/

lemma mem_Pset' {n a b : ℕ} :
    (a, b) ∈ Pset n ↔ a < n ∧ b < n ∧ (a + b) % 4 = 0 ∧
      ((a + b < n ∧ a % 2 = 0) ∨ (n ≤ a + b ∧ a % 2 = 1)) := mem_Pset

lemma sum_odd (a : ℕ) : ∑ t ∈ Finset.range a, (2 * t + 1) = a * a := by
  induction a with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; ring

lemma sum_desc (b : ℕ) : ∑ i ∈ Finset.range b, 2 * (b - i) = b * (b + 1) := by
  induction b with
  | zero => simp
  | succ k ih =>
    have hstep : ∀ i ∈ Finset.range k, 2 * (k + 1 - i) = 2 * (k - i) + 2 := by
      intro i hi
      have := Finset.mem_range.1 hi
      omega
    have hk : k + 1 - k = 1 := by omega
    rw [Finset.sum_range_succ, hk, Finset.sum_congr rfl hstep, Finset.sum_add_distrib, ih,
      Finset.sum_const, Finset.card_range]
    simp only [smul_eq_mul]
    ring

lemma fiber_card {m t : ℕ} (ht : t < m) :
    ((Pset (2 * m)).filter fun c => (c.1 + c.2) / 4 = t).card =
      if 2 * t < m then 2 * t + 1 else 2 * m - 2 * t := by
  split_ifs with h
  · have hEq : ((Pset (2 * m)).filter fun c => (c.1 + c.2) / 4 = t)
        = (Finset.range (2 * t + 1)).image (fun k => (2 * k, 4 * t - 2 * k)) := by
      ext c
      obtain ⟨a, b⟩ := c
      simp only [Finset.mem_filter, mem_Pset', Finset.mem_image, Finset.mem_range,
        Prod.mk.injEq]
      constructor
      · rintro ⟨⟨h1, h2, h3, h4⟩, h5⟩
        exact ⟨a / 2, by omega, by omega, by omega⟩
      · rintro ⟨k, hk, rfl, rfl⟩
        refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;> omega
    rw [hEq, Finset.card_image_of_injOn, Finset.card_range]
    intro x _ y _ hxy
    simp only [Prod.mk.injEq] at hxy
    omega
  · have hEq : ((Pset (2 * m)).filter fun c => (c.1 + c.2) / 4 = t)
        = (Finset.Ico (2 * t - m) m).image (fun k => (2 * k + 1, 4 * t - (2 * k + 1))) := by
      ext c
      obtain ⟨a, b⟩ := c
      simp only [Finset.mem_filter, mem_Pset', Finset.mem_image, Finset.mem_Ico,
        Prod.mk.injEq]
      constructor
      · rintro ⟨⟨h1, h2, h3, h4⟩, h5⟩
        exact ⟨a / 2, ⟨by omega, by omega⟩, by omega, by omega⟩
      · rintro ⟨k, hk, rfl, rfl⟩
        refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;> omega
    rw [hEq, Finset.card_image_of_injOn, Nat.card_Ico]
    · omega
    · intro x _ y _ hxy
      simp only [Prod.mk.injEq] at hxy
      omega

lemma card_Pset {m : ℕ} (hm : 0 < m) : 2 * (Pset (2 * m)).card = m * (m + 1) := by
  obtain ⟨a, ha⟩ : ∃ a, a = (m + 1) / 2 := ⟨_, rfl⟩
  have ham : a ≤ m := by omega
  have hfib : (Pset (2 * m)).card
      = ∑ t ∈ Finset.range m, ((Pset (2 * m)).filter fun c => (c.1 + c.2) / 4 = t).card := by
    refine Finset.card_eq_sum_card_fiberwise ?_
    intro c hc
    simp only [Finset.mem_coe, Finset.mem_range] at hc ⊢
    rw [mem_Pset] at hc
    omega
  have hsum : ∑ t ∈ Finset.range m, ((Pset (2 * m)).filter fun c => (c.1 + c.2) / 4 = t).card
      = ∑ t ∈ Finset.range m, (if 2 * t < m then 2 * t + 1 else 2 * m - 2 * t) :=
    Finset.sum_congr rfl fun t htm => fiber_card (Finset.mem_range.1 htm)
  have hsplit : ∑ t ∈ Finset.range m, (if 2 * t < m then 2 * t + 1 else 2 * m - 2 * t)
      = (∑ t ∈ Finset.range a, (if 2 * t < m then 2 * t + 1 else 2 * m - 2 * t))
        + ∑ t ∈ Finset.Ico a m, (if 2 * t < m then 2 * t + 1 else 2 * m - 2 * t) := by
    simp only [Finset.range_eq_Ico]
    exact (Finset.sum_Ico_consecutive _ (Nat.zero_le a) ham).symm
  have h1 : (∑ t ∈ Finset.range a, (if 2 * t < m then 2 * t + 1 else 2 * m - 2 * t))
      = a * a := by
    rw [← sum_odd a]
    exact Finset.sum_congr rfl fun t htm => if_pos (by
      have := Finset.mem_range.1 htm; omega)
  have h2 : (∑ t ∈ Finset.Ico a m, (if 2 * t < m then 2 * t + 1 else 2 * m - 2 * t))
      = (m - a) * (m - a + 1) := by
    have e1 : ∀ i ∈ Finset.range (m - a),
        (if 2 * (a + i) < m then 2 * (a + i) + 1 else 2 * m - 2 * (a + i)) = 2 * (m - a - i) := by
      intro i hi
      have := Finset.mem_range.1 hi
      rw [if_neg (by omega)]
      omega
    rw [Finset.sum_Ico_eq_sum_range, ← sum_desc (m - a)]
    exact Finset.sum_congr rfl e1
  rw [hfib, hsum, hsplit, h1, h2]
  rcases Nat.even_or_odd m with ⟨p, hp⟩ | ⟨p, hp⟩
  · have hap : a = p := by omega
    have hbp : m - a = p := by omega
    rw [hbp, hap, hp]
    ring
  · have hap : a = p + 1 := by omega
    have hbp : m - a = p := by omega
    rw [hbp, hap, hp]
    ring

lemma card_Qset {m : ℕ} (hm : 0 < m) : (Qset (2 * m)).card = m * (m + 1) := by
  have hinj : Set.InjOn (refl (2 * m)) (Pset (2 * m)) := by
    intro x hx y hy hxy
    have hx2 : x.2 < 2 * m := (mem_board.1 (Pset_subset_board hx)).2
    have hy2 : y.2 < 2 * m := (mem_board.1 (Pset_subset_board hy)).2
    rw [← refl_involutive hx2, ← refl_involutive hy2, hxy]
  have hdisj : Disjoint (Pset (2 * m)) ((Pset (2 * m)).image (refl (2 * m))) := by
    rw [Finset.disjoint_right]
    intro c hc hcP
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hc
    rw [mem_Pset] at hf
    rw [mem_Pset] at hcP
    simp only [refl] at hcP
    omega
  have hcard : (Qset (2 * m)).card = (Pset (2 * m)).card + (Pset (2 * m)).card := by
    rw [Qset, Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injOn hinj]
  have := card_Pset hm
  omega

/-! ### The answer -/

lemma adj_symm {c d : ℕ × ℕ} (h : Adj c d) : Adj d c := by
  obtain ⟨a, b⟩ := c
  obtain ⟨x, y⟩ := d
  simp only [Adj] at h ⊢
  omega

/-- **IMO 1999, Problem 3.**  For an even positive integer `n`, the least number of cells of an
`n × n` board that can be marked so that every cell of the board has a marked neighbour is
`n * (n + 2) / 4`. -/
theorem imo1999_p3 {n : ℕ} (hpos : 0 < n) (hn : Even n) :
    IsLeast {k | ∃ S : Finset (ℕ × ℕ), S ⊆ board n ∧ S.card = k ∧ Good n S} (n * (n + 2) / 4) := by
  classical
  have hn2 : n % 2 = 0 := Nat.even_iff.1 hn
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := ⟨n / 2, by omega⟩
  have hm : 0 < m := by omega
  have hval : 2 * m * (2 * m + 2) / 4 = m * (m + 1) := by
    rw [show 2 * m * (2 * m + 2) = 4 * (m * (m + 1)) by ring, Nat.mul_div_cancel_left _ (by norm_num)]
  rw [hval]
  constructor
  · refine ⟨Qset (2 * m), Qset_subset_board, card_Qset hm, ?_⟩
    intro c hc
    obtain ⟨d, ⟨hdQ, hadj⟩, -⟩ := key hn2 hc
    exact ⟨d, hdQ, hadj⟩
  · rintro k ⟨S, hSb, rfl, hS⟩
    rw [← card_Qset hm]
    have hex : ∀ q ∈ Qset (2 * m), ∃ s ∈ S, Adj q s := fun q hq => hS q (Qset_subset_board hq)
    choose! f hfS hfAdj using hex
    refine Finset.card_le_card_of_injOn f hfS ?_
    intro q1 h1 q2 h2 heq
    rw [Finset.mem_coe] at h1 h2
    have hs : f q1 ∈ board (2 * m) := hSb (hfS q1 h1)
    obtain ⟨d, -, hd⟩ := key hn2 hs
    have e1 : q1 = d := hd q1 ⟨h1, adj_symm (hfAdj q1 h1)⟩
    have e2 : q2 = d := hd q2 ⟨h2, by rw [heq]; exact adj_symm (hfAdj q2 h2)⟩
    rw [e1, e2]

end Imo1999P3
