import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 1000000

/-!
# IMO 1979 Problem 6

Let `A` and `E` be opposite vertices of an octagon.  A frog starts at vertex `A`.  From any
vertex except `E` it jumps to one of the two adjacent vertices.  When it reaches `E` it stops.
Let `aₙ` be the number of distinct paths of exactly `n` jumps ending at `E`.  Then

```
a_{2n-1} = 0,     a_{2n} = ((2 + √2)^(n-1) - (2 - √2)^(n-1)) / √2 .
```

We label the vertices of the octagon by `ZMod 8`, with `A = 0` and `E = 4`.  A path is encoded by
the list of its jumps: `true` means "jump to the next vertex", `false` means "jump to the previous
vertex".  A path is legal when it ends at `E` and never visits `E` earlier (the frog stops at `E`).
-/

namespace IMO1979P6

/-- One jump from vertex `X`: `true` moves to `X + 1`, `false` moves to `X - 1`. -/
def step (X : ZMod 8) (b : Bool) : ZMod 8 := if b then X + 1 else X - 1

/-- The vertex reached from `X` after performing the jumps in the list `s`. -/
def endsAt (X : ZMod 8) : List Bool → ZMod 8
  | [] => X
  | b :: t => endsAt (step X b) t

/-- `s` is a legal frog path starting at `X`: it ends at `E = 4` and it never visits `E`
before its last step (in particular the frog never jumps away from `E`). -/
def ValidPath (X : ZMod 8) (s : List Bool) : Prop :=
  endsAt X s = 4 ∧ ∀ k < s.length, endsAt X (s.take k) ≠ 4

instance (X : ZMod 8) : DecidablePred (ValidPath X) := fun s => by
  unfold ValidPath; infer_instance

/-- The finset of all lists of booleans of length `n`. -/
def boolLists : ℕ → Finset (List Bool)
  | 0 => {[]}
  | n + 1 => (boolLists n).image (List.cons true) ∪ (boolLists n).image (List.cons false)

/-- The number of legal frog paths of exactly `n` jumps starting at the vertex `X`. -/
def N (X : ZMod 8) (n : ℕ) : ℕ := ((boolLists n).filter (ValidPath X)).card

/-- `aₙ`: the number of distinct paths of exactly `n` jumps from `A = 0` ending at `E = 4`. -/
def a (n : ℕ) : ℕ := N 0 n

/-! ### Basic facts about `boolLists` -/

lemma mem_boolLists {s : List Bool} {n : ℕ} : s ∈ boolLists n ↔ s.length = n := by
  induction n generalizing s with
  | zero => simp [boolLists, List.length_eq_zero_iff]
  | succ n ih =>
    simp only [boolLists, Finset.mem_union, Finset.mem_image, ih]
    constructor
    · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩) <;> simp [ht]
    · intro h
      match s with
      | b :: t =>
        simp only [List.length_cons, Nat.add_right_cancel_iff] at h
        cases b
        · exact Or.inr ⟨t, h, rfl⟩
        · exact Or.inl ⟨t, h, rfl⟩

/-! ### The recursion for `N` -/

lemma endsAt_cons (X : ZMod 8) (b : Bool) (t : List Bool) :
    endsAt X (b :: t) = endsAt (step X b) t := rfl

lemma validPath_cons {X : ZMod 8} (hX : X ≠ 4) (b : Bool) (t : List Bool) :
    ValidPath X (b :: t) ↔ ValidPath (step X b) t := by
  unfold ValidPath
  simp only [endsAt_cons, List.length_cons]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun k hk => ?_⟩
    have := h2 (k + 1) (by omega)
    simpa [List.take_succ_cons, endsAt_cons] using this
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun k hk => ?_⟩
    match k with
    | 0 => simpa [endsAt] using hX
    | k + 1 =>
      have hk' : k < t.length := by omega
      simpa [List.take_succ_cons, endsAt_cons] using h2 k hk'

lemma N_zero (X : ZMod 8) : N X 0 = if X = 4 then 1 else 0 := by
  unfold N boolLists
  by_cases h : X = 4 <;> simp [Finset.filter_singleton, ValidPath, endsAt, h]

lemma N_four_succ (n : ℕ) : N 4 (n + 1) = 0 := by
  unfold N
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro s hs
  rw [mem_boolLists] at hs
  rintro ⟨-, h2⟩
  exact h2 0 (by omega) (by simp [endsAt])

lemma N_succ_of_ne {X : ZMod 8} (hX : X ≠ 4) (n : ℕ) :
    N X (n + 1) = N (X + 1) n + N (X - 1) n := by
  have key : ∀ b : Bool,
      ((boolLists n).image (List.cons b)).filter (ValidPath X) =
        ((boolLists n).filter (ValidPath (step X b))).image (List.cons b) := by
    intro b
    rw [Finset.filter_image]
    congr 1
    exact Finset.filter_congr fun t _ => by simpa using validPath_cons hX b t
  unfold N
  rw [show boolLists (n + 1) =
      (boolLists n).image (List.cons true) ∪ (boolLists n).image (List.cons false) from rfl,
    Finset.filter_union, Finset.card_union_of_disjoint, key, key,
    Finset.card_image_of_injective _ List.cons_injective,
    Finset.card_image_of_injective _ List.cons_injective]
  · rfl
  · rw [Finset.disjoint_left]
    intro s hs hs'
    rw [key, Finset.mem_image] at hs hs'
    obtain ⟨t, -, rfl⟩ := hs
    obtain ⟨u, -, hu⟩ := hs'
    simp at hu

/-! ### Paths with an odd number of jumps -/

/-- The parity of a vertex. -/
private def par : ZMod 8 →+* ZMod 2 := ZMod.castHom (by norm_num) (ZMod 2)

lemma par_step (X : ZMod 8) (b : Bool) : par (step X b) = par X + 1 := by
  have h : (-1 : ZMod 2) = 1 := by decide
  cases b <;> simp [step, sub_eq_add_neg, h]

lemma par_endsAt (s : List Bool) (X : ZMod 8) :
    par (endsAt X s) = par X + (s.length : ZMod 2) := by
  induction s generalizing X with
  | nil => simp [endsAt]
  | cons b t ih =>
    rw [endsAt_cons, ih, par_step, List.length_cons]
    push_cast
    ring

lemma even_length_of_validPath {s : List Bool} (h : ValidPath 0 s) : Even s.length := by
  have h1 := par_endsAt s 0
  rw [h.1] at h1
  have h4 : par (4 : ZMod 8) = 0 := by decide
  have h0 : par (0 : ZMod 8) = 0 := by decide
  rw [h4, h0, zero_add] at h1
  exact ZMod.natCast_eq_zero_iff_even.mp h1.symm

lemma a_odd (n : ℕ) : a (2 * n + 1) = 0 := by
  unfold a N
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro s hs hval
  rw [mem_boolLists] at hs
  have hev := even_length_of_validPath hval
  rw [hs, Nat.even_iff] at hev
  omega

/-! ### The recursion at the individual vertices -/

lemma N_v0 (n : ℕ) : N 0 (n + 1) = N 1 n + N 7 n := by
  have h := N_succ_of_ne (X := 0) (by decide) n; norm_num at h; exact h

lemma N_v1 (n : ℕ) : N 1 (n + 1) = N 2 n + N 0 n := by
  have h := N_succ_of_ne (X := 1) (by decide) n; norm_num at h; exact h

lemma N_v2 (n : ℕ) : N 2 (n + 1) = N 3 n + N 1 n := by
  have h := N_succ_of_ne (X := 2) (by decide) n; norm_num at h; exact h

lemma N_v3 (n : ℕ) : N 3 (n + 1) = N 4 n + N 2 n := by
  have h := N_succ_of_ne (X := 3) (by decide) n; norm_num at h; exact h

lemma N_v5 (n : ℕ) : N 5 (n + 1) = N 6 n + N 4 n := by
  have h := N_succ_of_ne (X := 5) (by decide) n; norm_num at h; exact h

lemma N_v6 (n : ℕ) : N 6 (n + 1) = N 7 n + N 5 n := by
  have h := N_succ_of_ne (X := 6) (by decide) n; norm_num at h; exact h

lemma N_v7 (n : ℕ) : N 7 (n + 1) = N 0 n + N 6 n := by
  have h := N_succ_of_ne (X := 7) (by decide) n; norm_num at h; exact h

lemma N_two_step_0 (n : ℕ) : N 0 (n + 1 + 2) = 2 * N 0 (n + 1) + N 2 (n + 1) + N 6 (n + 1) := by
  rw [N_v0, N_v1, N_v7]; ring

lemma N_two_step_2 (n : ℕ) : N 2 (n + 1 + 2) = 2 * N 2 (n + 1) + N 0 (n + 1) := by
  rw [N_v2, N_v3, N_v1, N_four_succ]; ring

lemma N_two_step_6 (n : ℕ) : N 6 (n + 1 + 2) = 2 * N 6 (n + 1) + N 0 (n + 1) := by
  rw [N_v6, N_v7, N_v5, N_four_succ]; ring

/-! ### The auxiliary sequences -/

/-- `(pq n).1 = a_{2(n+1)}` and `(pq n).2 = N 2 (2(n+1)) = N 6 (2(n+1))`. -/
def pq : ℕ → ℕ × ℕ
  | 0 => (0, 1)
  | n + 1 => (2 * (pq n).1 + 2 * (pq n).2, (pq n).1 + 2 * (pq n).2)

lemma N_even_rec (n : ℕ) :
    N 0 (2 * (n + 1)) = (pq n).1 ∧ N 2 (2 * (n + 1)) = (pq n).2 ∧
      N 6 (2 * (n + 1)) = (pq n).2 := by
  induction n with
  | zero => exact by decide
  | succ n ih =>
    obtain ⟨h0, h2, h6⟩ := ih
    have e1 : 2 * (n + 1) = 2 * n + 1 + 1 := by ring
    have e2 : 2 * (n + 1 + 1) = 2 * n + 1 + 1 + 2 := by ring
    rw [e1] at h0 h2 h6
    rw [e2, N_two_step_0, N_two_step_2, N_two_step_6, h0, h2, h6]
    refine ⟨?_, ?_, ?_⟩ <;> simp [pq] <;> ring

lemma pq_closed_form (n : ℕ) :
    ((pq n).1 : ℝ) = ((2 + Real.sqrt 2) ^ n - (2 - Real.sqrt 2) ^ n) / Real.sqrt 2 ∧
    ((pq n).2 : ℝ) = ((2 + Real.sqrt 2) ^ n + (2 - Real.sqrt 2) ^ n) / 2 := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hpos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hne : Real.sqrt 2 ≠ 0 := ne_of_gt hpos
  induction n with
  | zero => norm_num [pq]
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hp : ((pq (n + 1)).1 : ℝ) = 2 * ((pq n).1 : ℝ) + 2 * ((pq n).2 : ℝ) := by
      push_cast [pq]; ring
    have hq : ((pq (n + 1)).2 : ℝ) = ((pq n).1 : ℝ) + 2 * ((pq n).2 : ℝ) := by
      push_cast [pq]; ring
    constructor
    · rw [hp, ih1, ih2, pow_succ, pow_succ]
      field_simp
      ring
    · rw [hq, ih1, ih2, pow_succ, pow_succ]
      field_simp
      linear_combination ((2 - Real.sqrt 2) ^ n - (2 + Real.sqrt 2) ^ n) * hs

/-! ### The main results -/

/-- `a_{2n-1} = 0`: there is no path with an odd number of jumps. -/
theorem imo1979_p6_odd (n : ℕ) : a (2 * n + 1) = 0 := a_odd n

/-- `a_{2n} = ((2 + √2)^(n-1) - (2 - √2)^(n-1)) / √2`, written here with `n` replaced by
`n + 1` in order to avoid truncated subtraction. -/
theorem imo1979_p6_even (n : ℕ) :
    (a (2 * (n + 1)) : ℝ) =
      ((2 + Real.sqrt 2) ^ n - (2 - Real.sqrt 2) ^ n) / Real.sqrt 2 := by
  rw [a, (N_even_rec n).1]
  exact (pq_closed_form n).1

/-- `a_{2n} = ((2 + √2)^(n-1) - (2 - √2)^(n-1)) / √2` for `n ≥ 1`. -/
theorem imo1979_p6_even' (n : ℕ) (hn : 1 ≤ n) :
    (a (2 * n) : ℝ) =
      ((2 + Real.sqrt 2) ^ (n - 1) - (2 - Real.sqrt 2) ^ (n - 1)) / Real.sqrt 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simpa using imo1979_p6_even m

end IMO1979P6
