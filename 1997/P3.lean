import Mathlib

/-!
# IMO 1997, Problem 3

Real numbers `x₁, …, xₙ` satisfy `|x₁ + ⋯ + xₙ| = 1` and `|xᵢ| ≤ (n+1)/2`. Show there is a
permutation `y₁, …, yₙ` of them with `|y₁ + 2y₂ + ⋯ + n yₙ| ≤ (n+1)/2`.

## Formalization

The tuple is a `List ℝ` and a permutation is `List.Perm`. The weighted sum is

  `f (a :: t) = a + f t + t.sum`,

which is `∑ (i+1) * lᵢ` written so that it recurses on the list.

## Proof

Write `c = (n+1)/2`.

* `f l + f l.reverse = (n+1) * l.sum` (`f_add_reverse`), so the two endpoint values sum to `±2c`.
* `AdjSwap c l l'` exchanges two adjacent entries, both of absolute value at most `c`. Such a
  swap changes `f` by `b - a`, so by at most `2c` (`adjSwap_f`), and permutes the list.
* `reach_reverse`: a list of entries bounded by `c` reaches its own reverse by adjacent swaps —
  recursively reverse the tail, then carry the head to the back one swap at a time.
* `ivt'`: along a chain of such swaps, if `f` starts above `c` and never lands in `[-c, c]`, it
  stays above `c`; a step down of at most `2c` from above `c` cannot get below `-c` without
  passing through.

If no permutation worked, then `f x` and `f x.reverse` would both lie outside `[-c, c]`, and
since they sum to `±2c` one is `> c` and the other `< -c` — contradicting `ivt'` (applied to `f`
or to `-f`, depending on which end is which).

There is no `sorry`.
-/

namespace Imo1997P3

/-- `f [x₁, …, xₙ] = x₁ + 2x₂ + ⋯ + n xₙ`. -/
noncomputable def f : List ℝ → ℝ
  | [] => 0
  | a :: t => a + f t + t.sum

theorem f_append (p r : List ℝ) : f (p ++ r) = f p + f r + (p.length : ℝ) * r.sum := by
  induction p with
  | nil => simp [f]
  | cons a p ih =>
    simp only [List.cons_append, f, ih, List.length_cons, List.sum_append]
    push_cast
    ring

theorem f_add_reverse (l : List ℝ) : f l + f l.reverse = ((l.length : ℝ) + 1) * l.sum := by
  induction l with
  | nil => simp [f]
  | cons a t ih =>
    have h1 : f [a] = a := by simp [f]
    rw [List.reverse_cons, f_append, h1]
    simp only [f, List.length_reverse, List.length_cons, List.sum_cons, List.sum_nil,
      add_zero]
    push_cast
    linear_combination ih

/-- `l'` is `l` with two adjacent entries, both bounded by `B`, exchanged. -/
def AdjSwap (B : ℝ) (l l' : List ℝ) : Prop :=
  ∃ (pre post : List ℝ) (a b : ℝ), |a| ≤ B ∧ |b| ≤ B ∧
    l = pre ++ a :: b :: post ∧ l' = pre ++ b :: a :: post

theorem adjSwap_f {B : ℝ} {l l' : List ℝ} (h : AdjSwap B l l') : |f l - f l'| ≤ 2 * B := by
  obtain ⟨pre, post, a, b, ha, hb, hl, hl'⟩ := h
  have key : f l - f l' = b - a := by
    rw [hl, hl', f_append, f_append]
    simp only [f, List.sum_cons]
    ring
  rw [key, abs_le]
  have ha' := abs_le.1 ha
  have hb' := abs_le.1 hb
  constructor <;> linarith [ha'.1, ha'.2, hb'.1, hb'.2]

theorem adjSwap_perm {B : ℝ} {l l' : List ℝ} (h : AdjSwap B l l') : List.Perm l' l := by
  obtain ⟨pre, post, a, b, -, -, hl, hl'⟩ := h
  rw [hl, hl']
  exact List.Perm.append_left pre (List.Perm.swap a b post)

theorem adjSwap_cons {B : ℝ} {l l' : List ℝ} (a : ℝ) (h : AdjSwap B l l') :
    AdjSwap B (a :: l) (a :: l') := by
  obtain ⟨pre, post, u, v, hu, hv, hl, hl'⟩ := h
  exact ⟨a :: pre, post, u, v, hu, hv, by rw [hl]; simp, by rw [hl']; simp⟩

theorem reach_cons {B : ℝ} {l l' : List ℝ} (a : ℝ)
    (h : Relation.ReflTransGen (AdjSwap B) l l') :
    Relation.ReflTransGen (AdjSwap B) (a :: l) (a :: l') := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail (adjSwap_cons a hstep)

theorem reach_move {B : ℝ} (a : ℝ) (ha : |a| ≤ B) :
    ∀ r : List ℝ, (∀ z ∈ r, |z| ≤ B) →
      Relation.ReflTransGen (AdjSwap B) (a :: r) (r ++ [a]) := by
  intro r
  induction r with
  | nil =>
    intro _
    rw [List.nil_append]
  | cons b r ih =>
    intro hbd
    have hb1 : |b| ≤ B := hbd b (by simp)
    have hr : ∀ z ∈ r, |z| ≤ B := fun z hz => hbd z (by simp [hz])
    have step : AdjSwap B (a :: b :: r) (b :: a :: r) :=
      ⟨[], r, a, b, ha, hb1, by simp, by simp⟩
    refine Relation.ReflTransGen.head step ?_
    have h2 := reach_cons b (ih hr)
    simpa using h2

theorem reach_reverse {B : ℝ} : ∀ l : List ℝ, (∀ z ∈ l, |z| ≤ B) →
    Relation.ReflTransGen (AdjSwap B) l l.reverse := by
  intro l
  induction l with
  | nil =>
    intro _
    rw [List.reverse_nil]
  | cons a t ih =>
    intro hbd
    have ha : |a| ≤ B := hbd a (by simp)
    have ht : ∀ z ∈ t, |z| ≤ B := fun z hz => hbd z (by simp [hz])
    have htr : ∀ z ∈ t.reverse, |z| ≤ B := fun z hz => ht z (by simpa using hz)
    have s1 := reach_cons a (ih ht)
    have s2 := reach_move a ha t.reverse htr
    rw [List.reverse_cons]
    exact s1.trans s2

theorem reach_perm {B : ℝ} {l l' : List ℝ}
    (h : Relation.ReflTransGen (AdjSwap B) l l') : List.Perm l' l := by
  induction h with
  | refl => exact List.Perm.refl _
  | tail _ hstep ih => exact (adjSwap_perm hstep).trans ih

/-- Along a chain of swaps, a value starting above `c` and never landing in `[-c, c]` stays
above `c`. -/
theorem ivt' {B c : ℝ} (g : List ℝ → ℝ)
    (hstep : ∀ l l', AdjSwap B l l' → |g l - g l'| ≤ 2 * c)
    {a b : List ℝ} (hab : Relation.ReflTransGen (AdjSwap B) a b)
    (hno : ∀ z, Relation.ReflTransGen (AdjSwap B) a z → ¬ (|g z| ≤ c))
    (ha : c < g a) : c < g b := by
  induction hab with
  | refl => exact ha
  | tail hpath hstep' ih =>
    rename_i y z
    have hy : c < g y := ih
    have hbound := hstep y z hstep'
    have hnz := hno z (hpath.tail hstep')
    rw [abs_le] at hbound
    rw [not_le, lt_abs] at hnz
    rcases hnz with hzz | hzz
    · exact hzz
    · linarith [hbound.1, hbound.2]

/-- **IMO 1997 P3.** -/
theorem imo1997_p3 (n : ℕ) (x : List ℝ) (hlen : x.length = n)
    (hsum : |x.sum| = 1) (hbd : ∀ a ∈ x, |a| ≤ ((n : ℝ) + 1) / 2) :
    ∃ y : List ℝ, List.Perm y x ∧ |f y| ≤ ((n : ℝ) + 1) / 2 := by
  set c : ℝ := ((n : ℝ) + 1) / 2 with hcdef
  have hc : 0 ≤ c := by positivity
  by_contra hcon
  have hcon' : ∀ y : List ℝ, List.Perm y x → ¬ (|f y| ≤ c) := by
    intro y hy hle
    exact hcon ⟨y, hy, hle⟩
  have hrev : Relation.ReflTransGen (AdjSwap c) x x.reverse := reach_reverse x hbd
  have hno : ∀ z, Relation.ReflTransGen (AdjSwap c) x z → ¬ (|f z| ≤ c) :=
    fun z hz => hcon' z (reach_perm hz)
  have hkey : f x + f x.reverse = ((n : ℝ) + 1) * x.sum := by
    rw [f_add_reverse, hlen]
  have hx := hno x Relation.ReflTransGen.refl
  have hrv := hno _ hrev
  rw [not_le] at hx hrv
  have hsum2 : f x + f x.reverse = 2 * c ∨ f x + f x.reverse = -(2 * c) := by
    rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).1 hsum with hh | hh
    · left; rw [hkey, hh, hcdef]; ring
    · right; rw [hkey, hh, hcdef]; ring
  rw [lt_abs] at hx hrv
  rcases hx with hx | hx
  · -- `c < f x` : run the argument for `f`
    have hrvneg : f x.reverse < -c := by
      rcases hsum2 with hh | hh
      · rcases hrv with hr | hr
        · linarith
        · linarith
      · linarith
    have hfinal : c < f x.reverse :=
      ivt' f (fun l l' hsw => adjSwap_f hsw) hrev hno hx
    linarith
  · -- `c < -(f x)` : run the argument for `-f`
    have hrvpos : c < f x.reverse := by
      rcases hsum2 with hh | hh
      · linarith
      · rcases hrv with hr | hr
        · exact hr
        · linarith
    have hs' : ∀ l l', AdjSwap c l l' → |(-f l) - (-f l')| ≤ 2 * c := by
      intro l l' hsw
      have hb := adjSwap_f hsw
      rw [show -f l - -f l' = -(f l - f l') by ring, abs_neg]
      exact hb
    have hno' : ∀ z, Relation.ReflTransGen (AdjSwap c) x z → ¬ (|(-f z)| ≤ c) := by
      intro z hz hle
      exact hno z hz (by rwa [abs_neg] at hle)
    have hfinal : c < -(f x.reverse) := ivt' (fun l => -f l) hs' hrev hno' hx
    linarith

end Imo1997P3
