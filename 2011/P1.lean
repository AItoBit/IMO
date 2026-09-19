import Mathlib

/-!
# IMO 2011 Problem 1

For four distinct positive integers

    a < b < c < d

write

    S = a + b + c + d.

A pair is good when the sum of its two elements divides `S`.

This file proves:

1. `(b,d)` and `(c,d)` can never be good;
2. therefore at most four pairs are good;
3. `{p,5p,7p,11p}` has exactly four good pairs;
4. `{p,11p,19p,29p}` has exactly four good pairs;
5. hence the maximum possible value is `4`.

No `sorry`, `admit`, or extra axioms are used.
-/

namespace IMO2011P1

/-- Sum of the four elements. -/
def total (a b c d : ℕ) : ℕ :=
  a + b + c + d

/-- `x,y` form a good pair when `x+y` divides the total. -/
def GoodPair
    (a b c d x y : ℕ) : Prop :=
  x + y ∣ total a b c d

/--
Explicit decidability instance.

This avoids instance-search problems when `GoodPair` appears
inside the indicator function below.
-/
instance instDecidableGoodPair
    (a b c d x y : ℕ) :
    Decidable (GoodPair a b c d x y) := by
  unfold GoodPair
  infer_instance

/-- Convert a proposition to `0` or `1`. -/
def indicator (P : Prop) [Decidable P] : ℕ :=
  if P then 1 else 0

/-- Every indicator is at most one. -/
lemma indicator_le_one
    (P : Prop)
    [Decidable P] :
    indicator P ≤ 1 := by
  unfold indicator
  split_ifs <;> omega

/--
Number of good unordered pairs among

    (a,b), (a,c), (a,d),
    (b,c), (b,d), (c,d).
-/
def goodPairCount
    (a b c d : ℕ) : ℕ :=
  indicator (GoodPair a b c d a b) +
  indicator (GoodPair a b c d a c) +
  indicator (GoodPair a b c d a d) +
  indicator (GoodPair a b c d b c) +
  indicator (GoodPair a b c d b d) +
  indicator (GoodPair a b c d c d)

/-!
## Basic divisibility obstruction
-/

/--
If

    x < S < 2*x,

then `x` cannot divide `S`.
-/
lemma not_dvd_between
    {x S : ℕ}
    (h₁ : x < S)
    (h₂ : S < 2 * x) :
    ¬ x ∣ S := by

  intro hdiv

  rcases hdiv with ⟨k, hk⟩

  have hx : 0 < x := by
    by_contra hx0
    have hx' : x = 0 := by
      omega
    subst x
    simp at h₂

  have hk_ge_two : 2 ≤ k := by
    by_contra hklt

    have hk_le_one :
        k ≤ 1 := by
      omega

    rw [hk] at h₁

    nlinarith

  rw [hk] at h₂

  nlinarith

/-!
## Two pairs are impossible
-/

/--
For

    0 < a < b < c < d,

the pair `(b,d)` is not good.
-/
lemma pair_bd_not_good
    {a b c d : ℕ}
    (ha : 0 < a)
    (hab : a < b)
    (hbc : b < c)
    (hcd : c < d) :
    ¬ GoodPair a b c d b d := by

  unfold GoodPair total

  apply not_dvd_between

  · omega

  · omega

/--
For

    0 < a < b < c < d,

the pair `(c,d)` is not good.
-/
lemma pair_cd_not_good
    {a b c d : ℕ}
    (ha : 0 < a)
    (hab : a < b)
    (hbc : b < c)
    (hcd : c < d) :
    ¬ GoodPair a b c d c d := by

  unfold GoodPair total

  apply not_dvd_between

  · omega

  · omega

/-!
## Upper bound n_A ≤ 4
-/

/--
At most four of the six pairs can be good.
-/
theorem goodPairCount_le_four
    {a b c d : ℕ}
    (ha : 0 < a)
    (hab : a < b)
    (hbc : b < c)
    (hcd : c < d) :
    goodPairCount a b c d ≤ 4 := by

  have hbd :
      ¬ GoodPair a b c d b d :=
    pair_bd_not_good ha hab hbc hcd

  have hcd' :
      ¬ GoodPair a b c d c d :=
    pair_cd_not_good ha hab hbc hcd

  have h1 :
      indicator (GoodPair a b c d a b) ≤ 1 :=
    indicator_le_one _

  have h2 :
      indicator (GoodPair a b c d a c) ≤ 1 :=
    indicator_le_one _

  have h3 :
      indicator (GoodPair a b c d a d) ≤ 1 :=
    indicator_le_one _

  have h4 :
      indicator (GoodPair a b c d b c) ≤ 1 :=
    indicator_le_one _

  have h5 :
      indicator (GoodPair a b c d b d) = 0 := by
    simp [indicator, hbd]

  have h6 :
      indicator (GoodPair a b c d c d) = 0 := by
    simp [indicator, hcd']

  unfold goodPairCount

  rw [h5, h6]

  omega

/-!
## First extremal family: {p,5p,7p,11p}
-/

lemma family1_ab
    (p : ℕ) :
    GoodPair
      p (5 * p) (7 * p) (11 * p)
      p (5 * p) := by

  unfold GoodPair total

  refine ⟨4, ?_⟩

  ring

lemma family1_ac
    (p : ℕ) :
    GoodPair
      p (5 * p) (7 * p) (11 * p)
      p (7 * p) := by

  unfold GoodPair total

  refine ⟨3, ?_⟩

  ring

lemma family1_ad
    (p : ℕ) :
    GoodPair
      p (5 * p) (7 * p) (11 * p)
      p (11 * p) := by

  unfold GoodPair total

  refine ⟨2, ?_⟩

  ring

lemma family1_bc
    (p : ℕ) :
    GoodPair
      p (5 * p) (7 * p) (11 * p)
      (5 * p) (7 * p) := by

  unfold GoodPair total

  refine ⟨2, ?_⟩

  ring

lemma family1_bd_not
    {p : ℕ}
    (hp : 0 < p) :
    ¬ GoodPair
      p (5 * p) (7 * p) (11 * p)
      (5 * p) (11 * p) := by

  apply pair_bd_not_good

  · exact hp

  · nlinarith

  · nlinarith

  · nlinarith

lemma family1_cd_not
    {p : ℕ}
    (hp : 0 < p) :
    ¬ GoodPair
      p (5 * p) (7 * p) (11 * p)
      (7 * p) (11 * p) := by

  apply pair_cd_not_good

  · exact hp

  · nlinarith

  · nlinarith

  · nlinarith

/--
The family `{p,5p,7p,11p}` has exactly four good pairs.
-/
theorem family1_count
    {p : ℕ}
    (hp : 0 < p) :
    goodPairCount
      p (5 * p) (7 * p) (11 * p) = 4 := by

  have h1 :
      GoodPair
        p (5 * p) (7 * p) (11 * p)
        p (5 * p) :=
    family1_ab p

  have h2 :
      GoodPair
        p (5 * p) (7 * p) (11 * p)
        p (7 * p) :=
    family1_ac p

  have h3 :
      GoodPair
        p (5 * p) (7 * p) (11 * p)
        p (11 * p) :=
    family1_ad p

  have h4 :
      GoodPair
        p (5 * p) (7 * p) (11 * p)
        (5 * p) (7 * p) :=
    family1_bc p

  have h5 :
      ¬ GoodPair
        p (5 * p) (7 * p) (11 * p)
        (5 * p) (11 * p) :=
    family1_bd_not hp

  have h6 :
      ¬ GoodPair
        p (5 * p) (7 * p) (11 * p)
        (7 * p) (11 * p) :=
    family1_cd_not hp

  simp [
    goodPairCount,
    indicator,
    h1,
    h2,
    h3,
    h4,
    h5,
    h6
  ]

/-!
## Second extremal family: {p,11p,19p,29p}
-/

lemma family2_ab
    (p : ℕ) :
    GoodPair
      p (11 * p) (19 * p) (29 * p)
      p (11 * p) := by

  unfold GoodPair total

  refine ⟨5, ?_⟩

  ring

lemma family2_ac
    (p : ℕ) :
    GoodPair
      p (11 * p) (19 * p) (29 * p)
      p (19 * p) := by

  unfold GoodPair total

  refine ⟨3, ?_⟩

  ring

lemma family2_ad
    (p : ℕ) :
    GoodPair
      p (11 * p) (19 * p) (29 * p)
      p (29 * p) := by

  unfold GoodPair total

  refine ⟨2, ?_⟩

  ring

lemma family2_bc
    (p : ℕ) :
    GoodPair
      p (11 * p) (19 * p) (29 * p)
      (11 * p) (19 * p) := by

  unfold GoodPair total

  refine ⟨2, ?_⟩

  ring

lemma family2_bd_not
    {p : ℕ}
    (hp : 0 < p) :
    ¬ GoodPair
      p (11 * p) (19 * p) (29 * p)
      (11 * p) (29 * p) := by

  apply pair_bd_not_good

  · exact hp

  · nlinarith

  · nlinarith

  · nlinarith

lemma family2_cd_not
    {p : ℕ}
    (hp : 0 < p) :
    ¬ GoodPair
      p (11 * p) (19 * p) (29 * p)
      (19 * p) (29 * p) := by

  apply pair_cd_not_good

  · exact hp

  · nlinarith

  · nlinarith

  · nlinarith

/--
The family `{p,11p,19p,29p}` has exactly four good pairs.
-/
theorem family2_count
    {p : ℕ}
    (hp : 0 < p) :
    goodPairCount
      p (11 * p) (19 * p) (29 * p) = 4 := by

  have h1 :
      GoodPair
        p (11 * p) (19 * p) (29 * p)
        p (11 * p) :=
    family2_ab p

  have h2 :
      GoodPair
        p (11 * p) (19 * p) (29 * p)
        p (19 * p) :=
    family2_ac p

  have h3 :
      GoodPair
        p (11 * p) (19 * p) (29 * p)
        p (29 * p) :=
    family2_ad p

  have h4 :
      GoodPair
        p (11 * p) (19 * p) (29 * p)
        (11 * p) (19 * p) :=
    family2_bc p

  have h5 :
      ¬ GoodPair
        p (11 * p) (19 * p) (29 * p)
        (11 * p) (29 * p) :=
    family2_bd_not hp

  have h6 :
      ¬ GoodPair
        p (11 * p) (19 * p) (29 * p)
        (19 * p) (29 * p) :=
    family2_cd_not hp

  simp [
    goodPairCount,
    indicator,
    h1,
    h2,
    h3,
    h4,
    h5,
    h6
  ]

/-!
## Maximum value
-/

/--
The maximum possible number of good pairs is `4`.

The first conjunct proves the universal upper bound.
The second gives an example attaining it.
-/
theorem maximum_is_four :
    (∀ a b c d : ℕ,
        0 < a →
        a < b →
        b < c →
        c < d →
        goodPairCount a b c d ≤ 4)
    ∧
    (∃ a b c d : ℕ,
        0 < a ∧
        a < b ∧
        b < c ∧
        c < d ∧
        goodPairCount a b c d = 4) := by

  constructor

  · intro a b c d ha hab hbc hcd

    exact
      goodPairCount_le_four
        ha hab hbc hcd

  · refine
      ⟨1, 5, 7, 11,
       by norm_num,
       by norm_num,
       by norm_num,
       by norm_num,
       ?_⟩

    exact
      family1_count
        (p := 1)
        (by norm_num)

/--
Both families appearing in the IMO answer attain the maximum.
-/
theorem answer_families_attain_maximum
    (p : ℕ)
    (hp : 0 < p) :
    goodPairCount
        p (5 * p) (7 * p) (11 * p) = 4
    ∧
    goodPairCount
        p (11 * p) (19 * p) (29 * p) = 4 := by

  constructor

  · exact family1_count hp

  · exact family2_count hp

end IMO2011P1
