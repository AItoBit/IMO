import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

/-!
# IMO 1975, Problem 6

Find all polynomials `P` in two variables such that

* (i) for a positive integer `n` and all real `t, x, y`, `P (t x, t y) = tⁿ P (x, y)`
  (that is, `P` is homogeneous of degree `n`);
* (ii) for all real `a, b, c`, `P (b + c, a) + P (c + a, b) + P (a + b, c) = 0`;
* (iii) `P (1, 0) = 1`.

The answer is `P (x, y) = (x - 2 y) (x + y) ^ (n - 1)`.
-/

namespace Imo1975P6

open MvPolynomial

noncomputable section

/-- Evaluation of a two-variable real polynomial at a point `(x, y)`. -/
def ev (P : MvPolynomial (Fin 2) ℝ) (x y : ℝ) : ℝ := eval ![x, y] P

@[simp] lemma ev_add (P Q : MvPolynomial (Fin 2) ℝ) (x y : ℝ) :
    ev (P + Q) x y = ev P x y + ev Q x y := by simp [ev]

@[simp] lemma ev_mul (P Q : MvPolynomial (Fin 2) ℝ) (x y : ℝ) :
    ev (P * Q) x y = ev P x y * ev Q x y := by simp [ev]

@[simp] lemma ev_sub (P Q : MvPolynomial (Fin 2) ℝ) (x y : ℝ) :
    ev (P - Q) x y = ev P x y - ev Q x y := by simp [ev]

@[simp] lemma ev_pow (P : MvPolynomial (Fin 2) ℝ) (k : ℕ) (x y : ℝ) :
    ev (P ^ k) x y = (ev P x y) ^ k := by simp [ev]

@[simp] lemma ev_X0 (x y : ℝ) : ev (X 0) x y = x := by simp [ev]

@[simp] lemma ev_X1 (x y : ℝ) : ev (X 1) x y = y := by simp [ev]

@[simp] lemma ev_C (r : ℝ) (x y : ℝ) : ev (C r) x y = r := by simp [ev]

@[simp] lemma ev_zero (x y : ℝ) : ev 0 x y = 0 := by simp [ev]

/-- Two-variable polynomials with the same evaluation everywhere are equal. -/
lemma ev_funext {P Q : MvPolynomial (Fin 2) ℝ} (h : ∀ x y : ℝ, ev P x y = ev Q x y) : P = Q := by
  apply MvPolynomial.funext
  intro v
  have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
  rw [hv]; exact h (v 0) (v 1)

lemma X0_add_X1_ne_zero : (X 0 + X 1 : MvPolynomial (Fin 2) ℝ) ≠ 0 := by
  intro h
  have := congrArg (fun Q => ev Q 1 0) h
  simp [ev_add] at this

/-! ### Divisibility by `x + y` -/

/-- Substitution `x ↦ -y`, `y ↦ y`. -/
def antidiag (P : MvPolynomial (Fin 2) ℝ) : MvPolynomial (Fin 2) ℝ := bind₁ ![-X 1, X 1] P

lemma ev_antidiag (P : MvPolynomial (Fin 2) ℝ) (x y : ℝ) : ev (antidiag P) x y = ev P (-y) y := by
  unfold ev antidiag
  rw [show (eval ![x, y]) (bind₁ ![-X 1, X 1] P)
      = eval (fun i => eval ![x, y] (![-X 1, X 1] i)) P by
        simpa using eval₂Hom_bind₁ (RingHom.id ℝ) ![x, y] ![-X 1, X 1] P]
  have h : (fun i => (eval ![x, y]) (![-X 1, X 1] i)) = ![-y, y] := by
    funext i; fin_cases i <;> simp
  rw [h]

lemma dvd_sub_antidiag (P : MvPolynomial (Fin 2) ℝ) : (X 0 + X 1) ∣ (P - antidiag P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [antidiag]
  | add p q hp hq =>
      have h : p + q - antidiag (p + q) = (p - antidiag p) + (q - antidiag q) := by
        simp only [antidiag, map_add]; ring
      rw [h]; exact dvd_add hp hq
  | mul_X p i hp =>
      fin_cases i
      · show (X 0 + X 1) ∣ p * X 0 - antidiag (p * X 0)
        have ha : antidiag (p * X 0) = antidiag p * (-X 1) := by
          simp only [antidiag, map_mul]; simp
        have h : p * X 0 - antidiag (p * X 0)
            = (p - antidiag p) * X 0 + antidiag p * (X 0 + X 1) := by
          rw [ha]; ring
        rw [h]
        exact dvd_add (Dvd.dvd.mul_right hp _) (Dvd.dvd.mul_left dvd_rfl _)
      · show (X 0 + X 1) ∣ p * X 1 - antidiag (p * X 1)
        have ha : antidiag (p * X 1) = antidiag p * X 1 := by
          simp only [antidiag, map_mul]; simp
        have h : p * X 1 - antidiag (p * X 1) = (p - antidiag p) * X 1 := by
          rw [ha]; ring
        rw [h]
        exact Dvd.dvd.mul_right hp _

/-- A two-variable polynomial vanishing on the line `x + y = 0` is divisible by `x + y`. -/
lemma dvd_of_vanishing (P : MvPolynomial (Fin 2) ℝ) (h : ∀ y : ℝ, ev P (-y) y = 0) :
    (X 0 + X 1) ∣ P := by
  have h0 : antidiag P = 0 := by
    apply ev_funext
    intro x y
    rw [ev_antidiag, h, ev_zero]
  have hd := dvd_sub_antidiag P
  rwa [h0, sub_zero] at hd

/-! ### The cyclic condition at the level of polynomials -/

/-- The three-variable polynomial `P (b + c, a) + P (c + a, b) + P (a + b, c)`. -/
def cyc (P : MvPolynomial (Fin 2) ℝ) : MvPolynomial (Fin 3) ℝ :=
  bind₁ ![X 1 + X 2, X 0] P + bind₁ ![X 2 + X 0, X 1] P + bind₁ ![X 0 + X 1, X 2] P

lemma eval_bind3 (f : Fin 2 → MvPolynomial (Fin 3) ℝ) (P : MvPolynomial (Fin 2) ℝ)
    (x : Fin 3 → ℝ) : eval x (bind₁ f P) = eval (fun i => eval x (f i)) P := by
  simpa using eval₂Hom_bind₁ (RingHom.id ℝ) x f P

lemma eval_cyc (P : MvPolynomial (Fin 2) ℝ) (a b c : ℝ) :
    eval ![a, b, c] (cyc P) = ev P (b + c) a + ev P (c + a) b + ev P (a + b) c := by
  unfold cyc ev
  simp only [map_add, eval_bind3]
  have h1 : (fun i => (eval ![a, b, c]) (![X 1 + X 2, X 0] i)) = ![b + c, a] := by
    funext i; fin_cases i <;> simp
  have h2 : (fun i => (eval ![a, b, c]) (![X 2 + X 0, X 1] i)) = ![c + a, b] := by
    funext i; fin_cases i <;> simp
  have h3 : (fun i => (eval ![a, b, c]) (![X 0 + X 1, X 2] i)) = ![a + b, c] := by
    funext i; fin_cases i <;> simp
  rw [h1, h2, h3]

lemma cyc_eq_zero_iff (P : MvPolynomial (Fin 2) ℝ) :
    cyc P = 0 ↔ ∀ a b c : ℝ, ev P (b + c) a + ev P (c + a) b + ev P (a + b) c = 0 := by
  constructor
  · intro h a b c
    rw [← eval_cyc, h, map_zero]
  · intro h
    apply MvPolynomial.funext
    intro v
    have hv : v = ![v 0, v 1, v 2] := by funext i; fin_cases i <;> rfl
    rw [hv, map_zero, eval_cyc]
    exact h _ _ _

/-! ### Scaling -/

/-- Substitution `x ↦ t x`, `y ↦ t y`. -/
def scal (t : ℝ) (P : MvPolynomial (Fin 2) ℝ) : MvPolynomial (Fin 2) ℝ :=
  bind₁ ![C t * X 0, C t * X 1] P

lemma ev_scal (t : ℝ) (P : MvPolynomial (Fin 2) ℝ) (x y : ℝ) :
    ev (scal t P) x y = ev P (t * x) (t * y) := by
  unfold ev scal
  rw [show (eval ![x, y]) (bind₁ ![C t * X 0, C t * X 1] P)
      = eval (fun i => eval ![x, y] (![C t * X 0, C t * X 1] i)) P by
        simpa using eval₂Hom_bind₁ (RingHom.id ℝ) ![x, y] ![C t * X 0, C t * X 1] P]
  have h : (fun i => (eval ![x, y]) (![C t * X 0, C t * X 1] i)) = ![t * x, t * y] := by
    funext i; fin_cases i <;> simp
  rw [h]

lemma scal_eq_iff (n : ℕ) (P : MvPolynomial (Fin 2) ℝ) :
    (∀ t : ℝ, scal t P = C (t ^ n) * P) ↔
      (∀ t x y : ℝ, ev P (t * x) (t * y) = t ^ n * ev P x y) := by
  constructor
  · intro h t x y
    have := congrArg (fun Q => ev Q x y) (h t)
    simpa [ev_scal] using this
  · intro h t
    apply ev_funext
    intro x y
    rw [ev_scal, ev_mul, ev_C, h]

/-! ### The case `n = 1` -/

/-- A degree-one homogeneous polynomial satisfying the cyclic condition and vanishing at
`(1, 0)` is zero. -/
lemma eq_zero_of_deg_one (R : MvPolynomial (Fin 2) ℝ)
    (h1 : ∀ t x y : ℝ, ev R (t * x) (t * y) = t * ev R x y)
    (h2 : ∀ a b c : ℝ, ev R (b + c) a + ev R (c + a) b + ev R (a + b) c = 0)
    (h3 : ev R 1 0 = 0) : R = 0 := by
  have hx0 : ∀ x : ℝ, ev R x 0 = 0 := by
    intro x
    have := h1 x 1 0
    simpa [h3] using this
  have hanti : ∀ a b : ℝ, ev R a b = - ev R b a := by
    intro a b
    have := h2 a b 0
    rw [add_zero, zero_add, hx0] at this
    linarith
  have hkey : ∀ u : ℝ, ev R (2 * u + 1) 1 = ev R u 1 := by
    intro u
    have h := h2 1 1 (2 * u)
    have h4 : ev R 2 (2 * u) = 2 * ev R 1 u := by
      have := h1 2 1 u
      norm_num at this
      exact this
    norm_num at h
    rw [h4, hanti 1 u] at h
    have h6 : (1 : ℝ) + 2 * u = 2 * u + 1 := by ring
    rw [h6] at h
    linarith
  -- the one-variable polynomial `x ↦ R (x, 1)`
  set f : Polynomial ℝ := aeval ![Polynomial.X, (1 : Polynomial ℝ)] R with hf
  have hev : ∀ x : ℝ, Polynomial.eval x f = ev R x 1 := by
    intro x
    have h : (Polynomial.aeval x).comp (MvPolynomial.aeval ![Polynomial.X, (1 : Polynomial ℝ)])
        = (MvPolynomial.aeval ![x, (1 : ℝ)] : MvPolynomial (Fin 2) ℝ →ₐ[ℝ] ℝ) := by
      apply MvPolynomial.algHom_ext
      intro i; fin_cases i <;> simp
    have h2 := congrArg (fun g => g R) h
    simpa [ev, hf, MvPolynomial.aeval_eq_eval] using h2
  have hroot : ∀ k : ℕ, Polynomial.eval ((2 : ℝ) ^ k - 1) f = 0 := by
    intro k
    induction k with
    | zero => simpa [hev] using (hanti 0 1).trans (by rw [h3]; ring)
    | succ k ih =>
        have hstep : (2 : ℝ) ^ (k + 1) - 1 = 2 * ((2 : ℝ) ^ k - 1) + 1 := by ring
        rw [hstep, hev, hkey, ← hev]
        exact ih
  have hf0 : f = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply Set.infinite_of_injective_forall_mem (f := fun k : ℕ => (2 : ℝ) ^ k - 1)
    · have hm : StrictMono (fun k : ℕ => (2 : ℝ) ^ k - 1) := by
        intro a b hab
        simp only [sub_lt_sub_iff_right]
        gcongr
        norm_num
      exact hm.injective
    · intro k
      exact hroot k
  apply ev_funext
  intro x y
  rw [ev_zero]
  rcases eq_or_ne y 0 with rfl | hy
  · exact hx0 x
  · have hh := h1 y (x / y) 1
    rw [mul_one, mul_div_cancel₀ _ hy] at hh
    rw [hh, ← hev, hf0]
    simp

/-! ### The main classification -/

lemma X012_ne_zero : (X 0 + X 1 + X 2 : MvPolynomial (Fin 3) ℝ) ≠ 0 := by
  intro h
  have := congrArg (fun Q => eval ![(1 : ℝ), 0, 0] Q) h
  simp at this

lemma ev_answer (k : ℕ) (x y : ℝ) :
    ev ((X 0 - 2 * X 1) * (X 0 + X 1) ^ k) x y = (x - 2 * y) * (x + y) ^ k := by
  simp [ev]

lemma ev_shift (P : MvPolynomial (Fin 2) ℝ) (x y : ℝ) :
    ev (P - (X 0 - 2 * X 1)) x y = ev P x y - (x - 2 * y) := by simp [ev]

/-- The classification of the solutions:  a two-variable real polynomial `P` satisfying the
three conditions of the problem for a positive integer `n` equals `(x - 2 y) (x + y) ^ (n - 1)`. -/
theorem eq_answer_of_conditions : ∀ n : ℕ, 0 < n → ∀ P : MvPolynomial (Fin 2) ℝ,
    (∀ t x y : ℝ, ev P (t * x) (t * y) = t ^ n * ev P x y) →
    (∀ a b c : ℝ, ev P (b + c) a + ev P (c + a) b + ev P (a + b) c = 0) →
    ev P 1 0 = 1 → P = (X 0 - 2 * X 1) * (X 0 + X 1) ^ (n - 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro hn P h1 h2 h3
    match n, hn, h1, IH with
    | 1, _, h1, _ =>
        -- Base case `n = 1`.
        have hzero : P - (X 0 - 2 * X 1) = 0 := by
          apply eq_zero_of_deg_one
          · intro t x y
            rw [ev_shift, ev_shift, h1 t x y]
            ring
          · intro a b c
            rw [ev_shift, ev_shift, ev_shift]
            have := h2 a b c
            linarith
          · rw [ev_shift, h3]
            ring
        have hP : P = X 0 - 2 * X 1 := sub_eq_zero.mp hzero
        simp [hP]
    | (m + 2), _, h1, IH =>
        -- Inductive step.
        have hneg : ev P (-1) 1 = 0 := by
          have hc := h2 1 1 (-2)
          have hs : ev P 2 (-2) = (-2 : ℝ) ^ (m + 2) * ev P (-1) 1 := by
            have := h1 (-2) (-1) 1
            norm_num at this
            exact this
          norm_num at hc
          rw [hs] at hc
          have hfac : ((-2 : ℝ)) ^ (m + 2) + 2 ≠ 0 := by
            rcases Nat.even_or_odd (m + 2) with he | ho
            · rw [he.neg_pow]
              positivity
            · rw [ho.neg_pow]
              have h4 : (4 : ℝ) ≤ 2 ^ (m + 2) := by
                calc (4 : ℝ) = 2 ^ 2 := by norm_num
                  _ ≤ 2 ^ (m + 2) := by
                      apply pow_le_pow_right₀ (by norm_num) (by omega)
              intro hcon
              linarith
          have : ((-2 : ℝ) ^ (m + 2) + 2) * ev P (-1) 1 = 0 := by linarith
          rcases mul_eq_zero.mp this with h | h
          · exact absurd h hfac
          · exact h
        have hvan : ∀ y : ℝ, ev P (-y) y = 0 := by
          intro y
          have h := h1 y (-1) 1
          rw [mul_one, show y * (-1 : ℝ) = -y by ring, hneg, mul_zero] at h
          exact h
        obtain ⟨Q, hQ⟩ := dvd_of_vanishing P hvan
        have hevQ : ∀ x y : ℝ, ev P x y = (x + y) * ev Q x y := by
          intro x y; rw [hQ]; simp
        have hscalP : ∀ t : ℝ, scal t P = C (t ^ (m + 2)) * P := (scal_eq_iff _ P).mpr h1
        have hscalQ : ∀ t : ℝ, t ≠ 0 → scal t Q = C (t ^ (m + 1)) * Q := by
          intro t ht
          have hne : (C t * (X 0 + X 1) : MvPolynomial (Fin 2) ℝ) ≠ 0 :=
            mul_ne_zero (by simpa using ht) X0_add_X1_ne_zero
          apply mul_left_cancel₀ hne
          have hsp : scal t P = C t * (X 0 + X 1) * scal t Q := by
            rw [hQ]
            unfold scal
            rw [map_mul, map_add, bind₁_X_right, bind₁_X_right]
            simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
            ring
          rw [← hsp, hscalP t, hQ, show (t : ℝ) ^ (m + 2) = t * t ^ (m + 1) by ring, map_mul]
          ring
        have hQ00 : ev Q 0 0 = 0 := by
          have h := congrArg (fun R => ev R 0 0) (hscalQ 2 two_ne_zero)
          simp only [ev_scal, mul_zero, ev_mul, ev_C] at h
          have h2m : (2 : ℝ) ^ (m + 1) ≠ 1 := by
            have : (2 : ℝ) ^ 1 ≤ 2 ^ (m + 1) := by
              apply pow_le_pow_right₀ (by norm_num) (by omega)
            intro hcon
            rw [hcon] at this
            norm_num at this
          have hz : ((2 : ℝ) ^ (m + 1) - 1) * ev Q 0 0 = 0 := by linarith
          rcases mul_eq_zero.mp hz with h' | h'
          · exact absurd (sub_eq_zero.mp h') h2m
          · exact h'
        have h1Q : ∀ t x y : ℝ, ev Q (t * x) (t * y) = t ^ (m + 1) * ev Q x y := by
          intro t x y
          rcases eq_or_ne t 0 with rfl | ht
          · simp [hQ00]
          · have := congrArg (fun R => ev R x y) (hscalQ t ht)
            simpa [ev_scal] using this
        have h2Q : ∀ a b c : ℝ, ev Q (b + c) a + ev Q (c + a) b + ev Q (a + b) c = 0 := by
          rw [← cyc_eq_zero_iff]
          have hcp : cyc P = (X 0 + X 1 + X 2) * cyc Q := by
            unfold cyc
            rw [hQ]
            simp only [map_mul, map_add, bind₁_X_right, Matrix.cons_val_zero,
              Matrix.cons_val_one]
            ring
          have hz : cyc P = 0 := (cyc_eq_zero_iff P).mpr h2
          rw [hcp] at hz
          rcases mul_eq_zero.mp hz with h | h
          · exact absurd h X012_ne_zero
          · exact h
        have h3Q : ev Q 1 0 = 1 := by
          have := hevQ 1 0
          rw [h3] at this
          simpa using this.symm
        have hIH := IH (m + 1) (by omega) (by omega) Q h1Q h2Q h3Q
        rw [show m + 1 - 1 = m by omega] at hIH
        rw [show m + 2 - 1 = m + 1 by omega, hQ, hIH, pow_succ]
        ring

/-- **IMO 1975, Problem 6.**  For a positive integer `n`, the two-variable real polynomials `P`
which are homogeneous of degree `n`, satisfy `P (b + c, a) + P (c + a, b) + P (a + b, c) = 0`
for all real `a, b, c`, and satisfy `P (1, 0) = 1`, are exactly `(x - 2 y) (x + y) ^ (n - 1)`. -/
theorem imo1975_p6 (n : ℕ) (hn : 0 < n) (P : MvPolynomial (Fin 2) ℝ) :
    ((∀ t x y : ℝ, ev P (t * x) (t * y) = t ^ n * ev P x y) ∧
      (∀ a b c : ℝ, ev P (b + c) a + ev P (c + a) b + ev P (a + b) c = 0) ∧
      ev P 1 0 = 1) ↔
      P = (X 0 - 2 * X 1) * (X 0 + X 1) ^ (n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  constructor
  · rintro ⟨h1, h2, h3⟩
    have h := eq_answer_of_conditions (m + 1) hn P h1 h2 h3
    rwa [Nat.add_sub_cancel] at h
  · rintro rfl
    refine ⟨?_, ?_, ?_⟩
    · intro t x y
      rw [ev_answer, ev_answer, show t * x - 2 * (t * y) = t * (x - 2 * y) by ring,
        show t * x + t * y = t * (x + y) by ring, mul_pow, pow_succ]
      ring
    · intro a b c
      rw [ev_answer, ev_answer, ev_answer, show b + c + a = a + b + c by ring,
        show c + a + b = a + b + c by ring]
      ring
    · rw [ev_answer]
      norm_num

end

end Imo1975P6
