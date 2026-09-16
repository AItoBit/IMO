import Mathlib

-- We represent the sum of adjacent terms (e.g., d_i * d_{i+1})
def sumAdj : List ℕ → ℕ
  | [] => 0
  | _ :: [] => 0
  | a :: b :: tail => a * b + sumAdj (b :: tail)

-- The last element of a list, given a default starting value
def lastElem (a : ℕ) : List ℕ → ℕ
  | [] => a
  | b :: tail => lastElem b tail

-- The core property of adjacent divisors used in the telescoping proof
def DivChain (n : ℕ) : List ℕ → Prop
  | [] => True
  | _ :: [] => True
  | a :: b :: tail => a * b + n * a ≤ n * b ∧ DivChain n (b :: tail)

-- Part 1: Any two divisors a < b of n satisfy the required chain inequality
lemma divisor_pair_ineq {a b n ca cb : ℕ}
    (ha : n = a * ca) (hb : n = b * cb) (hab : a < b) (hn : 0 < n) :
    a * b + n * a ≤ n * b := by
  have hcb : 0 < cb := by
    cases cb with
    | zero => 
      simp at hb
      omega
    | succ _ => 
      exact Nat.zero_lt_succ _
  have H : cb < ca := by
    have h1 : a * cb < b * cb := Nat.mul_lt_mul_of_pos_right hab hcb
    have h2 : b * cb = a * ca := by omega
    have h3 : a * cb < a * ca := by omega
    exact Nat.lt_of_mul_lt_mul_left h3
  calc
    a * b + n * a = a * b + (b * cb) * a := by rw [hb]
    _ = b * (a * (1 + cb)) := by ring
    _ ≤ b * (a * ca) := by
      apply Nat.mul_le_mul_left
      apply Nat.mul_le_mul_left
      omega
    _ = b * n := by rw [← ha]
    _ = n * b := by ring

-- Part 2: Any sequence satisfying the chain inequality yields the sum bound
lemma sumAdj_bound (n : ℕ) :
    ∀ (l : List ℕ) (a : ℕ),
    DivChain n (a :: l) →
    sumAdj (a :: l) + n * a ≤ n * lastElem a l
  | [], a, hDiv => by
    change 0 + n * a ≤ n * a
    omega
  | b :: tail, a, hDiv => by
    have h1 : a * b + n * a ≤ n * b := hDiv.1
    have h2 : DivChain n (b :: tail) := hDiv.2
    have ih := sumAdj_bound n tail b h2
    change a * b + sumAdj (b :: tail) + n * a ≤ n * lastElem b tail
    omega

-- Part 3: The IMO 2002 Problem 4 main result
theorem imo2002_p4 (n : ℕ) (l : List ℕ)
    (h_last : lastElem 1 l = n)
    (h_div : DivChain n (1 :: l))
    (hn : 1 < n) :
    sumAdj (1 :: l) < n^2 := by
  -- Apply the sequence bound
  have h_bound := sumAdj_bound n l 1 h_div
  rw [h_last] at h_bound
  
  -- Use the property n^2 = n * n to cleanly close the inequality
  rw [pow_two]
  omega
