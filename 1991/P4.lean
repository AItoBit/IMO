import Mathlib

namespace IMO1991P4

/--
Represents the mathematical property required at each vertex of degree >= 2:
The greatest common divisor of its incident edge labels must equal 1.
-/
def ValidVertexLabeling (incident_labels : List ℕ) : Prop :=
  ∀ d : ℕ, (∀ x ∈ incident_labels, d ∣ x) → d = 1

/--
Both Solution 1 and Solution 2 rely on assigning consecutive integers
`n` and `n + 1` to adjacent edges around a vertex. This theorem fully
proves that this algorithmic step is sufficient to guarantee the GCD
condition for that vertex, regardless of what other edges are attached.
-/
theorem valid_of_consecutive_labels (incident_labels : List ℕ) (n : ℕ)
    (hn : n ∈ incident_labels) (hsucc : n + 1 ∈ incident_labels) :
    ValidVertexLabeling incident_labels := by
  -- Let d be any common divisor of all incident labels
  intro d hd
  
  -- Since d divides all incident labels, it must divide n and n + 1
  have h_n : d ∣ n := hd n hn
  have h_succ : d ∣ n + 1 := hd (n + 1) hsucc
  
  -- In Lean 4, Nat.dvd_sub takes exactly two divisibility proofs.
  -- It divides the difference unconditionally.
  have h_diff : d ∣ (n + 1) - n := Nat.dvd_sub h_succ h_n
  
  -- The difference is 1
  have h_one : (n + 1) - n = 1 := by omega
  
  -- Therefore, d divides 1, which means d = 1
  rw [h_one] at h_diff
  exact Nat.eq_one_of_dvd_one h_diff

end IMO1991P4
