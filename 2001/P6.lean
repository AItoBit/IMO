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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace IMO2001P6

/-- Rearrangement of the hypothesis `K*M + L*N = (K+L-M+N)*(-K+L+M+N)`. -/
theorem sq_rearrange {K L M N : ℤ}
    (heq : K * M + L * N = (K + L - M + N) * (-K + L + M + N)) :
    K ^ 2 - K * M + M ^ 2 = L ^ 2 + L * N + N ^ 2 := by
  linear_combination heq

/-- The key factorization identity:
`(K*M + L*N) * (L^2 + L*N + N^2) = (K*L + M*N) * (K*N + L*M)`. -/
theorem key_identity {K L M N : ℤ}
    (heq : K * M + L * N = (K + L - M + N) * (-K + L + M + N)) :
    (K * M + L * N) * (L ^ 2 + L * N + N ^ 2) = (K * L + M * N) * (K * N + L * M) := by
  linear_combination (-(L * N)) * sq_rearrange heq

/-- **IMO 2001, Problem 6.** If `K > L > M > N` are positive integers with
`K*M + L*N = (K+L-M+N)*(-K+L+M+N)`, then `K*L + M*N` is not prime. -/
theorem not_prime_mul_add_mul {K L M N : ℤ}
    (hN : 0 < N) (hMN : N < M) (hLM : M < L) (hKL : L < K)
    (heq : K * M + L * N = (K + L - M + N) * (-K + L + M + N)) :
    ¬ Prime (K * L + M * N) := by
  intro hp
  -- ordering of the three quantities
  have hpos : 0 < K * N + L * M := by nlinarith
  have h1 : K * N + L * M < K * M + L * N := by nlinarith
  have h2 : K * M + L * N < K * L + M * N := by nlinarith
  -- divisibility coming from the key identity
  have hdvd : (K * M + L * N) ∣ (K * L + M * N) * (K * N + L * M) :=
    ⟨L ^ 2 + L * N + N ^ 2, (key_identity heq).symm⟩
  -- the prime `K*L + M*N` does not divide the smaller positive number `K*M + L*N`
  have hnd : ¬ (K * L + M * N) ∣ (K * M + L * N) := by
    intro h
    have := Int.le_of_dvd (by linarith) h
    linarith
  have hcop : IsCoprime (K * M + L * N) (K * L + M * N) :=
    (hp.coprime_iff_not_dvd.mpr hnd).symm
  have hdvd' : (K * M + L * N) ∣ (K * N + L * M) :=
    hcop.dvd_of_dvd_mul_left hdvd
  have := Int.le_of_dvd hpos hdvd'
  linarith

end IMO2001P6
