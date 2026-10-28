module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Fintype
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Recovering a projection inside a finite algebra

If an algebra element D annihilates an idempotent P on both sides and D + P is
invertible, then a positive power of D + P is one. Orthogonality gives
`(D + P)^m = D^m + P`, so P belongs to the algebra containing D.

For binary matrix certificates this replaces evaluating a long characteristic
polynomial by checking two kernels, a pairing, and an inverse. The concrete
application is the ATLAS degree-1242 pair, used for James, J. Algebra 27 (1973),
57–111. The finite-ring argument itself is independent of those data.
-/

public section
open Matrix

namespace Representation.MatrixDensity

/-- Orthogonal completion to a unit recovers an idempotent in a finite algebra. -/
theorem projector_mem_of_isUnit_add
    {k R : Type*} [CommRing k] [Ring R] [Algebra k R] [Finite R]
    (Q : Subalgebra k R) (D P : R) (hD : D ∈ Q)
    (hDP : D * P = 0) (hPD : P * D = 0) (hP : P * P = P)
    (hunit : IsUnit (D + P)) : P ∈ Q := by
  have hp (m : ℕ) : (D + P) ^ (m + 1) = D ^ (m + 1) + P := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ (D + P), ih, add_mul, mul_add, mul_add, hPD, hP]
      have hz : D ^ (m + 1) * P = 0 := by
        rw [pow_succ, mul_assoc, hDP, mul_zero]
      rw [hz, add_zero, zero_add, ← pow_succ]
  obtain ⟨m, hm, he⟩ := hunit.isOfFinOrder.exists_pow_eq_one
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  have hsum : D ^ (m + 1) + P = 1 := (hp m).symm.trans he
  have hproj : P = 1 - D ^ (m + 1) := by
    apply eq_sub_iff_add_eq.mpr
    rwa [add_comm]
  rw [hproj]
  exact Q.sub_mem Q.one_mem (Q.pow_mem hD _)

/-- A paired left and right kernel supplies the orthogonal rank-one idempotent. -/
theorem rankOne_mem_of_isUnit_add
    {k n : Type*} [Field k] [Finite k] [Fintype n] [DecidableEq n]
    (Q : Subalgebra k (Matrix n n k)) (D : Matrix n n k) (u v : n → k)
    (hD : D ∈ Q) (hcol : D.mulVec u = 0) (hrow : vecMul v D = 0)
    (hpair : dotProduct v u = 1) (hunit : IsUnit (D + vecMulVec u v)) :
    vecMulVec u v ∈ Q := by
  apply projector_mem_of_isUnit_add Q D _ hD
  · rw [mul_vecMulVec, hcol, zero_vecMulVec]
  · rw [vecMulVec_mul, hrow, vecMulVec_zero]
  · rw [vecMulVec_mul_vecMulVec, hpair, one_smul]
  · exact hunit

end Representation.MatrixDensity
