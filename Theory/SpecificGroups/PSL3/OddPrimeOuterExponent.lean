module
public import Theory.SpecificGroups.PSL3.OuterSolvable.OddPrimeSquares
public import Theory.SpecificGroups.PSL3.OddInvolutionFixed.NormalForm

/-!
# Outer exponent of ternary linear groups over prime fields

The field contribution is trivial and every automorphism square is induced
by a general linear matrix. Scalar determinant correction makes its cube
inner. Thus the actual outer quotient has exponent dividing six.
Simplicity and nonsolvability are inherited from the caller.
Source: GLS3, Theorem 2.5.12; Aschbacher–Smith A.3.18, pp.51–53.
-/

public section
open Subgroup
open scoped MatrixGroups
noncomputable section
namespace Matrix.PSL3
variable {F : Type*} [Field F] [Finite F] [IsSimpleGroup PSL(3,F)]
/-- Every automorphism has sixth power inner over an odd prime field. -/
theorem odd_prime_sixth_power_inner (hns : ¬ Group.IsSolvable PSL(3,F)) {r : ℕ}
    (hr : r.Prime) (ho : Odd r) (hF : Nat.card F = r) (a : MulAut PSL(3,F)) :
    a ^ 6 ∈ MulAut.innerSubgroup PSL(3,F) := by
  obtain ⟨g, hg⟩ := OuterSolvable.OddPrimeSquares.square_mem_innerDiagonal hns hr ho hF a
  rw [show 6 = 2 * 3 from rfl, pow_mul, ← hg]
  exact OddInvolutionFixed.linearConj_cube_inner g
end Matrix.PSL3


namespace Matrix.PSL3
variable {F : Type*} [Field F] [Finite F] [IsSimpleGroup PSL(3,F)]
/-- The determinant also kills the outer action after twice the split-torus exponent. -/
theorem odd_prime_split_power_inner (hns : ¬ Group.IsSolvable PSL(3,F)) {r : ℕ}
    (hr : r.Prime) (ho : Odd r) (hF : Nat.card F = r) (a : MulAut PSL(3,F)) :
    a ^ (2 * (r - 1)) ∈ MulAut.innerSubgroup PSL(3,F) := by
  obtain ⟨g, hg⟩ := OuterSolvable.OddPrimeSquares.square_mem_innerDiagonal hns hr ho hF a
  rw [pow_mul, ← hg, ← map_pow]
  apply (QuotientGroup.eq_one_iff _).mp
  change OuterSolvable.linearOuterAction F (g ^ (r - 1)) = 1
  apply OuterSolvable.det_ker_le_linearOuterAction_ker F
  change GeneralLinearGroup.det (g ^ (r - 1)) = 1
  rw [map_pow, ← hF, ← Nat.card_units]
  exact pow_card_eq_one'
end Matrix.PSL3

