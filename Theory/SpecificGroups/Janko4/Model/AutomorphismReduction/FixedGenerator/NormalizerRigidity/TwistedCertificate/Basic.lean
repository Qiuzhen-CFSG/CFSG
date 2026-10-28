module
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Max2Bridge

/-!
# Algebra of the remaining matrix twist

A central involution twist propagates through products by parity. If a
polynomial R has a right multiple 1+a while its twisted version T has zero
first row, an invertible intertwiner commuting with a would kill a nonzero row.
The numerical witnesses are supplied separately, in the actual ATLAS binary
representation from `Janko4/Model/Data.lean`.
-/

@[expose] public section
namespace Janko4.OuterReduction.FixedGenerator.NormalizerRigidity.TwistedCertificate
open Matrix

/-- Multiplication propagates a central involution twist. -/
theorem intertwines_mul (M A R S : BinaryMatrix) (p q : Bool)
    (hAA : A * A = 1) (hRA : R * A = A * R)
    (hR : M * R = (if p then A * R else R) * M)
    (hS : M * S = (if q then A * S else S) * M) :
    M * (R * S) = (if Bool.xor p q then A * (R * S) else R * S) * M := by
  have hARA : A * R * A = R := by
    rw [mul_assoc, hRA, ← mul_assoc, hAA, one_mul]
  rw [← mul_assoc, hR, mul_assoc, hS]
  cases p <;> cases q <;>
    simp only [Bool.xor_false, Bool.xor_true, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, if_false, if_true]
  all_goals simp only [← mul_assoc, hRA, hARA]

/-- A vanishing row in the twisted polynomial contradicts invertibility. -/
theorem no_unit_of_annihilator (u : BinaryMatrixˣ)
    (huA : (u : BinaryMatrix) * matrixA = matrixA * (u : BinaryMatrix))
    (R T D : BinaryMatrix)
    (hRT : (u : BinaryMatrix) * R = T * (u : BinaryMatrix))
    (hRD : R * D = 1 + matrixA) (hT : T 0 = 0)
    (hne : (1 + matrixA : BinaryMatrix) 0 ≠ 0) : False := by
  have hz : (((u : BinaryMatrix) * R) * D) 0 = 0 := by
    rw [hRT, mul_assoc, mul_apply_eq_vecMul, hT, zero_vecMul]
  have he : (u : BinaryMatrix) * (1 + matrixA) = (1 + matrixA) * (u : BinaryMatrix) := by
    rw [mul_add, add_mul, mul_one, one_mul, huA]
  rw [mul_assoc, hRD, he, mul_apply_eq_vecMul] at hz
  have hh := congrArg (fun v : Fin 112 → ZMod 2 => v ᵥ* (↑(u⁻¹) : BinaryMatrix)) hz
  rw [vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    vecMul_one, zero_vecMul] at hh
  exact hne hh

end Janko4.OuterReduction.FixedGenerator.NormalizerRigidity.TwistedCertificate
