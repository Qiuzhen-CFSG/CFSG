module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerRigidity.TwistedCertificate.Words
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerRigidity.TwistedCertificate.Numerics

/-!
# Excluding an ambient matrix realization of the remaining local twist

The concrete polynomial R in the two certified centralizer generators has
R D = 1 + a. Replacing X by aX leaves the first row of the resulting polynomial
zero. An intertwining unit would therefore kill the nonzero first row of 1+a.

All word products, sums and the right factor are checked in the Lean kernel.
This excludes a matrix realization of one particular central twist; it does
not assert that every abstract automorphism of the local centralizer is inner.
The matrices and ATLAS provenance are those of `Janko4/Model/Data.lean`.
-/

public section
namespace Janko4.OuterReduction.FixedGenerator.NormalizerRigidity.TwistedCertificate
open NormalizerSquares NormalizerSquares.TwoCoreCentralizerData

/-- The residual X ↦ aX, Y ↦ Y action has no invertible matrix intertwiner
commuting with a in the actual 112-dimensional binary representation. -/
theorem no_twisted_unit (u : BinaryMatrixˣ)
    (ha : u * matrixUnitA = matrixUnitA * u)
    (hx : u * (localX : BinaryMatrixˣ) = matrixUnitA * (localX : BinaryMatrixˣ) * u)
    (hy : u * (localY : BinaryMatrixˣ) = (localY : BinaryMatrixˣ) * u) : False := by
  have hA : (u : BinaryMatrix) * matrixA = matrixA * (u : BinaryMatrix) :=
    @congrArg BinaryMatrixˣ BinaryMatrix (u * matrixUnitA) (matrixUnitA * u) Units.val ha
  have hX : (u : BinaryMatrix) * m001 = (matrixA * m001) * (u : BinaryMatrix) := by
    rw [← x_matrix]
    exact @congrArg BinaryMatrixˣ BinaryMatrix
      (u * (localX : BinaryMatrixˣ)) (matrixUnitA * (localX : BinaryMatrixˣ) * u) Units.val hx
  have hY : (u : BinaryMatrix) * m002 = m002 * (u : BinaryMatrix) := by
    rw [← y_matrix]
    exact @congrArg BinaryMatrixˣ BinaryMatrix
      (u * (localY : BinaryMatrixˣ)) ((localY : BinaryMatrixˣ) * u) Units.val hy
  apply no_unit_of_annihilator u hA rMatrix tMatrix dMatrix
  · rw [← original_sum, ← even_sum, ← odd_sum, mul_add,
      even_intertwines _ hX hY, odd_intertwines _ hX hY,
      even_sum, odd_sum, ← add_mul]
    rw [← a_matrix, product079, twisted_sum]
  · exact product078.trans target_sum.symm
  · exact twisted_zero_row
  · exact target_nonzero_row

end Janko4.OuterReduction.FixedGenerator.NormalizerRigidity.TwistedCertificate
