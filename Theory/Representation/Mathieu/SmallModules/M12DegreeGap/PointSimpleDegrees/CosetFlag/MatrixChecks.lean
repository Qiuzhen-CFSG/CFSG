module

public import Theory.Representation.Mathieu.SmallModules.M12DegreeGap.PointSimpleDegrees.CosetFlag.MatrixChecks.Arithmetic
public import Theory.Representation.Mathieu.SmallModules.M12DegreeGap.PointSimpleDegrees.CosetFlag.MatrixChecks.Decode

/-!
# Certified adapted matrices for the M₁₁ eleven-coset flag

The published inverse is a left inverse to the 720-column basis. Both forward
permutation matrices intertwine with the published adapted actions. Every
lower block vanishes at the 33 cuts, and every diagonal block is exactly the
specified canonical factor matrix, with the original row and column indexing.

The proof decodes kernel-checked XOR, shift and remainder identities. It uses
no group-identification, native action-table, or factor-simplicity hypothesis.
`MatrixChecks.Application` supplies these identities to the actual quotient
flag construction; only the independent native action-table certificate remains.

Source: James, J. Algebra 27 (1973), 57–111; witness conventions in
`PointSimpleDegrees/source/README.md`.
-/

public section
namespace Representation.MathieuSmall.M12DegreeGap.PointSimpleDegrees.CosetFlag

/-- All four matrix obligations, for the literal published witnesses. -/
theorem matrixIdentities : MatrixIdentities where
  inverse := MatrixChecks.inverse_of_columns MatrixChecks.all_columns
  action := MatrixChecks.action_of_columns MatrixChecks.all_columns
  upper := MatrixChecks.upper_of_blocks MatrixChecks.all_blocks
  diagonal := MatrixChecks.diagonal_of_blocks MatrixChecks.all_blocks

end Representation.MathieuSmall.M12DegreeGap.PointSimpleDegrees.CosetFlag
