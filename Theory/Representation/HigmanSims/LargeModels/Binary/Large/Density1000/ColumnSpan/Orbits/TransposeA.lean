module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.ColumnSpan.Orbits.TransposeA00
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.ColumnSpan.Orbits.TransposeA01
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.ColumnSpan.Orbits.TransposeA02
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.ColumnSpan.Orbits.TransposeA03
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.ColumnSpan.Orbits.TransposeA04
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.ColumnSpan.Orbits.TransposeA05
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.ColumnSpan.Orbits.TransposeA06
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.ColumnSpan.Orbits.TransposeA07

/-!
# The literal degree-1000 A transpose

The eight disjoint intervals certify every column comparison with the original
published A table. Balanced interval concatenation gives the complete check;
`transpose_of_checks` then identifies the candidate matrix with the transpose
of the literal generator. No numerical or representation hypothesis remains.

Source: R. A. Wilson et al., ATLAS HSG1-f2r1000B0. See
`Binary/source/README.md` and `Orbits/source/README.md` for attribution and
source rights. The Lean certificate code follows the repository's Apache-2.0
license.
-/

public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.ColumnSpan.Orbits

/-- All 1000 comparisons against the original published A generator. -/
theorem transposeAChecks :
    ColumnSpan.On (fun i =>
      ColumnSpan.aTransposeTree.columnMatch (2 ^ i) (ColumnSpan.aTree.get i) = true)
      0 1000 :=
  ((transposeA00.append transposeA01).append (transposeA02.append transposeA03)).append
    ((transposeA04.append transposeA05).append (transposeA06.append transposeA07))

/-- The A-transposition premise of the literal column-orbit induction. -/
theorem aTranspose_matrix :
    RowArithmetic.matrix 1000 1000 ColumnSpan.aTransposeTree.rows =
      (Density1000.generator false).transpose :=
  ColumnSpan.transpose_of_checks aTransposeTree aTree D1000.aRows 1000
    aTransposeTree_valid aTree_valid aTree_rows aTransposeTree_length transposeAChecks

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.ColumnSpan.Orbits
