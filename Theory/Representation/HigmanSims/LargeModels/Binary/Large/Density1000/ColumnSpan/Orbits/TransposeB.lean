module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.ColumnSpan.Orbits.TransposeB00
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.ColumnSpan.Orbits.TransposeB01
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.ColumnSpan.Orbits.TransposeB02
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.ColumnSpan.Orbits.TransposeB03
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.ColumnSpan.Orbits.TransposeB04
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.ColumnSpan.Orbits.TransposeB05
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.ColumnSpan.Orbits.TransposeB06
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.ColumnSpan.Orbits.TransposeB07

/-!
# Complete transpose certificate for the degree-1000 B generator

The eight checked intervals cover every row of the literal published B matrix.
Balanced interval concatenation supplies the complete bit comparison, and
`transpose_of_checks` identifies the candidate transpose with the transpose of
the actual generator used by the column-word action. No numerical premise remains.

Source: R. A. Wilson et al., ATLAS HSG1-f2r1000B0. The original tables,
attribution and rights statement are in `Binary/source/README.md`; the checked
evaluation method is described in `Orbits/source/README.md`.
-/

public section

namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.ColumnSpan.Orbits

/-- All 1000 B-transpose comparisons against the shared source table. -/
theorem transposeBChecks :
    ColumnSpan.On (fun i =>
      ColumnSpan.bTransposeTree.columnMatch (2 ^ i) (ColumnSpan.bTree.get i) = true)
      0 1000 :=
  ((transposeB00.append transposeB01).append (transposeB02.append transposeB03)).append
    ((transposeB04.append transposeB05).append (transposeB06.append transposeB07))

/-- The checked candidate is the transpose of the literal B generator. -/
theorem bTransposeTree_matrix :
    RowArithmetic.matrix 1000 1000 ColumnSpan.bTransposeTree.rows =
      (Density1000.generator true).transpose :=
  ColumnSpan.transpose_of_checks bTransposeTree bTree D1000.bRows 1000
    bTransposeTree_valid bTree_valid bTree_rows bTransposeTree_length transposeBChecks

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.ColumnSpan.Orbits
