module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density518.Columns
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density518

/-!
# Application of the certified column orbit to density

This module discharges the literal column premise of the existing density
criterion. It sits above both `Columns` and the original conditional assembly,
so the parent density module can import `Columns` without an import cycle.
The independent rank-one and row-span premises remain with the parent task.
Source: ATLAS HSG1-f2r518B0; see `source/README.md`.
-/

public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density518
open Matrix

/-- Discharge the column premise in the actual density consumer. The remaining
rank-one and row premises belong to the parent density assembly. -/
theorem matrixAlgebraFull_of_rank_one_and_row_span
    (hprojector : vecMulVec u v ∈ Q)
    (hrows : Submodule.span (ZMod 2) (Set.range (fun i => vecMul v (rowActor i))) = ⊤) :
    MatrixAlgebraFull 2 :=
  matrixAlgebraFull_of_rank_one_and_spans hprojector column_span hrows


end Representation.HigmanSims.LargeModels.Binary.Large.Density518
