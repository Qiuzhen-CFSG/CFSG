module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density518.RankOne
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density518

/-!
# Application of the certified projector to degree-518 density

The unconditional `rank_one_mem` discharges exactly the projector premise.
The parent density assembly retains the independent column and row spans.
This separate consumer keeps `RankOne` importable by the parent assembly.
Source: ATLAS HSG1-f2r518B0; `RankOne/source/README.md`.
-/

public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density518
open Matrix

/-- Application to the literal density consumer; the parent owns both spans. -/
theorem matrixAlgebraFull_of_spans
    (hcolumns : Submodule.span (ZMod 2)
      (Set.range (fun i => (columnActor i).mulVec u)) = ⊤)
    (hrows : Submodule.span (ZMod 2)
      (Set.range (fun i => vecMul v (rowActor i))) = ⊤) : MatrixAlgebraFull 2 :=
  matrixAlgebraFull_of_rank_one_and_spans rank_one_mem hcolumns hrows


end Representation.HigmanSims.LargeModels.Binary.Large.Density518
