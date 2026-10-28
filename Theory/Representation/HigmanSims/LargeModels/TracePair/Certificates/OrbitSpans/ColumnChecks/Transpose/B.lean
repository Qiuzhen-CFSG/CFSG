module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.Trace.Transpose.Checks
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.OrbitSpans.ColumnChecks.TransposeData

/-!
# Reusing the certified transpose of the second HS generator

The independently published trace columns and the column-orbit transpose
candidate are literally the same packed data. Transport the completed trace
block certificate through this equality, preserving the actual matrix entries.
Source: `Trace/Transpose/source/README.md` and `ColumnChecks/source/README.md`.
-/

public section
namespace Representation.HigmanSims.LargeModels.TracePair.Certificates.OrbitSpans.ColumnChecks

theorem transposedRowsB_eq_columnsB : transposedRowsB = Trace.columnsB := by rfl

theorem transposedRowsB_eq :
    Packed.eval 896 transposedRowsB = (Packed.eval 896 generatorRowsB).transpose := by
  rw [transposedRowsB_eq_columnsB]
  exact Trace.Transpose.eval_eq_transpose _ _ Trace.Transpose.blocks_checked

end Representation.HigmanSims.LargeModels.TracePair.Certificates.OrbitSpans.ColumnChecks
