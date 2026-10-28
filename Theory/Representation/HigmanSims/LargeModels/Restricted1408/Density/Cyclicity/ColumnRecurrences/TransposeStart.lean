module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.ColumnRecurrences.TransposeData
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.RowsA

/-!
# First bounded transpose certificate

The first 32 proposed rows are computed from the literal aRows. This is the
representative kernel-checked block for the full transpose-certificate producer.
It does not assert the remaining columns. See `source/README.md`.
-/

public section
namespace Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.ColumnRecurrences

set_option maxRecDepth 4096 in
theorem transposeABlock00_check : columnsCheck aRows.toList 0 transposeABlock00 = true := by
  decide +kernel

end Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.ColumnRecurrences
