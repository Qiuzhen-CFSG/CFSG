module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.ColumnRecurrences.StepData
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.ColumnRecurrences.TransposeData

/-!
# First bounded column-orbit product certificate

The first 32 positive orbit steps satisfy the packed row-product equations for
the proposed transpose tables. The literal matrix interpretation is proved
separately by `ColumnRecurrences.step_mulVec`. See `source/README.md`.
-/

public section
namespace Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.ColumnRecurrences

set_option maxRecDepth 4096 in
theorem stepBlock00_check :
    productsCheck transposeARows.toList transposeBRows.toList stepBlock00 = true := by
  decide +kernel

end Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.ColumnRecurrences
