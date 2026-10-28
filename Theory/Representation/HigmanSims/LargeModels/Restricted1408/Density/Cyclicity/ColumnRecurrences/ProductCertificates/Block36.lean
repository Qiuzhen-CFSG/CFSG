module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.ColumnRecurrences.StepData
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.ColumnRecurrences.TransposeData

/-!
# Column-orbit products, block 36

Kernel reduction checks the 32 published products in this block against the
unchanged proposed transpose tables. The checker selects a for false and b for
true. See `../source/README.md` for the ATLAS provenance and action convention.
-/

public section
namespace Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.ColumnRecurrences

set_option maxRecDepth 4096 in
theorem stepBlock36_check :
    productsCheck transposeARows.toList transposeBRows.toList stepBlock36 = true := by
  decide +kernel

end Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.ColumnRecurrences
