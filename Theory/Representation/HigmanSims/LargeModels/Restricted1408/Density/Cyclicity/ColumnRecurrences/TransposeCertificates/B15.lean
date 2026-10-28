module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.ColumnRecurrences.TransposeData
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.RowsB

/-!
# Literal transpose B, columns 480 through 511

The direct column scan checks these proposed transpose rows against the original
matrix, with column j packed in bit order given by `column_bit`. The check is
reduced by the kernel. See `../source/README.md` for source and conventions.
-/

public section
namespace Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.ColumnRecurrences

set_option maxRecDepth 4096 in
theorem transposeBBlock15_check :
    columnsCheck bRows.toList 480 transposeBBlock15 = true := by
  decide +kernel

end Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.ColumnRecurrences
