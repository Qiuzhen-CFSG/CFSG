module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnOrbit.Edges.FirstProducts.Data

/-!
# Complete connection to the published first-generator edges

Two sequential kernel checks identify every certificate input with its parent
column, and cover exactly the first-labelled entries of the original tree.
The output scan uses the original columns with only their initial entry removed.

Source, reproduction and measurements: `source/README.md`.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnEdges.FirstProducts

set_option maxRecDepth 8192 in
theorem inputs_checked : checkInputs 0 ColumnData.columns entries = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem outputs_checked :
    checkOutputs ColumnData.parents ColumnData.columns.tail entries = true := by
  decide +kernel

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnEdges.FirstProducts
