module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnOrbit.Edges.Data

/-!
# Representative full packed edge

This checks the published first two edges numerically using the imported raw-numeral
transpose candidate. The application to the original first generator still
requires the separately owned transpose identity. Reproduction and measurements
are documented in `source/README.md`.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnEdges

set_option maxRecDepth 8192 in
theorem first_product_zero :
    select firstTranspose ColumnData.columns[0]! = ColumnData.columns[1]! := by
  decide +kernel

/-- The seed calculation is the original first generator's action on the nucleus. -/
theorem first_mulVec_nucleus_of_transpose
    (hA : matrix 1792 firstTranspose = Data1792.first.transpose) :
    Data1792.first.mulVec nucleus = ColumnData.column (1 : Fin 1792) := by
  rw [← ColumnData.column_zero]
  exact mulVec_of_select 1792 Data1792.firstRows firstTranspose hA
    firstTranspose_length _ _ first_product_zero

set_option maxRecDepth 8192 in
theorem second_product_one :
    select secondTranspose ColumnData.columns[0]! = ColumnData.columns[2]! := by
  decide +kernel

/-- The second seed calculation is the original second generator's nucleus action. -/
theorem second_mulVec_nucleus_of_transpose
    (hB : matrix 1792 secondTranspose = Data1792.second.transpose) :
    Data1792.second.mulVec nucleus = ColumnData.column (2 : Fin 1792) := by
  rw [← ColumnData.column_zero]
  exact mulVec_of_select 1792 Data1792.secondRows secondTranspose hB
    secondTranspose_length _ _ second_product_one

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnEdges
