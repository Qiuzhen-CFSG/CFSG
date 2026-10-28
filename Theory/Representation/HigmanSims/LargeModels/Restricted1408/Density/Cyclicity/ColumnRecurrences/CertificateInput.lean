module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.ColumnRecurrences.StepData
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.ColumnRecurrences.TransposeData
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.RowsA
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.RowsB

/-!
# Independent arithmetic contracts for the column orbit

The first contract compares every proposed transpose row against the literal
matrix. The second checks all 1407 products using those proposed tables. Their
conjunction supplies the exact ordinary column recurrences via the proved
layout, parent-input and transpose bridges in `ColumnRecurrences.lean`.
These definitions assert neither contract. See `source/README.md`.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.ColumnRecurrences

def TransposeChecks : Prop :=
  columnsCheck aRows.toList 0 transposeARows.toList = true ∧
  columnsCheck bRows.toList 0 transposeBRows.toList = true

def ProductChecks : Prop :=
  productsCheck transposeARows.toList transposeBRows.toList steps = true

end Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.ColumnRecurrences
