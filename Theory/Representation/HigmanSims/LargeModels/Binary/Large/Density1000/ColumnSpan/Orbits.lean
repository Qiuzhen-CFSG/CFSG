module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.ColumnSpan.Orbits.Trees
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.ColumnSpan.Orbits.TransposeA
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.ColumnSpan.Orbits.TransposeB
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.ColumnSpan.Orbits.Steps

/-!
# The degree-1000 candidate columns are the literal word orbit

The complete transpose certificates identify the packed transposes with the
literal published A and B generators. The 999 checked word transitions then
feed well-founded induction on the source column words, starting at the source
image and prepending each new letter. This identifies all 1000 candidate
columns with the actual left matrix action.

The identification has no numerical, spanning or representation hypothesis.
The independent packed-column spanning certificate remains the input needed
by `columnOrbit_span_of_realizations` to conclude column-orbit spanning.

Source: R. A. Wilson et al., ATLAS HSG1-f2r1000B0 and
`Binary/source/density1000.json`; see `Orbits/source/README.md`.
-/

public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000

/-- Every candidate column is the image under its literal published source word. -/
theorem columnOrbit_eq (i : Fin 1000) :
    columnOrbit i = RowArithmetic.vector 1000 Data.columnRows[i.val]! :=
  ColumnSpan.orbits_of_steps ColumnSpan.aTransposeTree ColumnSpan.bTransposeTree
    ColumnSpan.columnTree ColumnSpan.wordTree ColumnSpan.aTransposeTree_valid
    ColumnSpan.bTransposeTree_valid ColumnSpan.columnTree_valid ColumnSpan.wordTree_valid
    ColumnSpan.columnTree_rows ColumnSpan.wordTree_rows ColumnSpan.aTransposeTree_length
    ColumnSpan.bTransposeTree_length ColumnSpan.Orbits.aTranspose_matrix
    ColumnSpan.Orbits.bTransposeTree_matrix ColumnSpan.Orbits.stepsChecks i

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000
