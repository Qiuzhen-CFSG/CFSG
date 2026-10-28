module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.SpanningInput
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Packed

/-!
# Literal-action contracts for the proposed cyclic orbits

Choice `false` means a and choice `true` means b. Rows multiply on the right;
columns use ordinary left matrix action. In particular, a packed computation
of the column recurrence must use transposed tables and prove their comparison
with the literal matrices. Neither recurrence is asserted by these definitions.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity

/-- The proposed row orbit really follows the two literal right actions. -/
def RowOrbitRecurrences : Prop :=
  ∀ i : Fin 1408, 0 < i.val →
    vectorOfBits rowOrbitRows[i.val]! =
      if rowOrbitChoices[i.val]! then
        Matrix.vecMul (vectorOfBits rowOrbitRows[rowOrbitParents[i.val]!]!) matrixB
      else
        Matrix.vecMul (vectorOfBits rowOrbitRows[rowOrbitParents[i.val]!]!) matrixA

/-- The proposed column orbit really follows the two literal left actions. -/
def ColumnOrbitRecurrences : Prop :=
  ∀ i : Fin 1408, 0 < i.val →
    vectorOfBits columnOrbitRows[i.val]! =
      if columnOrbitChoices[i.val]! then
        matrixB.mulVec (vectorOfBits columnOrbitRows[columnOrbitParents[i.val]!]!)
      else
        matrixA.mulVec (vectorOfBits columnOrbitRows[columnOrbitParents[i.val]!]!)

end Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity
