module

public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.RowData

/-!
# Contract for a shared packed row

The two multiplication equalities and twelve-bit successor bounds are proved
for every row by the checked batches. The bounds justify the slot encoding
used by the native-code checks. Numerical attribution is in `Table.RowData`.
-/

public section
namespace Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table

@[expose] def RowGood (n : ℕ) : Prop :=
  row (rowValue n) generatorA = rowValue (stepA n) ∧
  row (rowValue n) generatorB = rowValue (stepB n) ∧
  stepA n < 4096 ∧ stepB n < 4096

end Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table
