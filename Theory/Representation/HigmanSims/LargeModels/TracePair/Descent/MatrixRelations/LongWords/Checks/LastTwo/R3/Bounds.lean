module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.LastTwo.R2.Arithmetic

/-!
# Width certificates for the seven right operands in R3

Both coefficient planes of every row fit in an 896-bit lane. These bounds
allow the generic simultaneous row checker from `R2.Arithmetic` to certify
R3 without using any R2 product. The candidates are the exact right operands
5, 9, 1, 3, 42, 44 and 46 in `LongWords/source/circuit.json`.
-/

public section
namespace Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.R3
open R2

/-- Both coefficient planes of candidate 5 fit in one lane. -/
theorem bounded_5 : Bounded 896 (rowsAt 5) :=
  bounded_of_check 896 (rowsAt 5) (by decide +kernel)

/-- Both coefficient planes of candidate 9 fit in one lane. -/
theorem bounded_9 : Bounded 896 (rowsAt 9) :=
  bounded_of_check 896 (rowsAt 9) (by decide +kernel)

/-- Both coefficient planes of candidate 1 fit in one lane. -/
theorem bounded_1 : Bounded 896 (rowsAt 1) :=
  bounded_of_check 896 (rowsAt 1) (by decide +kernel)

/-- Both coefficient planes of candidate 3 fit in one lane. -/
theorem bounded_3 : Bounded 896 (rowsAt 3) :=
  bounded_of_check 896 (rowsAt 3) (by decide +kernel)

/-- Both coefficient planes of candidate 42 fit in one lane. -/
theorem bounded_42 : Bounded 896 (rowsAt 42) :=
  bounded_of_check 896 (rowsAt 42) (by decide +kernel)

/-- Both coefficient planes of candidate 44 fit in one lane. -/
theorem bounded_44 : Bounded 896 (rowsAt 44) :=
  bounded_of_check 896 (rowsAt 44) (by decide +kernel)

/-- Both coefficient planes of candidate 46 fit in one lane. -/
theorem bounded_46 : Bounded 896 (rowsAt 46) :=
  bounded_of_check 896 (rowsAt 46) (by decide +kernel)

end Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.R3
