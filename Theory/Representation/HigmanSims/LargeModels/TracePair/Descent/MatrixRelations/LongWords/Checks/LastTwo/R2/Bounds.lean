module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.LastTwo.R2.Arithmetic

/-!
# Width certificates for the five right operands in R2

Both planes of every row are smaller than 2^896. These checks justify copying
rows into separate 896-bit lanes without carries. They concern exactly the
fixed candidates 6, 16, 11, 37 and 38, in the original source order.
-/

public section
namespace Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.R2

/-- Both coefficient planes of candidate 6 fit in one lane. -/
theorem bounded_6 : Bounded 896 (rowsAt 6) :=
  bounded_of_check 896 (rowsAt 6) (by decide +kernel)

/-- Both coefficient planes of candidate 16 fit in one lane. -/
theorem bounded_16 : Bounded 896 (rowsAt 16) :=
  bounded_of_check 896 (rowsAt 16) (by decide +kernel)

/-- Both coefficient planes of candidate 11 fit in one lane. -/
theorem bounded_11 : Bounded 896 (rowsAt 11) :=
  bounded_of_check 896 (rowsAt 11) (by decide +kernel)

/-- Both coefficient planes of candidate 37 fit in one lane. -/
theorem bounded_37 : Bounded 896 (rowsAt 37) :=
  bounded_of_check 896 (rowsAt 37) (by decide +kernel)

/-- Both coefficient planes of candidate 38 fit in one lane. -/
theorem bounded_38 : Bounded 896 (rowsAt 38) :=
  bounded_of_check 896 (rowsAt 38) (by decide +kernel)

end Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.R2
