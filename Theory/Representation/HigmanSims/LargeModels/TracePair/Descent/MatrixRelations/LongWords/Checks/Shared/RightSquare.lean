module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.Shared.RightSquare.Gate01
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.Shared.RightSquare.Gate06
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.Shared.RightSquare.Gate09
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.Shared.RightSquare.Gate15

/-!
# The four shared products with the square candidate on the right

These are the literal numerical gates 1, 6, 9 and 15. Coordinate images of
`rows02` and checked linear combinations certify every row of each product.
Repeated input rows reuse the same arithmetic, with both source and target
rows checked against the published data. No interpretation of a candidate
as a word is a premise. See `RightSquare/source/README.md` for reproduction
and `TracePair/source/README.md` for the ATLAS source and field convention.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords

/-- All four fixed products whose right operand is candidate 2. -/
theorem shared_right_square_products :
    ∀ i : Fin 46, (i = 1 ∨ i = 6 ∨ i = 9 ∨ i = 15) → ProductCheck i := by
  intro i hi
  rcases hi with rfl | rfl | rfl | rfl
  · exact Shared.RightSquare.Gate01.product_checked
  · exact Shared.RightSquare.Gate06.product_checked
  · exact Shared.RightSquare.Gate09.product_checked
  · exact Shared.RightSquare.Gate15.product_checked

end Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords
