module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.FirstTwo.WordEight.Gate21
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.FirstTwo.WordEight.Gate22
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.FirstTwo.WordEight.Gate23
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.FirstTwo.WordEight.Gate24
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.FirstTwo.WordEight.Gate25

/-!
# The remaining fixed product gates for HS source WordEight

Each imported theorem certifies a full numerical matrix product. This branch
requires no interpretation of earlier candidates as words. The exact source
circuit and identity endpoints are documented in `LongWords/source/README.md`.
-/

public section
namespace Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.FirstTwo

/-- The complete independent numerical branch, without extra premises. -/
theorem word_eight_products :
    ∀ i : Fin 46, 21 ≤ i.val → i.val < 26 → ProductCheck i := by
  intro i hlo hhi
  have hi : i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25 := by omega
  rcases hi with rfl | rfl | rfl | rfl | rfl
  · exact WordEight.Gate21.product_check
  · exact WordEight.Gate22.product_check
  · exact WordEight.Gate23.product_check
  · exact WordEight.Gate24.product_check
  · exact WordEight.Gate25.product_check

end Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.FirstTwo
