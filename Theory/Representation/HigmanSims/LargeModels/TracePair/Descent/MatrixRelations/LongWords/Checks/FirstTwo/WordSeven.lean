module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.FirstTwo.WordSeven.Gate17
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.FirstTwo.WordSeven.Gate18
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.FirstTwo.WordSeven.Gate19
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.FirstTwo.WordSeven.Gate20

/-!
# The remaining fixed product gates for HS source WordSeven

Each imported theorem certifies a full numerical matrix product. This branch
requires no interpretation of earlier candidates as words. The exact source
circuit and identity endpoints are documented in `LongWords/source/README.md`.
-/

public section
namespace Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.FirstTwo

/-- The complete independent numerical branch, without extra premises. -/
theorem word_seven_products :
    ∀ i : Fin 46, 17 ≤ i.val → i.val < 21 → ProductCheck i := by
  intro i hlo hhi
  have hi : i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 := by omega
  rcases hi with rfl | rfl | rfl | rfl
  · exact WordSeven.Gate17.product_check
  · exact WordSeven.Gate18.product_check
  · exact WordSeven.Gate19.product_check
  · exact WordSeven.Gate20.product_check

end Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.FirstTwo
