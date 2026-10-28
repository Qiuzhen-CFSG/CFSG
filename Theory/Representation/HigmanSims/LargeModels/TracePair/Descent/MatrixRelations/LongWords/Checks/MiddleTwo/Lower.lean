module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.MiddleTwo.Lower.Gate26
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.MiddleTwo.Lower.Gate27
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.MiddleTwo.Lower.Gate28
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.MiddleTwo.Lower.Gate29

/-!
# The lower four middle products of the HS long-word circuit

All rows of the four literal products (16,17,28), (8,5,29), (3,14,30), and
(8,7,31) are checked by the Lean kernel. This establishes gates 26--29 without
premises or earlier word interpretations. The upper four middle gates remain
with the middle-batch assembly owner. See `Lower/source/README.md`.
-/

public section
namespace Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.MiddleTwo

/-- The four complete literal products forming the lower half of the middle batch. -/
theorem lower_products (i : Fin 46) (hlo : 26 ≤ i.val) (hhi : i.val < 30) :
    ProductCheck i := by
  have hi : i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 := by omega
  rcases hi with rfl | rfl | rfl | rfl
  · exact Lower.product_26
  · exact Lower.product_27
  · exact Lower.product_28
  · exact Lower.product_29

end Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.MiddleTwo
