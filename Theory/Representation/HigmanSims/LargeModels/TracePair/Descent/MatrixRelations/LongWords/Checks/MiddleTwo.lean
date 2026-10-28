module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.MiddleTwo.Tail
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.MiddleTwo.Lower
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.MiddleTwo.Upper

/-!
# Assembly of the middle eight HS product gates

The lower and upper four-gate certificates prove all eight literal matrix
products for source word 9 and R1. Splitting the interval at gate 30 assembles
them without extra hypotheses or earlier word interpretations. The original
conditional tail assembly remains available. Sources, arithmetic conventions,
and complete-check measurements are recorded in `MiddleTwo/source/README.md`.
-/

public section
namespace Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords
open Certificates

/-- All eight fixed products for source word 9 and R1, including the square
of candidate 18, with no remaining numerical premises. -/
theorem middle_products (i : Fin 46) (hlow : 26 ≤ i.val) (hhigh : i.val < 34) :
    ProductCheck i := by
  by_cases h : i.val < 30
  · exact MiddleTwo.lower_products i hlow h
  · exact MiddleTwo.upper_products i (by omega) hhigh

/-- Discharge the certified R1 tail while retaining every unchecked product. -/
theorem middle_products_of_remaining
    (hother : ∀ i : Fin 46, 26 ≤ i.val → i.val < 33 → ProductCheck i)
    (hhead : ∀ r : Fin 896, r.val < 880 →
      Packed.rowProduct (rows18.getD r.val (0,0)) rows18 =
        identityRows.getD r.val (0,0)) :
    ∀ i : Fin 46, 26 ≤ i.val → i.val < 34 → ProductCheck i := by
  intro i hlow hhigh
  by_cases h : i.val < 33
  · exact hother i hlow h
  have hi : i = 33 := by omega
  subst i
  exact MiddleTwo.product_33_of_head hhead

end Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords
