module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.MiddleTwo.Upper
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords

/-!
# Application of the upper middle products to the six literal HS words

The four upper middle gates are discharged by numerical certificates. The
lower middle half and the other three batches remain explicit for their
assembly owners. The application uses the unchanged ordered circuit and the
literal packed ATLAS generators.
-/

public section
namespace Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.MiddleTwo
open Certificates

/-- Discharge the upper middle gates in the actual six-relator consumer. -/
theorem relations_of_upper_products
    (hlower : ∀ i : Fin 46, 26 ≤ i.val → i.val < 30 → ProductCheck i)
    (hshared : ∀ i : Fin 46, i.val < 17 → ProductCheck i)
    (hfirst : ∀ i : Fin 46, 17 ≤ i.val → i.val < 26 → ProductCheck i)
    (hlast : ∀ i : Fin 46, 34 ≤ i.val → ProductCheck i) :
    ∀ i : Fin 13, 7 ≤ i.val → positiveRelation
      (Packed.eval 896 generatorRowsA) (Packed.eval 896 generatorRowsB) i = 1 := by
  apply relations_of_batches hshared hfirst ?_ hlast
  intro i hlo hhi
  by_cases h : i.val < 30
  · exact hlower i hlo h
  · exact upper_products i (by omega) hhi

end Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.MiddleTwo
