module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.MiddleTwo.Lower
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords

/-!
# Applying the lower middle products to the six literal long words

Gates 26--29 are discharged by `lower_products`. The four upper middle gates
and the other three batches remain explicit, as required by their separate
assembly owners. The application preserves the original literal generators
and all six ordered relators, including R1--R3.
-/

public section
namespace Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.MiddleTwo
open Certificates

theorem relations_of_lower_products
    (hupper : ∀ i : Fin 46, 30 ≤ i.val → i.val < 34 → ProductCheck i)
    (hshared : ∀ i : Fin 46, i.val < 17 → ProductCheck i)
    (hfirst : ∀ i : Fin 46, 17 ≤ i.val → i.val < 26 → ProductCheck i)
    (hlast : ∀ i : Fin 46, 34 ≤ i.val → ProductCheck i) :
    ∀ i : Fin 13, 7 ≤ i.val → positiveRelation
      (Packed.eval 896 generatorRowsA) (Packed.eval 896 generatorRowsB) i = 1 := by
  apply relations_of_batches hshared hfirst _ hlast
  intro i hlo hhi
  by_cases h : i.val < 30
  · exact lower_products i hlo h
  · exact hupper i (by omega) hhi

end Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.MiddleTwo
