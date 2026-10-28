module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.NestedThree.MixedSquares
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.NestedThree

/-!
# Applying the checked mixed squares to the nested commutator

The two complete square certificates discharge exactly the mixed-square
premises of `nested_commutator_three_of_shared_products`. The shared gates
and the three subsequent numerical products remain explicit. Their producers
and the final unconditional relator belong to the parent assembly.

Source: relator 5 of the retained `Descent/source/HSG1-P1.M`, interpreted on
the unchanged HSG1-f4r896aB0 matrices as described in `TracePair/source/`.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations
open Certificates Commutators.NestedThree

/-- Apply both full mixed-square certificates, retaining the other producers. -/
theorem nested_commutator_three_of_mixed_squares
    (hshared : ∀ i : Fin 46, i.val < 17 → LongWords.ProductCheck i)
    (hC : Packed.eval 896 rowsAB4Sq * Packed.eval 896 rowsABSq = Packed.eval 896 rowsInner)
    (hC2 : Packed.eval 896 rowsInner * Packed.eval 896 rowsInner = Packed.eval 896 rowsInnerSq)
    (hC3 : Packed.eval 896 rowsInnerSq * Packed.eval 896 rowsInner = 1) :
    positiveRelation (Packed.eval 896 generatorRowsA) (Packed.eval 896 generatorRowsB) 5 = 1 :=
  nested_commutator_three_of_shared_products hshared a_b_fourth_square a_b_square hC hC2 hC3

end Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations
